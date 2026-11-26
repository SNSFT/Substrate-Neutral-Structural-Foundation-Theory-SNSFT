#!/usr/bin/env python3
"""RAP registry scanner: scans every ORCID iD and figshare author on the RAP scan list.

The scan list lives in the Supabase table rap_registry (kind, value), which anyone can add to
from uuia.app/rap. Each entry is scanned on its own; a source that fails for one entry is skipped
for that entry and run, and every other entry and source carries on. Results are written under
registry/<kind>/<value>/ on the rap-registry branch, and registry/index.json lists every profile.

Sources, all public, no account needed from the person being scanned:
  orcid     pub.orcid.org/v3.0 (anonymous public API): name and works, with dates and DOIs
  openalex  api.openalex.org: citation total and works count, read daily; the record keeps
            each day's total, so the day-over-day rise is the citations added that day
  figshare  figshare_snapshot.py: views and downloads per item per day, by country and city

Nothing recorded is ever removed: works stay listed once seen, and a stored day total is
replaced only by a read that is at least as large. Standard library only.

Environment:
  SUPABASE_URL, SUPABASE_PUBLISHABLE_KEY   read the scan list (public read under row-level security)
  OPENALEX_API_KEY                  free key from openalex.org/settings/api
  RAP_MODE                          "new" scans only entries without a profile yet; "all" scans every entry
  FIGSHARE_SCRIPT                   path to figshare_snapshot.py
"""
import json, os, re, subprocess, sys, time, datetime, urllib.request, urllib.error, urllib.parse

SB_URL = os.environ.get("SUPABASE_URL", "").rstrip("/")
SB_KEY = os.environ.get("SUPABASE_PUBLISHABLE_KEY", "")
OA_KEY = os.environ.get("OPENALEX_API_KEY", "")
MODE = os.environ.get("RAP_MODE", "new")
FIG = os.environ.get("FIGSHARE_SCRIPT", "figshare_snapshot.py")
ROOT = "registry"
TODAY = datetime.datetime.now(datetime.timezone.utc).date().isoformat()
NOW = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def get(url, headers=None):
    h = {"Accept": "application/json", "User-Agent": "rap-registry-scan (uuia.app/rap; mailto:rvtrent@uuia.app)"}
    h.update(headers or {})
    for attempt in range(3):
        try:
            with urllib.request.urlopen(urllib.request.Request(url, headers=h), timeout=60) as r:
                time.sleep(0.2)
                return json.load(r)
        except urllib.error.HTTPError as e:
            if e.code in (429, 500, 502, 503) and attempt < 2:
                time.sleep(5 * (attempt + 1))
                continue
            print(f"  skipped {url.split('?')[0]}: HTTP {e.code}")
            return None
        except Exception as e:
            print(f"  skipped {url.split('?')[0]}: {e}")
            return None


def orcid_ok(v):
    """ISO 7064 11,2 check digit, as ORCID issues it."""
    if not re.fullmatch(r"\d{4}-\d{4}-\d{4}-\d{3}[\dX]", v):
        return False
    d = v.replace("-", "")
    total = 0
    for c in d[:-1]:
        total = (total + int(c)) * 2
    r = (12 - total % 11) % 11
    return d[-1] == ("X" if r == 10 else str(r))


def load(path, default):
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return default


def save(path, data):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


def scan_orcid(oid, folder):
    rec = load(f"{folder}/orcid.json", {})
    rec.update({"schema": 1, "source": "orcid", "orcid": oid})
    rec.setdefault("works", {})
    person = get(f"https://pub.orcid.org/v3.0/{oid}/person")
    if person:
        n = (person.get("name") or {})
        given = ((n.get("given-names") or {}).get("value") or "").strip()
        family = ((n.get("family-name") or {}).get("value") or "").strip()
        credit = ((n.get("credit-name") or {}).get("value") or "").strip()
        rec["name"] = credit or " ".join(x for x in (given, family) if x) or rec.get("name", "")
    works = get(f"https://pub.orcid.org/v3.0/{oid}/works")
    for g in (works or {}).get("group", []):
        for s in g.get("work-summary", [])[:1]:
            pc = str(s.get("put-code"))
            pd = s.get("publication-date") or {}
            y = ((pd.get("year") or {}).get("value") or "")
            m = ((pd.get("month") or {}).get("value") or "")
            d = ((pd.get("day") or {}).get("value") or "")
            created = (s.get("created-date") or {}).get("value")
            created = datetime.datetime.fromtimestamp(created / 1000, datetime.timezone.utc).date().isoformat() if created else ""
            doi = ""
            for x in ((s.get("external-ids") or {}).get("external-id") or []):
                if (x.get("external-id-type") or "").lower() == "doi":
                    doi = (x.get("external-id-value") or "").lower()
                    break
            w = rec["works"].setdefault(pc, {})
            w.update({"title": (((s.get("title") or {}).get("title") or {}).get("value") or ""),
                      "type": s.get("type") or "", "doi": doi,
                      "published": "-".join(x for x in (y, m.zfill(2) if m else "", d.zfill(2) if d else "") if x),
                      "added": created, "last_seen": TODAY})
            w.setdefault("first_seen", TODAY)
    rec["updated"] = NOW
    save(f"{folder}/orcid.json", rec)
    return rec


def scan_openalex(oid, folder):
    if not OA_KEY:
        print("  OPENALEX_API_KEY not set; OpenAlex skipped.")
        return None
    rec = load(f"{folder}/openalex.json", {})
    rec.update({"schema": 1, "source": "openalex", "orcid": oid})
    rec.setdefault("days", {})
    a = get(f"https://api.openalex.org/authors/orcid:{oid}?api_key={OA_KEY}")
    if not a:
        return rec if rec.get("days") else None
    rec["author"] = {"id": a.get("id", ""), "name": a.get("display_name", "")}
    rec["counts_by_year"] = a.get("counts_by_year", [])
    day = rec["days"].setdefault(TODAY, {})
    for k_src, k in (("cited_by_count", "cited"), ("works_count", "works")):
        v = int(a.get(k_src) or 0)
        if v > day.get(k, 0):
            day[k] = v
    rec.setdefault("opening", {"day": min(rec["days"]), **rec["days"][min(rec["days"])]})
    rec["updated"] = NOW
    save(f"{folder}/openalex.json", rec)
    return rec


def scan_figshare(author, oid, folder):
    if not os.path.exists(FIG):
        print("  figshare_snapshot.py not found; figshare skipped.")
        return None
    env = dict(os.environ, FIGSHARE_AUTHOR=author, FIGSHARE_ORCID=oid or "", FIGSHARE_ITEMS="",
               OUT=f"{folder}/figshare.json")
    os.makedirs(folder, exist_ok=True)
    subprocess.run([sys.executable, FIG], env=env, check=False)
    return load(f"{folder}/figshare.json", None)


def main():
    if not (SB_URL and SB_KEY):
        sys.exit("SUPABASE_URL and SUPABASE_PUBLISHABLE_KEY are required.")
    rows = get(f"{SB_URL}/rest/v1/rap_registry?select=kind,value,created_at&order=created_at.asc",
               {"apikey": SB_KEY}) or []
    index = load(f"{ROOT}/index.json", {"profiles": {}})
    index.setdefault("profiles", {})
    for r in rows:
        kind, value = r.get("kind"), (r.get("value") or "").strip().upper()
        key = f"{kind}:{value}"
        if MODE == "new" and key in index["profiles"]:
            continue
        folder = f"{ROOT}/{kind}/{value}"
        p = index["profiles"].get(key, {"kind": kind, "value": value, "registered": (r.get("created_at") or "")[:10],
                                         "first_scanned": TODAY})
        print(f"scan {key}")
        files = set(p.get("files", []))
        if kind == "orcid":
            if not orcid_ok(value):
                print("  not a valid ORCID iD; skipped.")
                continue
            o = scan_orcid(value, folder)
            if o:
                files.add("orcid.json")
                p["name"] = o.get("name", "") or p.get("name", "")
                p["works"] = len(o.get("works", {}))
            a = scan_openalex(value, folder)
            if a and a.get("days"):
                files.add("openalex.json")
                last = a["days"][max(a["days"])]
                p["citations"] = last.get("cited", 0)
        elif kind == "figshare":
            if not re.fullmatch(r"\d{1,12}", value):
                continue
            f = scan_figshare(value, "", folder)
            if f and f.get("items"):
                files.add("figshare.json")
                p["items"] = len(f["items"])
                tot = (f.get("totals") or {})
                if tot:
                    t = tot[max(tot)]
                    p["views"], p["downloads"] = t.get("views", 0), t.get("downloads", 0)
        else:
            continue
        p["files"] = sorted(files)
        p["last_scanned"] = NOW
        index["profiles"][key] = p
    index["updated"] = NOW
    save(f"{ROOT}/index.json", index)
    print(f"{len(index['profiles'])} profiles on record.")


if __name__ == "__main__":
    main()
