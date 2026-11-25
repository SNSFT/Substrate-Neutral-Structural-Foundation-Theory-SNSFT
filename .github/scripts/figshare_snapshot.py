#!/usr/bin/env python3
"""Daily figshare usage snapshot for the Repository Acquisition Panel.

Reads figshare's public APIs for one author and merges the result into figshare.json:
  - the author's published items (id, title, DOI, published date)
  - per item, per day: views and downloads (stats.figshare.com timeline)
  - per day: views and downloads by country and city, summed over the items (breakdown)
  - the author's running totals of views, downloads and shares
No token is needed for public items. Nothing recorded is ever removed: an item stays listed
once seen, and a stored day count is replaced only by a read that is at least as large.
Standard library only.

Environment:
  FIGSHARE_AUTHOR   figshare author id (the number in figshare.com/authors/<name>/<id>)
  FIGSHARE_ORCID    optional ORCID iD, used to find the author's items
  FIGSHARE_ITEMS    optional comma-separated item ids to track in addition to those found
  OUT               optional output path (default figshare.json)
"""
import json, os, sys, time, datetime, urllib.request, urllib.error

API = "https://api.figshare.com/v2"
STATS = "https://stats.figshare.com"
AUTHOR = os.environ.get("FIGSHARE_AUTHOR", "").strip()
ORCID = os.environ.get("FIGSHARE_ORCID", "").strip()
EXTRA = [x.strip() for x in os.environ.get("FIGSHARE_ITEMS", "").split(",") if x.strip()]
OUT = os.environ.get("OUT", "figshare.json")


def req(url, body=None):
    r = urllib.request.Request(url, data=json.dumps(body).encode() if body is not None else None, headers={
        "Accept": "application/json", "Content-Type": "application/json",
        "User-Agent": "tl-acquisition-snapshot"})
    for attempt in range(3):
        try:
            with urllib.request.urlopen(r, timeout=60) as resp:
                time.sleep(0.25)
                return json.load(resp)
        except urllib.error.HTTPError as e:
            if e.code in (429, 502, 503) and attempt < 2:
                time.sleep(5 * (attempt + 1))
                continue
            print(f"  skipped {url}: HTTP {e.code}")
            return None
        except Exception as e:
            print(f"  skipped {url}: {e}")
            return None


def find_items():
    """Items whose author list carries the author id, found by ORCID and by author search."""
    found = {}
    queries = ([f":orcid: {ORCID}"] if ORCID else []) + [f":author_id: {AUTHOR}"]
    for q in queries:
        page = 1
        while True:
            res = req(f"{API}/articles/search", {"search_for": q, "page": page, "page_size": 100})
            if not res:
                break
            for a in res:
                found[str(a["id"])] = a
            if len(res) < 100:
                break
            page += 1
    return found


def item_details(item_id):
    a = req(f"{API}/articles/{item_id}")
    if not a:
        return None
    if AUTHOR and not any(str(x.get("id")) == AUTHOR for x in a.get("authors", [])):
        return None
    return {"title": a.get("title", ""), "doi": a.get("doi", ""), "url": a.get("url_public_html", ""),
            "published": (a.get("published_date") or "")[:10], "type": a.get("defined_type_name", "")}


def keep_max(store, key, value):
    if value > store.get(key, 0):
        store[key] = value


def main():
    if not AUTHOR:
        print("FIGSHARE_AUTHOR not set; figshare snapshot skipped.")
        return
    try:
        with open(OUT, encoding="utf-8") as f:
            data = json.load(f)
    except FileNotFoundError:
        data = {}
    data.update({"schema": 1, "source": "figshare", "author_id": AUTHOR})
    for k in ("items", "days", "geo", "totals"):
        data.setdefault(k, {})

    ids = set(data["items"]) | set(find_items()) | set(EXTRA)
    for i in sorted(ids):
        d = item_details(i)
        if d:
            data["items"][i] = {**data["items"].get(i, {}), **d}
    today = datetime.datetime.now(datetime.timezone.utc).date().isoformat()

    for i, it in data["items"].items():
        start = it.get("published") or "2026-01-01"
        for counter, key in (("views", "v"), ("downloads", "d")):
            res = req(f"{STATS}/timeline/day/{counter}/article/{i}?start_date={start}&end_date={today}")
            for day, n in ((res or {}).get("timeline") or {}).items():
                day = day[:10]
                keep_max(data["days"].setdefault(day, {}).setdefault(i, {}), key, int(n or 0))
            res = req(f"{STATS}/breakdown/day/{counter}/article/{i}?start_date={start}&end_date={today}")
            for day, countries in ((res or {}).get("breakdown") or {}).items():
                day = day[:10]
                for country, cities in (countries or {}).items():
                    if isinstance(cities, dict):
                        for city, n in cities.items():
                            place = f"{country}|{city or 'Unknown'}"
                            cell = data["geo"].setdefault(day, {}).setdefault(place, {})
                            cell.setdefault("_items", {})
                            keep_max(cell["_items"], f"{i}:{key}", int(n or 0))
                    else:
                        cell = data["geo"].setdefault(day, {}).setdefault(f"{country}|Unknown", {})
                        cell.setdefault("_items", {})
                        keep_max(cell["_items"], f"{i}:{key}", int(cities or 0))

    # geo cells: per-item maxima kept in _items, summed into v and d
    for day, places in data["geo"].items():
        for place, cell in places.items():
            items = cell.get("_items", {})
            cell["v"] = sum(n for k, n in items.items() if k.endswith(":v"))
            cell["d"] = sum(n for k, n in items.items() if k.endswith(":d"))

    tot = {c: ((req(f"{STATS}/total/{c}/author/{AUTHOR}") or {}).get("totals")) for c in ("views", "downloads", "shares")}
    if any(v is not None for v in tot.values()):
        prev = data["totals"].get(today, {})
        data["totals"][today] = {c: max(prev.get(c, 0), v or 0) for c, v in tot.items()}

    data["days"] = dict(sorted(data["days"].items()))
    data["geo"] = dict(sorted(data["geo"].items()))
    data["totals"] = dict(sorted(data["totals"].items()))
    data["updated"] = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, separators=(",", ":"))
    v = sum(x.get("v", 0) for day in data["days"].values() for x in day.values())
    dl = sum(x.get("d", 0) for day in data["days"].values() for x in day.values())
    print(f"figshare author {AUTHOR}: {len(data['items'])} items, {len(data['days'])} days, {v} views, {dl} downloads; totals {data['totals'].get(today)}")


if __name__ == "__main__":
    main()
