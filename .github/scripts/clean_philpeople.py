#!/usr/bin/env python3
"""Clean a PhilPeople Web Analytics export (copied page text) into philpeople.json and a CSV.

philpeople.json stores each origin, document and referrer once; rows point to them.

Each visit row: time as PhilPeople lists it, origin, page or document, referrer.
The export carries no year; the year is set from the export's end date (the 'To' field):
a row dated after that day belongs to the year before. Rows are stored with a count, and
merging a new export into an existing philpeople.json keeps the larger count for every
row key, so the record is never lowered and nothing is removed.
Usage: python3 clean_philpeople.py export.txt [existing philpeople.json] [out.json] [out.csv]
"""
import sys, re, json, csv, datetime, collections

MON = {m: i for i, m in enumerate("Jan Feb Mar Apr May Jun Jul Aug Sep Oct Nov Dec".split(), 1)}


def parse(text):
    lines = [l.rstrip("\r\n") for l in text.splitlines()]
    end = None
    for i, l in enumerate(lines):
        if l.strip() == "To" and i + 1 < len(lines) and re.match(r"^\d{4}-\d\d-\d\d$", lines[i + 1].strip()):
            end = datetime.date.fromisoformat(lines[i + 1].strip())
            break
    end = end or datetime.date.today()
    rows = collections.Counter()
    for l in lines:
        p = l.split("\t")
        if len(p) != 4 or p[0].strip() == "Date and Time":
            continue
        m = re.match(r"^(\d{1,2}) ([A-Z][a-z]{2}) (\d\d:\d\d)$", p[0].strip())
        if not m:
            continue
        day = datetime.date(end.year, MON[m.group(2)], int(m.group(1)))
        if day > end:
            day = day.replace(year=end.year - 1)
        ref = p[3].strip()
        rows[(day.isoformat(), m.group(3), p[1].strip(), p[2].strip(), "" if ref == "-" else ref)] += 1
    return rows, end


def doc_codes(rows):
    seen = collections.defaultdict(collections.Counter)
    for (d, t, o, doc, ref), n in rows.items():
        m = re.search(r"phil(?:archive|papers)\.org/rec/([A-Z0-9-]+)", ref)
        if m:
            seen[doc][m.group(1)] += n
    out = {}
    for doc, c in seen.items():
        code, k = c.most_common(1)[0]
        if k / sum(c.values()) >= 0.6:
            out[doc] = code
    return out


def pack(data, rows):
    """Store each origin, document and referrer once; a row is
    [date, time, origin index, document index, referrer index, count]."""
    tabs = {"origins": {}, "docs": {}, "refs": {}}
    def ix(tab, v):
        return tabs[tab].setdefault(v, len(tabs[tab]))
    data["rows"] = [[d, t, ix("origins", o), ix("docs", doc), ix("refs", ref), n]
                    for (d, t, o, doc, ref), n in sorted(rows.items(), reverse=True)]
    for tab, m in tabs.items():
        data[tab] = list(m)


def expand(data):
    for d, t, o, doc, ref, n in data["rows"]:
        yield (d, t, data["origins"][o], data["docs"][doc], data["refs"][ref]), n


def main():
    src = sys.argv[1]
    prev = sys.argv[2] if len(sys.argv) > 2 and sys.argv[2] != "-" else None
    out_json = sys.argv[3] if len(sys.argv) > 3 else "philpeople.json"
    out_csv = sys.argv[4] if len(sys.argv) > 4 else "philpeople.csv"
    rows, end = parse(open(src, encoding="utf-8", errors="replace").read())
    data = {"schema": 2, "source": "PhilPeople Web Analytics", "codes": {}, "imports": []}
    if prev:
        data = json.load(open(prev, encoding="utf-8"))
        for k, n in expand(data):
            rows[k] = max(rows.get(k, 0), n)
    data["codes"] = {**data.get("codes", {}), **doc_codes(rows)}
    pack(data, rows)
    days = sorted({k[0] for k in rows})
    data["imports"] = data.get("imports", []) + [{"export_end": end.isoformat(), "rows": sum(rows.values())}]
    data["first_day"], data["last_day"] = days[0], days[-1]
    json.dump(data, open(out_json, "w", encoding="utf-8"), ensure_ascii=False, separators=(",", ":"))
    with open(out_csv, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["date", "time", "origin", "document", "philarchive_code", "referrer", "count"])
        for (d, t, o, doc, ref), n in expand(data):
            w.writerow([d, t, o, doc, data["codes"].get(doc, ""), ref, n])
    print(f"{sum(r[5] for r in data['rows'])} views, {len(data['rows'])} rows, {days[0]} – {days[-1]}, {len(data['codes'])} documents matched to a PhilArchive record")


if __name__ == "__main__":
    main()
