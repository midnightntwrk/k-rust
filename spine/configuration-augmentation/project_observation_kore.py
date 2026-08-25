#!/usr/bin/env python3
from __future__ import annotations
import argparse, json, re
from pathlib import Path

markers={"observationCellLabel":r"observation'-GT-'","observationCellSort":r"SortObservationCell","observationInitializer":r"initObservationCell","observationUnit":r"Lbl'-LT-'observation'-GT-'"}
parser=argparse.ArgumentParser(); parser.add_argument("input",type=Path); parser.add_argument("output",type=Path); args=parser.parse_args()
text=args.input.read_text(encoding="utf-8"); line=next((v for v in text.splitlines() if "symbol Lbl'-LT-'observation'-GT-'" in v),"")
loc=re.search(r"Location\(([^)]*)\)",line); source=re.search(r"Source\(([^)]*)\)",line); src=source.group(1) if source else None
if src:
    for anchor in ("/p3/fixtures/","/investigations/w1-egress/fixtures/"):
        if anchor in src: src=src[src.index(anchor):]
result={"markers":{k:len(re.findall(v,text)) for k,v in markers.items()},"provenance":{"location":loc.group(1) if loc else None,"source":src}}
args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n",encoding="utf-8")
