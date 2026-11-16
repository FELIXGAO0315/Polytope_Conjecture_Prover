#!/usr/bin/env python3
"""E5: per-theorem TRANSITIVE trusted-base.

proof_deps.json records the inventory symbols each root theorem's local closure
references, but stops one level into the inventory. A per-theorem audit
ask for the *trusted assumptions* of each theorem -- i.e. the sorry-marked base
lemmas it ultimately rests on, resolved transitively THROUGH the inventory's own
proof graph. This script does that closure. READ-ONLY, source-text only.
"""
import re, os, json
from collections import deque

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
INV = os.path.join(ROOT, "polib/Inventory.lean")
DEPS = os.path.join(ROOT, "scripts/ablation/out/proof_deps.json")

src = open(INV).read()
nc = re.sub(r'/-.*?-/', '', src, flags=re.S)
nc = re.sub(r'--[^\n]*', '', nc)
decl = re.compile(r'^\s*(?:private\s+|protected\s+|noncomputable\s+)*'
                  r'(?:lemma|theorem|def|opaque|axiom)\s+([A-Za-z_][\w\']*)', re.M)
marks = [(m.group(1), m.start()) for m in decl.finditer(nc)]
names = [m[0] for m in marks]
nameset = set(names)

body = {}
has_sorry = set()
refs = {}
for i, (name, s) in enumerate(marks):
    e = marks[i+1][1] if i+1 < len(marks) else len(nc)
    b = nc[s:e]
    body[name] = b
    # strip the decl's own name token region (header) when scanning refs
    ids = set(re.findall(r"[A-Za-z_][\w\']*", b))
    refs[name] = (ids & nameset) - {name}
    if re.search(r'\bsorry\b', b):
        has_sorry.add(name)

def trusted_base(seed_syms):
    """BFS through inventory dep graph; return the sorried base decls reached."""
    seen = set()
    q = deque(s for s in seed_syms if s in nameset)
    reached_sorry = set()
    while q:
        n = q.popleft()
        if n in seen:
            continue
        seen.add(n)
        if n in has_sorry:
            reached_sorry.add(n)
        for r in refs.get(n, ()):
            if r not in seen:
                q.append(r)
    return reached_sorry, seen

deps = json.load(open(DEPS))
print(f"Inventory: {len(names)} decls, {len(has_sorry)} carry sorry: {sorted(has_sorry)}\n")
print("=== PER-THEOREM TRANSITIVE TRUSTED BASE (sorry-marked lemmas each theorem rests on) ===\n")
label = {"C104": "Thm 1  (p4=0,p5<=2,f2>=7 => 2p6>=4-S)",
         "C201": "Thm 2  (p4=p5=0,S>=1 => p6>=2-S)",
         "C215": "Thm 3  (p4=p5=0,f2>=7 => 3p6+2S>=12)",
         "C124": "Thm 4  (2p6<=2f2-2p4-2p5, elementary)"}
rows = []
for cid in ["C104", "C201", "C215", "C124"]:
    seeds = deps[cid]["inventory_symbols_used_by_root_closure"]
    sorried, allreach = trusted_base(seeds)
    rows.append((cid, sorted(sorried)))
    print(f"{label.get(cid,cid)}")
    print(f"   inventory symbols directly in root closure : {sorted(s for s in seeds if s!='IsMap')}")
    print(f"   => TRANSITIVE sorry-base trusted assumptions: {sorted(sorried)}  (count {len(sorried)})")
    print()

out = os.path.join(ROOT, "scripts/ablation/out/trusted_base.json")
json.dump({cid: sb for cid, sb in rows}, open(out, "w"), indent=1)
print(f"wrote {out}")
