#!/usr/bin/env python3
"""Task 4a/4b: per-proof dependency analysis. READ-ONLY, source-text only."""
import re, os, json

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# 1. inventory symbols (top-level lemma/theorem/def/opaque/axiom names)
inv = open(os.path.join(ROOT, "polib/Inventory.lean")).read()
inv_nocomment = re.sub(r'/-.*?-/', '', inv, flags=re.S)
inv_nocomment = re.sub(r'--[^\n]*', '', inv_nocomment)
inv_syms = set(re.findall(r'^\s*(?:private\s+|protected\s+|noncomputable\s+)*(?:lemma|theorem|def|opaque|axiom)\s+([A-Za-z_][A-Za-z0-9_\']*)', inv_nocomment, re.M))
# which inventory syms carry a sorry (owning-decl heuristic)
def sorry_owners(src):
    lines = src.splitlines()
    decl_re = re.compile(r'^\s*(?:private\s+|protected\s+|noncomputable\s+)*(?:lemma|theorem|def|opaque|axiom)\s+([A-Za-z_][A-Za-z0-9_\']*)')
    cur=None; owners={}
    for l in lines:
        m=decl_re.match(l)
        if m: cur=m.group(1)
        if re.search(r'\bsorry\b', l.split('--')[0]):
            owners[cur]=owners.get(cur,0)+1
    return owners
inv_sorry = sorry_owners(inv)

def analyze(path, rootname):
    src = open(path).read()
    src_nc = re.sub(r'--[^\n]*', '', src)
    # split into decl blocks: name -> body text
    decl_re = re.compile(r'^\s*(?:private\s+|protected\s+|noncomputable\s+)*(?:lemma|theorem|def)\s+([A-Za-z_][A-Za-z0-9_\']*)', re.M)
    marks = [(m.group(1), m.start()) for m in decl_re.finditer(src_nc)]
    blocks = {}
    for i,(name,start) in enumerate(marks):
        end = marks[i+1][1] if i+1 < len(marks) else len(src_nc)
        blocks[name] = src_nc[start:end]
    local = set(blocks)
    # references within a block (identifiers)
    def refs(body):
        ids = set(re.findall(r"[A-Za-z_][A-Za-z0-9_\']*", body))
        return ids
    # transitive closure from root over LOCAL helpers
    used_local = set()
    stack=[rootname]
    while stack:
        n = stack.pop()
        if n in used_local: continue
        used_local.add(n)
        for r in refs(blocks.get(n,"")):
            if r in local and r != n and r not in used_local:
                stack.append(r)
    # inventory symbols referenced anywhere in the used_local closure
    inv_used = set()
    for n in used_local:
        for r in refs(blocks[n]):
            if r in inv_syms:
                inv_used.add(r)
    all_declared = [name for name,_ in marks]
    unused = [d for d in all_declared if d not in used_local]
    return {
        "root": rootname,
        "declared": all_declared,
        "root_uses_local_helpers": sorted(used_local - {rootname}),
        "declared_but_unused_by_root": unused,
        "inventory_symbols_used_by_root_closure": sorted(inv_used),
        "inventory_used_that_are_sorried_base": sorted(s for s in inv_used if s in inv_sorry),
    }

targets = [
    ("output/conjecture_without_ce/c104/c104.lean", "C104"),
    ("output/conjecture_without_ce/c124/c124.lean", "C124"),
    ("output/conjecture_without_ce/c201/c201.lean", "C201"),
    ("output/conjecture_without_ce/c215/c215.lean", "C215"),
]
print("Inventory sorried-base owners:", sorted(inv_sorry))
print("="*70)
out = {}
for rel, root in targets:
    r = analyze(os.path.join(ROOT, rel), root)
    out[root] = r
    print(f"\n### {root}  ({rel})")
    print("  declared decls:", r["declared"])
    print("  root transitively uses local helpers:", r["root_uses_local_helpers"])
    print("  DECLARED BUT UNUSED by root:", r["declared_but_unused_by_root"])
    print("  inventory symbols used (root closure):", r["inventory_symbols_used_by_root_closure"])
    print("  ^ of which are SORRIED base lemmas:", r["inventory_used_that_are_sorried_base"])

json.dump(out, open(os.path.join(ROOT, "supplement_experiment/ablation/out/proof_deps.json"), "w"), indent=1)
print("\nwrote supplement_experiment/ablation/out/proof_deps.json")
