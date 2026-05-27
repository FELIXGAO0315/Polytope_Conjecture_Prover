"""
prompt_optimizer.py
===================
Token-budget utilities for the Lean 4 formalizer prompt pipeline.

Tier 1 — filter_dep_imports_to_direct   (drop transitive deps from prompt)
Tier 2 — extract_signature              (strip proof bodies; keep only signatures)
"""

from __future__ import annotations

import re


# ═══════════════════════════════════════════════════════════════════════════════
# TIER 1 — Selective Dep Injection
# ═══════════════════════════════════════════════════════════════════════════════

def filter_dep_imports_to_direct(
    node_deps: list[str],
    proven_dep_imports: dict[str, str],
) -> dict[str, str]:
    """Return only the imports for direct dependencies of this node.

    Drops transitive deps — when proving C (which depends on B which depends on A),
    only B's import is included, not A's.
    """
    return {
        dep_id: code
        for dep_id, code in proven_dep_imports.items()
        if dep_id in node_deps
    }


# ═══════════════════════════════════════════════════════════════════════════════
# TIER 2 — Signature-Only Imports
# ═══════════════════════════════════════════════════════════════════════════════

def extract_signature(lean_code: str) -> str:
    """Strip proof bodies from Lean 4 code, keeping only theorem signatures.

    A 100-line proof becomes a 3-line signature. Used for partial dep inline
    blocks so the LLM sees what the dep proves without wading through tactic noise.

    Input:
        theorem MyLemma (n : ℕ) : n + 0 = n := by
          simp
          ring

    Output:
        theorem MyLemma (n : ℕ) : n + 0 = n := by sorry -- proof omitted
    """
    lines = lean_code.split('\n')
    result_lines = []
    inside_proof = False

    for line in lines:
        stripped = line.strip()

        if re.match(r'^(theorem|lemma|def|noncomputable def)\s', stripped):
            inside_proof = False

        if ':= by' in line and not inside_proof:
            sig_part = line[:line.index(':= by')].rstrip()
            result_lines.append(sig_part + ' := by sorry -- proof omitted')
            inside_proof = True
            continue

        if re.search(r':=\s*$', line) and not inside_proof:
            result_lines.append(line.rstrip() + ' sorry -- proof omitted')
            inside_proof = True
            continue

        if inside_proof:
            if stripped and not stripped.startswith('--'):
                current_indent = len(line) - len(line.lstrip())
                if current_indent == 0 and stripped:
                    inside_proof = False
                    result_lines.append(line)
            continue

        result_lines.append(line)

    return '\n'.join(result_lines)


