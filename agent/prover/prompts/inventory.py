"""Single source of truth for the Inventory lemma catalogue.

The actual Lean proofs live in ``polib/Inventory.lean``.  This module
mirrors that catalogue in machine-readable form so every prompt that
references Inventory lemmas can render from one place — change a
signature here and the fix-loop reference, blueprint table, and
sorry-removal hints all update together.

Only lemmas that the prover prompts reference are listed.  Private
helpers (``sum_ico_3_7_weighted`` etc.) are intentionally omitted
since the prover never calls them directly.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Literal


@dataclass(frozen=True)
class InventoryLemma:
    name: str
    """Identifier used in Lean."""

    call_form: str
    """How the lemma is invoked, e.g. ``"P6InequalityPart maps hM hm"``.
    Spaces and argument names match the conventions the prompts use."""

    short_math: str
    """One-line ASCII/unicode math summary of the conclusion."""

    kind: Literal["axiom", "derived"]
    """``axiom`` = sorried in Inventory (geometric fact taken as primitive);
    ``derived`` = proved in Inventory from the axioms."""

    genus: Literal["any", "sphere"] = "any"
    """``sphere`` = restricted to ``SimplyCon3ConnectedMap 0`` only."""

    suffix_note: str = ""
    """Extra parenthetical shown after the math, e.g. the side-condition
    on ``hk`` for ``kgon_occupation_bound``."""

    proved_tag: str = ""
    """Trailing tag for the derived block, e.g. ``"(PROVED, no sorry)"``."""

    natural_lang: str = ""
    """Short natural-language description used by the blueprint planner's
    PROHIBITED_NODES table.  Empty if not exposed there."""

    lean_signature: str = ""
    """Exact Lean type expression of the lemma's conclusion (without the
    ``: Type :=`` head, just the proposition).  Used by the blueprint
    planner's "exact Lean signatures" reference so the LLM sees the precise
    API.  Empty if not exposed there."""

    requires_clause: str = ""
    """Trailing ``where ...`` clause spelling out side-conditions, e.g.
    ``"where hm : maps.m ≥ 6"``.  Combined with ``lean_signature`` for
    the blueprint signatures block."""


# ---------------------------------------------------------------------------
# THE catalogue.  Order is the order the prompts list them in — keeping it
# stable means renderer output is reproducible across runs.
# ---------------------------------------------------------------------------

INVENTORY: list[InventoryLemma] = [
    # ── Axiom block ───────────────────────────────────────────────────────
    InventoryLemma(
        name="euler_formula",
        call_form="euler_formula maps hM",
        short_math="(v:ℤ) - e + Σ_{k=3}^{m} p_i k = 2 - 2g",
        kind="axiom",
        natural_lang="Euler formula: V − E + F = 2 − 2g",
        lean_signature="(maps.v : ℤ) - maps.e + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 2 - 2 * g",
    ),
    InventoryLemma(
        name="handshake",
        call_form="handshake maps hM",
        short_math="2·e = Σ_{k=3}^{m} k·p_i k",
        kind="axiom",
        natural_lang="Handshaking lemma: 2E = Σ k·p_k",
        lean_signature="2 * maps.e = ∑ k ∈ Finset.Ico 3 (maps.m + 1), k * maps.p_i k",
    ),
    InventoryLemma(
        name="regularity",
        call_form="regularity maps hM",
        short_math="3·v = 2·e",
        kind="axiom",
        natural_lang="3-regularity: 3V = 2E",
        lean_signature="3 * maps.v = 2 * maps.e",
    ),
    InventoryLemma(
        name="kgon_occupation_bound",
        call_form="kgon_occupation_bound maps hM k hk",
        short_math="total_occ k ≤ (k:ℤ)/2 · p_k",
        kind="axiom",
        suffix_note="(hk : k ∈ Finset.Ico 4 (maps.m+1))",
    ),
    InventoryLemma(
        name="p_range",
        call_form="p_range maps hM k hk",
        short_math="p_i k = 0",
        kind="axiom",
        suffix_note="(when maps.m < k)",
    ),
    InventoryLemma(
        name="occupation_conservation",
        call_form="occupation_conservation maps hM hm",
        short_math="Σ_{k≥4} total_occ k = 3·p₃",
        kind="axiom",
        suffix_note="(hm : maps.m ≥ 6)",
    ),
    InventoryLemma(
        name="occupation_bound",
        call_form="occupation_bound maps hM k hk",
        short_math="0 ≤ total_occ k ∧ total_occ k ≤ (k:ℤ)/2·p_k",
        kind="axiom",
    ),
    InventoryLemma(
        name="quad_occ_cancellation",
        call_form="quad_occ_cancellation maps hM hm",
        short_math="Σ_{k∈[4,m]∖{6}} total_occ k ≤ Σ_{k∈[5,m]∖{6}} (k:ℤ)/2·p_k",
        kind="axiom",
        natural_lang="Quadrangle net-zero occupation: Σ_{k∈[4,m]∖{6}} occ ≤ Σ_{k∈[5,m]∖{6}} ⌊k/2⌋p_k",
    ),
    InventoryLemma(
        name="equality_family",
        call_form="equality_family n",
        short_math="∃ M_n, IsMap M_n ∧ M_n.m = n+3 ∧ p₆-equality",
        kind="axiom",
        suffix_note="(takes ONLY `n` — no maps argument)",
    ),

    # ── Derived block ─────────────────────────────────────────────────────
    InventoryLemma(
        name="P6EdgeCountEquation",
        call_form="P6EdgeCountEquation maps hM",
        short_math="3*p₃ = 12*(1-g) - 2*p₄ - p₅ + Σ_{k≥7}(k-6)*p_k",
        kind="derived",
        proved_tag="(PROVED, no sorry)",
        natural_lang="Dehn-Sommerville / edge-count eq: 3p₃ = 12(1−g) − 2p₄ − p₅ + Σ_{k≥7}(k−6)p_k",
        lean_signature="3 * (maps.p_i 3 : ℤ) = 12 * (1 - g) - 2 * (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ)",
    ),
    InventoryLemma(
        name="Juc_EulerFormula",
        call_form="Juc_EulerFormula maps hM",
        short_math="3*p₃ = 12 - 2*p₄ - p₅ + Σ_{k≥7}(k-6)*p_k",
        kind="derived",
        genus="sphere",
        proved_tag="(PROVED, g=0)",
        natural_lang="Edge-count equation for sphere (g=0): 3p₃ = 12 − 2p₄ − p₅ + Σ_{k≥7}(k−6)p_k",
        lean_signature="same for g=0 (M : SimplyCon3ConnectedMap 0)",
    ),
    InventoryLemma(
        name="P6InequalityPart",
        call_form="P6InequalityPart maps hM hm",
        short_math="3*p₆ ≥ 12*(1-g) - 2*p₄ - 3*p₅ + Σ_{k≥7}((k+1)/2-6)*p_k",
        kind="derived",
        proved_tag="(PROVED, no sorry)",
        natural_lang="Hexagon lower bound (general g): 3p₆ ≥ 12(1−g) − 2p₄ − 3p₅ + Σ_{k≥7}(⌊(k+1)/2⌋−6)p_k",
        lean_signature="3 * (maps.p_i 6 : ℤ) ≥ 12 * (1 - g) - 2 * (maps.p_i 4 : ℤ) - 3 * (maps.p_i 5 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ)",
        requires_clause="where `hm : maps.m ≥ 6`",
    ),
    InventoryLemma(
        name="Juc_InequalityPart",
        call_form="Juc_InequalityPart maps hM hm",
        short_math="same bound for g=0",
        kind="derived",
        genus="sphere",
        proved_tag="(PROVED, no sorry)",
        natural_lang="Hexagon lower bound (sphere g=0): same bound",
    ),
    InventoryLemma(
        name="Barnette_P6Bound",
        call_form="Barnette_P6Bound maps hM hm hsum",
        short_math="2*p₆ ≥ 4 + p₃ - p₅ - 2*Σ_{k≥7} p_k",
        kind="derived",
        genus="sphere",
        suffix_note="(g=0; requires hsum : Σ_{k≥7} p_k ≥ 3)",
        natural_lang="Barnette p₆ bound (sphere g=0): 2p₆ ≥ 4 + p₃ − p₅ − 2·Σ_{k≥7} p_k, requires Σ_{k≥7} p_k ≥ 3",
        lean_signature="2 * (maps.p_i 6 : ℤ) ≥ 4 + (maps.p_i 3 : ℤ) - (maps.p_i 5 : ℤ) - 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)",
        requires_clause="where `maps : SimplyCon3ConnectedMap 0`, `hm : maps.m ≥ 6`, `hsum : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 3`",
    ),
    InventoryLemma(
        name="JucovicTheorem",
        call_form="JucovicTheorem maps hM h1",
        short_math="hexagon lower bound ∧ equality family",
        kind="derived",
        genus="sphere",
        suffix_note="(g=0, h1 : Σp_k ≥ 7)",
        natural_lang="Jučovič theorem: lower bound ∧ equality family",
    ),
    InventoryLemma(
        name="Juc_HexMaxOccupation",
        call_form="Juc_HexMaxOccupation maps hM hm",
        short_math="total_occ 6 ≤ 3*p₆",
        kind="derived",
        proved_tag="(PROVED)",
    ),
    InventoryLemma(
        name="Juc_NonHexEdgeBound",
        call_form="Juc_NonHexEdgeBound maps hM hm",
        short_math="Σ_{k≥5,k≠6} total_occ k ≤ Σ_{k≥5,k≠6} (k/2)*p_k",
        kind="derived",
        proved_tag="(PROVED)",
    ),
]


# Convenience accessors
AXIOMS: list[InventoryLemma] = [l for l in INVENTORY if l.kind == "axiom"]
DERIVED: list[InventoryLemma] = [l for l in INVENTORY if l.kind == "derived"]


def by_name(name: str) -> InventoryLemma:
    for l in INVENTORY:
        if l.name == name:
            return l
    raise KeyError(f"Inventory lemma not found: {name!r}")


# ---------------------------------------------------------------------------
# Renderers — one per prompt format that quotes Inventory.  Add new renderers
# when new prompts need the catalogue; never duplicate the data.
# ---------------------------------------------------------------------------

def _render_lemma_line(lemma: InventoryLemma) -> str:
    """Render one bullet entry in the FIX_LOOP_POLIB_REF format."""
    suffix_bits: list[str] = []
    if lemma.suffix_note:
        suffix_bits.append(lemma.suffix_note)
    if lemma.proved_tag:
        suffix_bits.append(lemma.proved_tag)
    tail = ("  " + "  ".join(suffix_bits)) if suffix_bits else ""
    return f"- `{lemma.call_form}` → {lemma.short_math}{tail}"


def render_prohibited_nodes_table() -> str:
    """Render the markdown table of "ALREADY PROVED in Inventory" facts
    for the blueprint planner prompt.  Only lemmas with a ``natural_lang``
    string are included — those are the ones the planner is most likely to
    accidentally re-derive."""
    rows = [f"| {l.natural_lang} | `{l.call_form}` |"
            for l in INVENTORY if l.natural_lang]
    return (
        "| Mathematical content | Inventory lemma to call |\n"
        "|---|---|\n"
        + "\n".join(rows)
    )


def render_blueprint_signatures_section() -> str:
    """Render the "Inventory lemma exact Lean signatures" bullet list for
    the blueprint planner prompt.  Only lemmas with a ``lean_signature``
    string are listed — these are the ones whose precise API the planner
    needs in order to write correct ``Proved by: have ... := <call>`` hints
    in node descriptions."""
    lines = []
    for l in INVENTORY:
        if not l.lean_signature:
            continue
        sig = f"`{l.lean_signature}`"
        tail = f"  {l.requires_clause}" if l.requires_clause else ""
        lines.append(f"- `{l.call_form}` : {sig}{tail}")
    return "\n".join(lines)


def render_fix_loop_polib_ref() -> str:
    """Produce the FIX_LOOP_POLIB_REF block from the catalogue.

    Injected into every fix-loop prompt (targeted_fix / targeted_fix_strict
    / targeted_fix_decompose).  The generation system prompt is cached by
    the API and not re-sent on fix calls, so this block carries the
    Inventory references explicitly into every fix invocation.
    """
    axiom_lines = "\n".join(_render_lemma_line(l) for l in AXIOMS)
    derived_lines = "\n".join(_render_lemma_line(l) for l in DERIVED)
    return (
        "## ⚠ REALIZABILITY TOKEN: every axiom call below needs `hM : IsMap maps` — take it\n"
        "## from your theorem's own hypotheses and pass it as the argument right after `maps`.\n"
        "## `IsMap` is opaque: it can NEVER be proved for a constructed instance.\n"
        "\n"
        "## Inventory geometric axiom lemmas — call as STANDALONE functions (never dot-notation):\n"
        f"{axiom_lines}\n"
        "\n"
        "## Derived Inventory lemmas (PROVED or axiomatised — calling them does NOT add new sorry):\n"
        "These are available via `import Inventory` in any generated file. USE THESE instead of sorry.\n"
        f"{derived_lines}\n"
        "⚠ Calling any Inventory lemma is ACCEPTABLE even if it has sorry internally — you are\n"
        "  reusing the accepted, hand-curated axiom base, NOT introducing new sorry.\n"
        "⛔ The axiom base is CLOSED: NEVER write a new sorried helper lemma of your own,\n"
        "  even one that \"looks like\" content from the source papers. A file containing a\n"
        "  new sorry is REJECTED at save time.\n"
        "\n"
        "## Session-proved Polib lemmas (accumulated conjecture proofs):\n"
        "Check the \"Previously proved dependencies\" section in your prompt for what is\n"
        "currently available via `import Polib`. Only use a lemma name if it is EXPLICITLY listed there.\n"
        "Do NOT assume any specific name exists — if it is not listed, it does not exist yet.\n"
        "\n"
        "⛔ NEVER use `maps.euler_formula`, `maps.handshake`, etc. — dot-notation does NOT work.\n"
        "⛔ NEVER add fields to `SimplyCon3ConnectedMap` — structure has ONLY data fields.\n"
        "\n"
        "## Dependent type pitfalls — CRITICAL for fix-loop:\n"
        "- `regularity maps hM` / `handshake maps hM` return ℕ equations. Cast to ℤ with `exact_mod_cast`.\n"
        "- `(maps.total_faces : ℤ)` ≠ `∑ k ∈ Finset.Ico 3 (maps.m+1), (maps.p_i k : ℤ)` automatically.\n"
        "  Bridge: `simp [SimplyCon3ConnectedMap.total_faces, Nat.cast_sum]`\n"
        "- `rw [hg] at h` when `hg : g = 0` and `h` comes from `maps : SimplyCon3ConnectedMap g`\n"
        "  ALWAYS fails (\"motive is not type correct\"). Use `linarith [hg]` instead.\n"
    )
