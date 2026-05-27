from __future__ import annotations

import re
from dataclasses import dataclass, field

from agent.tools.latex_parser import ParsedTheorem, ProofStep, _sha256


@dataclass
class ParsedConjecture:
    conjecture_id: str        # "C2", "C4", …
    statement_latex: str      # raw LaTeX of the full statement (still inside $…$)
    hypotheses: list[str]     # conditions extracted from "If …"
    conclusion: str           # extracted from "then …"
    iris_scores: dict[str, float] = field(default_factory=dict)  # T, R, L, IRIS

    def to_parsed_theorem(self) -> ParsedTheorem:
        """Convert to ParsedTheorem with empty proof_steps for the prove pipeline."""
        name = self.conjecture_id
        synth = self._synth_latex()
        return ParsedTheorem(
            name=name,
            theorem_type="theorem",
            hypotheses=self.hypotheses,
            conclusion=self.conclusion,
            proof_steps=[],
            latex_source=synth,
            latex_hash=_sha256(synth),
            source_label=self.conjecture_id,
        )

    def _synth_latex(self) -> str:
        """Minimal LaTeX theorem block wrapping this conjecture (no proof)."""
        return (
            f"\\begin{{theorem}}[{self.conjecture_id}]\n"
            f"{self.statement_latex}\n"
            f"\\end{{theorem}}"
        )


# ---------------------------------------------------------------------------
# Statement parsing helpers
# ---------------------------------------------------------------------------

def _strip_dollar(s: str) -> str:
    s = s.strip()
    if s.startswith("$") and s.endswith("$"):
        s = s[1:-1].strip()
    return s


def _parse_if_then(latex_stmt: str) -> tuple[list[str], str]:
    """Split 'If CONDS, then CONCLUSION' into (hypotheses, conclusion).

    Works on the raw LaTeX string (still contains \\text{}, \\wedge, etc.).
    Falls back to ([], full_stmt) if the pattern is not found.
    """
    raw = _strip_dollar(latex_stmt)

    # Spacing commands: \; \, \! \:  — character after \ must be explicit (no ?)
    # to avoid eating the \ of the next \text / \wedge / etc.
    _SP = r"(?:\\[;,!:]\s*)*"

    # Split at ",SPACING\text{then }SPACING"
    split_re = re.compile(
        r"," + _SP + r"\\text\{then\s*\}\s*" + _SP,
        re.IGNORECASE,
    )
    parts = split_re.split(raw, maxsplit=1)

    if len(parts) != 2:
        return [], raw.strip()

    cond_part, conclusion = parts[0].strip(), parts[1].strip()

    # Remove leading "\text{If }SPACING"
    cond_part = re.sub(
        r"^\\text\{If\s*\}\s*" + _SP,
        "",
        cond_part,
        flags=re.IGNORECASE,
    ).strip()

    # Split conditions by \;\wedge\;  (spacing commands must be explicit)
    wedge_re = re.compile(_SP + r"\\wedge\s*" + _SP)
    conds = [c.strip() for c in wedge_re.split(cond_part) if c.strip()]

    return conds, conclusion.strip()


# ---------------------------------------------------------------------------
# Parser
# ---------------------------------------------------------------------------

class ConjectureParser:
    """Parses the conjecture longtable format from the IRIS conjectures TeX file.

    Each table row is a single physical line ending with \\\\ :
        C$_{N}$ & $STATEMENT$ & T & R & L & IRIS \\\\
    """

    # Identifies a row's first column: C$_{digits}$
    _ID_RE = re.compile(r"^C\$_\{(\d+)\}\$$")
    # Validates a score column (plain float)
    _FLOAT_RE = re.compile(r"^[\d.]+$")

    def parse_file(self, tex_source: str) -> list[ParsedConjecture]:
        """Return all conjectures found in *tex_source*, in document order."""
        conjectures: list[ParsedConjecture] = []
        for line in tex_source.splitlines():
            row = line.rstrip()
            # Every data row ends with \\ (two backslash chars)
            if not row.endswith("\\\\"):
                continue
            row = row[:-2].rstrip()

            # Split on & — expect exactly 6 columns
            cols = [c.strip() for c in row.split("&")]
            if len(cols) != 6:
                continue

            id_col, stmt_col, t_col, r_col, l_col, iris_col = cols

            # Validate ID column: must be exactly  C$_{N}$
            id_m = self._ID_RE.match(id_col)
            if not id_m:
                continue

            # Validate score columns
            if not all(self._FLOAT_RE.match(c) for c in (t_col, r_col, l_col, iris_col)):
                continue

            cid = f"C{id_m.group(1)}"
            statement = stmt_col
            t, r, l_score, iris = (
                float(t_col), float(r_col), float(l_col), float(iris_col)
            )
            hypotheses, conclusion = _parse_if_then(statement)
            conjectures.append(
                ParsedConjecture(
                    conjecture_id=cid,
                    statement_latex=statement,
                    hypotheses=hypotheses,
                    conclusion=conclusion,
                    iris_scores={"T": t, "R": r, "L": l_score, "IRIS": iris},
                )
            )
        return conjectures

    def parse_statement(self, statement_latex: str, conjecture_id: str = "C?") -> ParsedConjecture:
        """Parse a single statement string (e.g. pasted from the table)."""
        hypotheses, conclusion = _parse_if_then(statement_latex)
        return ParsedConjecture(
            conjecture_id=conjecture_id,
            statement_latex=statement_latex,
            hypotheses=hypotheses,
            conclusion=conclusion,
        )
