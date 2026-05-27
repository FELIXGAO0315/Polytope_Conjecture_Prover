from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass

from agent.exceptions import ParseError


@dataclass
class ProofStep:
    index: int
    latex_text: str
    step_type: str  # "suppose"|"therefore"|"by"|"let"|"have"|"conclude"|"other"
    references: list[str]

    def to_dict(self) -> dict:
        return {
            "index": self.index,
            "latex_text": self.latex_text,
            "step_type": self.step_type,
            "references": self.references,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "ProofStep":
        return cls(
            index=d["index"],
            latex_text=d["latex_text"],
            step_type=d["step_type"],
            references=d["references"],
        )


@dataclass
class ParsedTheorem:
    name: str
    theorem_type: str  # "theorem"|"lemma"|"proposition"|"corollary"|"definition"
    hypotheses: list[str]
    conclusion: str
    proof_steps: list[ProofStep]
    latex_source: str
    latex_hash: str
    source_label: str

    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "theorem_type": self.theorem_type,
            "hypotheses": self.hypotheses,
            "conclusion": self.conclusion,
            "proof_steps": [s.to_dict() for s in self.proof_steps],
            "latex_source": self.latex_source,
            "latex_hash": self.latex_hash,
            "source_label": self.source_label,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "ParsedTheorem":
        return cls(
            name=d["name"],
            theorem_type=d["theorem_type"],
            hypotheses=d["hypotheses"],
            conclusion=d["conclusion"],
            proof_steps=[ProofStep.from_dict(s) for s in d["proof_steps"]],
            latex_source=d["latex_source"],
            latex_hash=d["latex_hash"],
            source_label=d["source_label"],
        )


_THEOREM_ENVS = ["theorem", "lemma", "proposition", "corollary", "definition"]

_HYPO_KEYWORDS = re.compile(
    r"^(Let|Assume|Suppose|For all|If|Given)\b",
    re.IGNORECASE,
)
_HYPO_LATEX = re.compile(r"\\(forall|exists|Rightarrow|Leftarrow|implies)\b")

_CONCLUSION_KEYWORDS = re.compile(
    r"^(Then|We have|It follows that|Hence|Therefore|We conclude|We get|This gives)\b",
    re.IGNORECASE,
)

_STEP_MARKERS = re.compile(
    r"^(?:First[,.]|Second[,.]|Next[,.]|Now[,.]|Finally[,.]|Therefore[,.]|Hence[,.]|"
    r"Since\b|By\b|Note that\b|Observe that\b|We have\b|We get\b|It follows\b|"
    r"Suppose\b|Let\b|Define\b|Set\b|Consider\b|Apply\b|Using\b)",
    re.IGNORECASE,
)

_STEP_SPLIT_PATTERN = (
    r"(?<=[.!?;])\s+(?="
    r"(?:First[,.]|Second[,.]|Next[,.]|Now[,.]|Finally[,.]|Therefore[,.]|Hence[,.]|"
    r"Since\b|By\b|Note that\b|Observe that\b|We have\b|We get\b|It follows\b|"
    r"Suppose\b|Let\b|Define\b|Set\b|Consider\b|Apply\b|Using\b)"
    r")"
)

_REFERENCE_PATTERNS = [
    re.compile(r"\\ref\{([^}]+)\}"),
    re.compile(r"\\cite\{([^}]+)\}"),
    re.compile(
        r"\b(?:by|from|using|via|applying)\s+(?:Theorem|Lemma|Proposition|Corollary|Fact|Claim)\s+([\d.]+)",
        re.IGNORECASE,
    ),
    re.compile(r"\[([^\]]+)\]"),
]

_STEP_TYPE_MAP = [
    ("suppose", re.compile(r"^(Suppose|Assume|Let|If)\b", re.IGNORECASE)),
    ("therefore", re.compile(r"^(Therefore|Hence|Thus|So|We conclude|It follows)\b", re.IGNORECASE)),
    ("by", re.compile(r"^(By|Using|Applying|From)\b", re.IGNORECASE)),
    ("let", re.compile(r"^(Let|Set|Define|Consider)\b", re.IGNORECASE)),
    ("have", re.compile(r"^(We have|We get|Note that|Observe that)\b", re.IGNORECASE)),
    ("conclude", re.compile(r"^(Finally|This completes|QED|This shows)\b", re.IGNORECASE)),
]


def _sha256(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def _to_camel_case(text: str) -> str:
    words = re.sub(r"[^a-zA-Z0-9 ]+", " ", text).split()
    return "".join(w.capitalize() for w in words[:4]) if words else "UnknownTheorem"


def _extract_references(text: str) -> list[str]:
    refs: list[str] = []
    for pattern in _REFERENCE_PATTERNS:
        refs.extend(pattern.findall(text))
    seen: set[str] = set()
    unique: list[str] = []
    for r in refs:
        if r not in seen:
            seen.add(r)
            unique.append(r)
    return unique


def _classify_step_type(text: str) -> str:
    stripped = text.strip()
    for step_type, pattern in _STEP_TYPE_MAP:
        if pattern.match(stripped):
            return step_type
    return "other"


def _split_into_steps(proof_text: str) -> list[str]:
    # Split by blank lines first
    paragraphs = re.split(r"\n{2,}", proof_text)
    steps: list[str] = []
    for para in paragraphs:
        para = para.strip()
        if not para:
            continue
        # Further split long paragraphs at transition word boundaries
        sentences = re.split(r"(?<=[.!?])\s+(?=[A-Z])", para)
        for sentence in sentences:
            sentence = sentence.strip()
            if not sentence:
                continue
            # Split again at step markers mid-sentence
            sub = re.split(_STEP_SPLIT_PATTERN, sentence, flags=re.IGNORECASE)
            for s in sub:
                s = s.strip()
                if s:
                    steps.append(s)
    return steps if steps else [proof_text.strip()]


class LatexParser:
    def parse_with_llm(
        self,
        latex_source: str,
        client,
        model: str = "claude-haiku-4-5-20251001",
    ) -> "ParsedTheorem":
        """Parse theorem structure using a Claude call instead of regex.

        More robust for non-standard LaTeX formatting.
        Falls back to the regex parser if the LLM returns invalid output.
        """
        import json as _json
        import re as _re

        PROMPT = (
            "Extract the structure of the following LaTeX theorem. "
            "Return ONLY valid JSON with these exact keys:\n"
            '  "name": string (CamelCase identifier based on label or conclusion)\n'
            '  "theorem_type": one of theorem|lemma|proposition|corollary|definition\n'
            '  "hypotheses": list of strings (the given assumptions)\n'
            '  "conclusion": string (what must be proved)\n'
            '  "source_label": string (the \\label{} value, or empty string)\n\n'
            "LaTeX source:\n" + latex_source
        )

        try:
            response = client.messages.create(
                model=model,
                max_tokens=512,
                messages=[{"role": "user", "content": PROMPT}],
            )
            text = response.content[0].text.strip()
            # Strip markdown fences if present
            m = _re.search(r"\{.*\}", text, _re.DOTALL)
            if not m:
                raise ValueError("No JSON object found in LLM response")
            data = _json.loads(m.group())

            latex_hash = _sha256(latex_source)

            # Parse proof steps with the existing regex method
            proof_steps: list[ProofStep] = []
            proof_match = _re.search(
                r"\\begin\{proof\}(.*?)\\end\{proof\}", latex_source, _re.DOTALL
            )
            if proof_match:
                raw_steps = _split_into_steps(proof_match.group(1).strip())
                for i, step_text in enumerate(raw_steps):
                    proof_steps.append(ProofStep(
                        index=i,
                        latex_text=step_text,
                        step_type=_classify_step_type(step_text),
                        references=_extract_references(step_text),
                    ))

            return ParsedTheorem(
                name=data.get("name", "UnknownTheorem"),
                theorem_type=data.get("theorem_type", "theorem"),
                hypotheses=data.get("hypotheses", []),
                conclusion=data.get("conclusion", ""),
                proof_steps=proof_steps,
                latex_source=latex_source,
                latex_hash=latex_hash,
                source_label=data.get("source_label", ""),
            )

        except Exception:
            # If the LLM call fails for any reason, fall back to regex parser
            return self.parse(latex_source)

    def parse(self, latex_source: str) -> ParsedTheorem:
        latex_hash = _sha256(latex_source)

        # 1. Detect theorem environment
        env_match = None
        theorem_type = ""
        for env in _THEOREM_ENVS:
            pattern = re.compile(
                rf"\\begin\{{{env}\}}(.*?)\\end\{{{env}\}}", re.DOTALL
            )
            m = pattern.search(latex_source)
            if m:
                env_match = m
                theorem_type = env
                break

        if env_match is None:
            raise ParseError(
                "No supported theorem environment found "
                "(theorem, lemma, proposition, corollary, definition).",
                partial_result=None,
            )

        env_body = env_match.group(1)

        # 2. Extract source label
        source_label = ""
        label_match = re.search(r"\\label\{([^}]+)\}", env_body)
        if label_match:
            source_label = label_match.group(1)
        else:
            ref_match = re.search(
                r"\((?:Theorem|Lemma|Proposition|Corollary|Definition)\s+([\d.]+)\)",
                env_body,
                re.IGNORECASE,
            )
            if ref_match:
                source_label = f"{theorem_type.capitalize()} {ref_match.group(1)}"

        # 3. Separate statement from proof
        proof_pattern = re.compile(r"\\begin\{proof\}(.*?)\\end\{proof\}", re.DOTALL)
        proof_match = proof_pattern.search(latex_source)
        proof_text = proof_match.group(1).strip() if proof_match else ""

        # Statement body = env body without nested proof
        statement_body = re.sub(r"\\begin\{proof\}.*?\\end\{proof\}", "", env_body, flags=re.DOTALL).strip()
        statement_body = re.sub(r"\\label\{[^}]+\}", "", statement_body).strip()

        # 4. Extract hypotheses and conclusion from statement
        lines = [l.strip() for l in re.split(r"[.\n]+", statement_body) if l.strip()]
        hypotheses: list[str] = []
        conclusion_lines: list[str] = []
        in_conclusion = False

        for line in lines:
            if not line:
                continue
            if _CONCLUSION_KEYWORDS.match(line) or in_conclusion:
                in_conclusion = True
                conclusion_lines.append(line)
            elif _HYPO_KEYWORDS.match(line) or _HYPO_LATEX.search(line):
                hypotheses.append(line)
            else:
                # Ambiguous lines before conclusion go to hypotheses if we have none yet
                if not conclusion_lines:
                    hypotheses.append(line)
                else:
                    conclusion_lines.append(line)

        # Fallback: if nothing detected as hypothesis, treat all-but-last as hypothesis
        if not hypotheses and len(lines) >= 2:
            hypotheses = lines[:-1]
            conclusion_lines = lines[-1:]

        conclusion = " ".join(conclusion_lines) if conclusion_lines else (lines[-1] if lines else "")

        # 5. Split proof into steps
        raw_steps = _split_into_steps(proof_text) if proof_text else []
        proof_steps: list[ProofStep] = []
        for i, step_text in enumerate(raw_steps):
            proof_steps.append(
                ProofStep(
                    index=i,
                    latex_text=step_text,
                    step_type=_classify_step_type(step_text),
                    references=_extract_references(step_text),
                )
            )

        # 6. Infer name
        name = ""
        if source_label:
            # Convert label to CamelCase
            name = _to_camel_case(re.sub(r"[^a-zA-Z0-9]", " ", source_label))
        if not name:
            name = _to_camel_case(conclusion)
        if not name:
            name = "UnknownTheorem"

        return ParsedTheorem(
            name=name,
            theorem_type=theorem_type,
            hypotheses=hypotheses,
            conclusion=conclusion,
            proof_steps=proof_steps,
            latex_source=latex_source,
            latex_hash=latex_hash,
            source_label=source_label,
        )
