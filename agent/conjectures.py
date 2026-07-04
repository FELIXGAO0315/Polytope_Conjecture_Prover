from __future__ import annotations

import json
import os
from dataclasses import dataclass
from typing import Iterable, List, Optional, Union, Dict, Any, Tuple
import time
import re
from math import isfinite


@dataclass
class ConjectureSpec:
    name: str
    formula: str  # expected format: "if (<hypothesis>), then <conjecture>"


@dataclass
class ConjectureFormula:
    condition_code: str
    conjecture_code: str
    rhs_code: str
    coefficients: Dict[str, float]
    required_properties: List[str]
    raw_formula: str
    threshold: Optional[float]
    is_linear: bool = True
    relation: str = ">="  # either ">=" (p6 lower bound) or "<=" (p6 upper bound)


_SUM_AT_LEAST_RE = re.compile(r"sum_pk_k>=7_at_least_(\d+)")
_SUM_THRESHOLD_RE = re.compile(r"sum_pk_k>=7\s*>=\s*([+-]?\d+(?:/\d+)?(?:\.\d+)?)", re.IGNORECASE)
_F2_THRESHOLD_RE = re.compile(r"f_2>=_(\d+)", re.IGNORECASE)
_VAR_PATTERN = re.compile(r"\b(p_?[3456]|sum_pk_k>=7|sum_pk_after_p6)\b")
_SAFE_VARS = ("p3", "p4", "p5", "p6", "sum_pk_after_p6")

# Structural-predicate column names emitted by dataset.py — Graffiti3 picks
# them up by name, but downstream evaluators (pvec_eval) want them in the
# DSL forms `p_<k> = <n>` / `p_<k> <= <n>`. We translate at canonicalize
# time so render, parser, hint store and pool-gate all see the same shape.
_STRUCT_EQ_RE = re.compile(r"\bp(?:_)?([3-9])_eq_(\d+)\b")
_STRUCT_LE_RE = re.compile(r"\bp(?:_)?([3-9])_le_(\d+)\b")
_STRUCT_GE_RE = re.compile(r"\bp(?:_)?([3-9])_ge_(\d+)\b")


def canonicalize_hypothesis_tokens(expr: str) -> str:
    """Normalize hypothesis tokens.

    Rewrites:
      - `sum_pk_k>=7_at_least_j` → `sum_pk_k>=7 >= j`
      - `p<k>_eq_<n>`            → `p_<k> = <n>`     (Eberhard / Jučovič)
      - `p<k>_le_<n>`            → `p_<k> <= <n>`    (Grünbaum tails)
      - `p<k>_ge_<n>`            → `p_<k> >= <n>`
    """
    if not isinstance(expr, str) or not expr:
        return expr

    def _replace(match: re.Match[str]) -> str:
        value = match.group(1)
        try:
            value = str(int(value))
        except Exception:
            pass
        return f"sum_pk_k>=7 >= {value}"

    out = _SUM_AT_LEAST_RE.sub(_replace, expr)
    # Split joint structural columns BEFORE the single-predicate regex:
    # `p3_eq_0_and_p4_eq_0` would not match `\bp_eq_0\b` because the `\b`
    # after the digit fails when followed by `_and_…`. Inserting an explicit
    # ` and ` at every `_and_` between two structural tokens makes each
    # piece word-bounded so the regex matches both.
    out = re.sub(r"(eq_\d+|le_\d+|ge_\d+)_and_(p)", r"\1 and \2", out)
    out = _STRUCT_EQ_RE.sub(lambda m: f"p_{m.group(1)} = {m.group(2)}", out)
    out = _STRUCT_LE_RE.sub(lambda m: f"p_{m.group(1)} <= {m.group(2)}", out)
    out = _STRUCT_GE_RE.sub(lambda m: f"p_{m.group(1)} >= {m.group(2)}", out)
    return out


def canonicalize_formula(formula: str) -> str:
    """Return conjecture formula with canonicalized hypothesis tokens."""
    if not isinstance(formula, str):
        return formula
    return canonicalize_hypothesis_tokens(formula.replace('≥', '>=').strip())


class AdvancedConjectureParser:
    """Parse string conjectures into executable components shared across agents."""

    def parse_formula_with_coefficients(self, formula: str) -> ConjectureFormula:
        canonical = canonicalize_formula(formula or "")
        if not canonical.lower().startswith("if"):
            raise ValueError(f"Formula must start with 'if (...)': {formula}")

        match = re.match(r"if\s*\((.*?)\)\s*,?\s*then\s*(.*)", canonical, re.IGNORECASE | re.DOTALL)
        if not match:
            raise ValueError(f"Cannot split hypothesis/conclusion: {formula}")

        condition_expr = match.group(1).strip()
        conclusion_expr = match.group(2).strip()

        condition_code, threshold, cond_props = self._compile_condition(condition_expr)
        coefficients, rhs_code, rhs_props, is_linear, relation = self._compile_conclusion(conclusion_expr)

        required_props = sorted(set(cond_props) | set(rhs_props))
        conj_code = f"props['p6'] >= ({rhs_code})" if relation == ">=" else f"props['p6'] <= ({rhs_code})"
        return ConjectureFormula(
            condition_code=condition_code,
            conjecture_code=conj_code,
            rhs_code=rhs_code,
            coefficients=coefficients,
            required_properties=required_props,
            raw_formula=canonical,
            threshold=threshold,
            is_linear=is_linear,
            relation=relation,
        )

    def _compile_condition(self, expr: str) -> Tuple[str, Optional[float], List[str]]:
        base_check = "props.get('is_polytope', props.get('is_simple', False))"
        expr = expr.strip()
        if not expr or expr.lower() in ("true",):
            return base_check, None, ["is_polytope"]

        required_props = {"is_polytope"}
        threshold: Optional[float] = None
        working = expr

        def _parse_number(raw: str) -> float:
            try:
                value = float(eval(raw, {"__builtins__": {}}))
            except Exception as err:
                raise ValueError(f"Invalid numeric literal '{raw}' in condition '{expr}': {err}") from err
            if not isfinite(value):
                raise ValueError(f"Non-finite numeric literal '{raw}' in condition '{expr}'")
            return value

        def _replace_sum(match: re.Match[str]) -> str:
            nonlocal threshold
            value = _parse_number(match.group(1))
            if threshold is None:
                threshold = value
            required_props.update({"sum_pk_after_p6"})
            return f"(props.get('sum_pk_after_p6', 0) >= {value})"

        working = _SUM_THRESHOLD_RE.sub(_replace_sum, working)

        def _replace_f2(match: re.Match[str]) -> str:
            required_props.update({"p_vector"})
            value = int(match.group(1))
            return f"(sum(props.get('p_vector', []) or []) >= {value})"

        working = _F2_THRESHOLD_RE.sub(_replace_f2, working)

        # Normalize references to simple / cubic property using placeholders to avoid double substitution.
        working = re.sub(r"\bis_polytope\b", "__IS_POLY__", working)
        working = re.sub(r"\bis_simple\b", "__IS_SIMPLE__", working)

        # Replace remaining variable tokens with property lookups.
        def _var_to_prop(match: re.Match[str]) -> str:
            text = match.string
            start_index = match.start()
            if start_index > 0 and text[start_index - 1] in ("'", '"'):
                return match.group(0)
            token = match.group(1)
            token = token.replace("p_", "p")
            if token == "sum_pk_k>=7":
                token = "sum_pk_after_p6"
            required_props.add(token if token != "sum_pk_after_p6" else "sum_pk_after_p6")
            return f"props.get('{token}', 0)"

        working = _VAR_PATTERN.sub(_var_to_prop, working)

        # Restore placeholders
        working = working.replace("__IS_POLY__", base_check)
        working = working.replace("__IS_SIMPLE__", base_check)

        # Lift single `=` (DSL equality) to Python `==`, leaving the relational
        # operators `>=`, `<=`, `!=`, `==` untouched. Needed for structural
        # predicates like `(p_3 = 0)` so the compiled condition is a valid
        # Python expression. Negative lookarounds match a `=` not already part
        # of a relational operator.
        working = re.sub(r"(?<![<>=!])=(?!=)", "==", working)

        # Replace logical operators variants.
        working = working.replace("&&", " and ").replace("||", " or ")

        final_code = f"({base_check} and ({working}))"
        return final_code, threshold, list(required_props)

    def _compile_conclusion(self, expr: str) -> Tuple[Dict[str, float], str, List[str], bool, str]:
        expr = expr.strip()
        # Accept forms: p6 >= ..., p6 <= ..., -p6 >= ..., -p6 <= ...
        relation = ">="
        rhs_raw = None

        match_ge = re.match(r"p6\s*>=\s*(.*)", expr, re.IGNORECASE)
        match_le = re.match(r"p6\s*<=\s*(.*)", expr, re.IGNORECASE)
        match_neg_ge = re.match(r"-\s*p6\s*>=\s*(.*)", expr, re.IGNORECASE)
        match_neg_le = re.match(r"-\s*p6\s*<=\s*(.*)", expr, re.IGNORECASE)

        if match_ge:
            relation = ">="
            rhs_raw = match_ge.group(1).strip()
        elif match_le:
            relation = "<="
            rhs_raw = match_le.group(1).strip()
        elif match_neg_ge:
            # -p6 >= rhs  =>  p6 <= -rhs
            relation = "<="
            rhs_raw = f"-({match_neg_ge.group(1).strip()})"
        elif match_neg_le:
            # -p6 <= rhs  =>  p6 >= -rhs
            relation = ">="
            rhs_raw = f"-({match_neg_le.group(1).strip()})"
        else:
            raise ValueError(f"Conclusion must be of form 'p6 >= ...' or 'p6 <= ...': {expr}")

        # strip parens
        if rhs_raw.startswith("(") and rhs_raw.endswith(")"):
            rhs_raw = rhs_raw[1:-1].strip()

        rhs_norm = (
            rhs_raw.replace("sum_pk_k>=7", "sum_pk_after_p6")
            .replace("sum_pk_after_p6", "sum_pk_after_p6")
            .replace("p_", "p")
        )

        nonlinear_markers = ("sqrt", "log", "ln", "exp", "**", "^", "²")
        is_linear = not any(tok in rhs_norm for tok in nonlinear_markers)
        coeffs: Dict[str, float]
        try:
            coeffs = self._extract_coefficients(rhs_norm) if is_linear else {"const": 0.0}
        except Exception:
            coeffs = {"const": 0.0}
            is_linear = False

        rhs_code = self._rhs_props_expression(rhs_norm)

        required = ["p3", "p4", "p5", "p6", "sum_pk_after_p6"]
        return coeffs, rhs_code, required, is_linear, relation

    def _extract_coefficients(self, expr: str) -> Dict[str, float]:
        allowed = {name: 0.0 for name in _SAFE_VARS}

        def _safe_eval(values: Dict[str, float]) -> float:
            env = {name: values.get(name, 0.0) for name in allowed}
            try:
                return float(eval(expr, {"__builtins__": {}}, env))
            except Exception as err:
                raise ValueError(f"Failed to evaluate RHS '{expr}': {err}") from err

        base = _safe_eval({})
        coeffs: Dict[str, float] = {"const": base}
        for var in _SAFE_VARS:
            value = _safe_eval({var: 1.0}) - base
            if abs(value) < 1e-12:
                value = 0.0
            if var == "sum_pk_after_p6":
                if value != 0.0:
                    coeffs["sum_pk"] = value
            elif value != 0.0:
                coeffs[var] = value

        return coeffs

    def _rhs_props_expression(self, expr: str) -> str:
        # If the expression already uses explicit props.get(...), don't re-wrap; assume user-supplied code.
        if "props.get(" in expr:
            return expr
        code = expr
        replacements = [
            (r"\bsum_pk_after_p6\b", "props.get('sum_pk_after_p6', 0)"),
            (r"\bsum_pk_k>=7\b", "props.get('sum_pk_after_p6', 0)"),
            (r"\bp3\b", "props.get('p3', 0)"),
            (r"\bp4\b", "props.get('p4', 0)"),
            (r"\bp5\b", "props.get('p5', 0)"),
            (r"\bp6\b", "props.get('p6', 0)"),
        ]
        for pattern, repl in replacements:
            code = re.sub(pattern, repl, code)
        return code


def _from_json_obj(obj: dict, index: int) -> Optional[ConjectureSpec]:
    # Accept either a single "formula" or a split hypothesis/conjecture
    name = obj.get("name") or obj.get("id") or f"conj_{index}"
    if "formula" in obj and isinstance(obj["formula"], str):
        return ConjectureSpec(name=name, formula=canonicalize_formula(obj["formula"]))
    hyp = obj.get("hypothesis")
    conj = obj.get("conjecture")
    if isinstance(hyp, str) and isinstance(conj, str):
        combined = f"if ({hyp}), then {conj}"
        return ConjectureSpec(name=name, formula=canonicalize_formula(combined))
    return None


def _default_conjecture_dir() -> str:
    here = os.path.dirname(__file__)
    return os.path.normpath(os.path.join(here, "..", "conjectures"))


def load_conjectures_with_status(source: Optional[Union[str, os.PathLike]] = None) -> Tuple[List[ConjectureSpec], Dict[str, str]]:
    """Load conjectures and (optional) per-conjecture status.

    Supports:
      - JSONL file: data/conjectures.jsonl where each line is {name, formula} or {name, hypothesis, conjecture}
      - JSON array: data/conjectures.json with same schema
      - JSON object with keys "unsolved" and/or "solved": each is a list of entries
    - Text files: data/conjectures/*.txt, one formula per non-empty line
    """
    specs: List[ConjectureSpec] = []
    statuses: Dict[str, str] = {}

    # Resolve source
    if source is None:
        source_dir = _default_conjecture_dir()
    else:
        source_dir = str(source)

    # JSONL
    jsonl_path = os.path.join(source_dir, "conjectures.jsonl") if os.path.isdir(source_dir) else source_dir
    if os.path.isfile(jsonl_path):
        with open(jsonl_path, "r") as f:
            for i, line in enumerate(f):
                line = line.strip()
                if not line:
                    continue
                try:
                    obj = json.loads(line)
                    spec = _from_json_obj(obj, i)
                    if spec:
                        specs.append(spec)
                except Exception:
                    continue

    # JSON array or object with solved/unsolved
    if os.path.isdir(source_dir):
        json_path = os.path.join(source_dir, "conjectures.json")
    elif source_dir.endswith('.json') and os.path.isfile(source_dir):
        json_path = source_dir
    else:
        json_path = None
    if json_path and os.path.isfile(json_path):
        try:
            with open(json_path, "r") as f:
                data = json.load(f)
            if isinstance(data, list):
                for i, obj in enumerate(data):
                    if isinstance(obj, dict):
                        spec = _from_json_obj(obj, i)
                        if spec:
                            specs.append(spec)
            elif isinstance(data, dict):
                # New schema: unsolved/failed/proved. `solved` (legacy) is
                # treated the same as `failed`.
                _key_status = {
                    "unsolved": "unsolved",
                    "failed": "falsified",
                    "solved": "falsified",   # legacy alias
                    "proved": "proven",
                }
                for status_key, items in data.items():
                    if status_key not in _key_status or not isinstance(items, list):
                        continue
                    for i, obj in enumerate(items):
                        if isinstance(obj, dict):
                            spec = _from_json_obj(obj, i)
                            if spec:
                                specs.append(spec)
                                statuses[spec.name] = _key_status[status_key]
        except Exception:
            pass

    # Text files
    if os.path.isdir(source_dir):
        for fn in os.listdir(source_dir):
            if fn.lower().endswith(".txt"):
                try:
                    with open(os.path.join(source_dir, fn), "r") as f:
                        for i, line in enumerate(f):
                            s = line.strip()
                            if s:
                                formula = canonicalize_formula(s)
                                specs.append(ConjectureSpec(name=f"{os.path.splitext(fn)[0]}_{i}", formula=formula))
                except Exception:
                    continue

    return specs, statuses


def load_conjectures(source: Optional[Union[str, os.PathLike]] = None) -> List[ConjectureSpec]:
    specs, _ = load_conjectures_with_status(source)
    return specs


# Registry utilities to track conjecture status

def _registry_path(source_dir: Optional[str] = None) -> str:
    if source_dir is None:
        source_dir = _default_conjecture_dir()
    return os.path.join(source_dir, "registry.json")


def load_registry(source_dir: Optional[str] = None) -> Dict[str, Dict[str, Any]]:
    path = _registry_path(source_dir)
    if os.path.isfile(path):
        try:
            with open(path, "r") as f:
                return json.load(f)
        except Exception:
            return {}
    return {}


def save_registry(reg: Dict[str, Dict[str, Any]], source_dir: Optional[str] = None) -> None:
    path = _registry_path(source_dir)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        json.dump(reg, f, indent=2)
    os.replace(tmp, path)


def ensure_registry_for_specs(specs: List[ConjectureSpec], reg: Dict[str, Dict[str, Any]],
                              initial_status: Optional[Dict[str, str]] = None) -> Dict[str, Dict[str, Any]]:
    now = int(time.time())
    for s in specs:
        if s.name not in reg:
            reg[s.name] = {
                "name": s.name,
                "formula": s.formula,
                "status": (initial_status.get(s.name) if initial_status and s.name in initial_status else "unsolved"),
                "created_at": now,
                "attempts_without_ce": 0,
                "ce_found_count": 0,
                "potentially_valid": False,
            }
        else:
            # Keep formula in sync if changed
            reg[s.name].setdefault("formula", s.formula)
            reg[s.name].setdefault("attempts_without_ce", 0)
            reg[s.name].setdefault("ce_found_count", 0)
            reg[s.name].setdefault("potentially_valid", False)
    return reg


def load_iris_scores(source: Optional[Union[str, os.PathLike]] = None) -> Dict[str, Dict[str, Any]]:
    """Read IRIS scores from conjectures.json. Single source of truth — no
    registry mirroring. Returns {name: iris_dict}."""
    out: Dict[str, Dict[str, Any]] = {}
    try:
        raw = _load_raw_dataset(str(source) if source else None)
    except Exception:
        return out
    for e in _all_entries(raw):
        iris = e.get("iris")
        name = e.get("name")
        if name and isinstance(iris, dict):
            out[name] = iris
    return out


def mark_conjecture_status(name: str, status: str, reg: Dict[str, Dict[str, Any]], **updates) -> None:
    rec = reg.setdefault(name, {"name": name, "status": status})
    rec["status"] = status
    if status == "falsified":
        rec.setdefault("solved_at", int(time.time()))
    rec.update(updates)


def record_ce_found(name: str, reg: Dict[str, Dict[str, Any]]) -> None:
    rec = reg.setdefault(name, {"name": name})
    rec["status"] = "falsified"
    rec["ce_found_count"] = int(rec.get("ce_found_count", 0)) + 1
    rec["solved_at"] = int(time.time())
    rec["last_attempt_at"] = rec["solved_at"]
    # When CE found, attempts_without_ce becomes irrelevant; optionally reset
    rec["attempts_without_ce"] = 0
    rec["potentially_valid"] = False


def increment_attempt(name: str, reg: Dict[str, Dict[str, Any]], threshold: int = 20) -> None:
    rec = reg.setdefault(name, {"name": name})
    rec["attempts_without_ce"] = int(rec.get("attempts_without_ce", 0)) + 1
    rec["last_attempt_at"] = int(time.time())
    if rec["attempts_without_ce"] >= int(threshold):
        # Keep status as unsolved but mark as potentially_valid
        rec["potentially_valid"] = True


def sync_registry_from_ce_map(reg: Dict[str, Dict[str, Any]], map_path: Optional[str] = None) -> Dict[str, Dict[str, Any]]:
    """Ensure any conjecture that already has stored CE polytope_ids is marked falsified."""
    if map_path is None:
        map_path = os.path.join(_default_conjecture_dir(), "conjecture_ce_map.json")
    if not os.path.exists(map_path):
        return reg
    try:
        data = json.load(open(map_path, "r"))
    except Exception:
        return reg
    now = int(time.time())
    for name, rec in data.items():
        ids = rec.get("polytope_ids") or []
        if not ids:
            continue
        r = reg.setdefault(name, {"name": name, "status": "unsolved", "created_at": now})
        if r.get("status") != "falsified":
            r["status"] = "falsified"
            r["ce_found_count"] = int(r.get("ce_found_count", 0)) + len(ids)
            r["solved_at"] = r.get("solved_at", now)
            r["last_attempt_at"] = r.get("last_attempt_at", now)
            r["attempts_without_ce"] = 0
            r["potentially_valid"] = False
    return reg


def _dataset_path(dest: Optional[str] = None) -> str:
    dest_dir = _default_conjecture_dir() if dest is None else dest
    if os.path.isdir(dest_dir):
        return os.path.join(dest_dir, 'conjectures.json')
    return dest_dir


def load_conjecture_dataset(
    dest: Optional[str] = None,
) -> Tuple[List[ConjectureSpec], List[ConjectureSpec], List[ConjectureSpec]]:
    """Load conjectures.json split by bucket → (unsolved, failed, proved).

    Tolerates the legacy ``solved`` key by folding it into ``failed`` (same
    treatment as ``_load_raw_dataset``)."""
    data = _load_raw_dataset(dest)

    def _specs(bucket: str) -> List[ConjectureSpec]:
        out: List[ConjectureSpec] = []
        for entry in data.get(bucket, []):
            if entry.get('name') and entry.get('formula'):
                out.append(ConjectureSpec(
                    name=entry['name'],
                    formula=canonicalize_formula(entry['formula']),
                ))
        return out

    return _specs('unsolved'), _specs('failed'), _specs('proved')


_BUCKETS = ("unsolved", "failed", "proved")


def _load_raw_dataset(dest: Optional[str] = None) -> Dict[str, List[dict]]:
    """Load conjectures.json preserving every per-entry field (status, …).

    Reads the new 3-bucket schema (unsolved/failed/proved). The legacy
    ``solved`` key (where 'solved' == 'falsified') is folded into ``failed``
    on load for backward compatibility with old files."""
    empty = {b: [] for b in _BUCKETS}
    path = _dataset_path(dest)
    if not os.path.isfile(path):
        return empty
    try:
        with open(path, "r") as f:
            data = json.load(f)
    except Exception:
        return empty
    out = {b: [e for e in data.get(b, []) if isinstance(e, dict)] for b in _BUCKETS}
    # Legacy: `solved` used to hold refuted entries. Merge into `failed`.
    legacy_solved = [e for e in data.get("solved", []) if isinstance(e, dict)]
    if legacy_solved:
        seen = {e.get("name") for e in out["failed"]}
        for e in legacy_solved:
            if e.get("name") not in seen:
                out["failed"].append(e)
    return out


_NAME_SUFFIX_RE = re.compile(r"^(.*?)(\d+)$")


def _natural_sort_key(entry: dict) -> Tuple[str, int, str]:
    """Sort key that puts `foo_2` before `foo_10` (numeric suffix, not lex).

    Matches both the legacy `auto_<ts>_<n>` shape and the new bare `C<n>`
    shape (trailing digits with any prefix).  Falls back to (name, 0) for
    entries that don't end in digits so we never crash on legacy names."""
    name = entry.get("name") or ""
    m = _NAME_SUFFIX_RE.match(name)
    if m:
        return (m.group(1), int(m.group(2)), name)
    return (name, 0, name)


def _write_raw_dataset(data: Dict[str, List[dict]], dest: Optional[str] = None) -> str:
    path = _dataset_path(dest)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".tmp"
    obj = {b: sorted(data.get(b, []), key=_natural_sort_key) for b in _BUCKETS}
    with open(tmp, "w") as f:
        json.dump(obj, f, indent=2)
    os.replace(tmp, path)
    return path


def _all_entries(data: Dict[str, List[dict]]) -> List[dict]:
    """Flatten every bucket into a single list of entries."""
    return [e for b in _BUCKETS for e in data.get(b, [])]


def upsert_conjectures(specs: Iterable[ConjectureSpec], dest: Optional[str] = None,
                       iris_by_name: Optional[Dict[str, Dict[str, Any]]] = None) -> List[str]:
    """Insert new conjectures, de-duping by normalized formula against BOTH
    lists. New entries land in unsolved with status='new'; existing entries
    and all their fields are preserved verbatim. Returns inserted names.

    iris_by_name (optional): {spec.name: iris_dict} computed by
    `agent.conjecture_generator.tools.iris_scoring.compute_iris`. Attached as
    the per-entry "iris" field so the RL CE finder can pick it up via
    ensure_registry_for_specs."""
    specs = list(specs)
    if not specs:
        return []

    data = _load_raw_dataset(dest)
    iris_by_name = iris_by_name or {}

    def _norm(formula: str) -> str:
        try:
            return canonicalize_formula(formula or "")
        except Exception:
            return (formula or "").strip()

    all_entries = _all_entries(data)
    existing_formulas = {_norm(e.get("formula", "")) for e in all_entries}
    used_names = {e.get("name") for e in all_entries}

    inserted: List[str] = []
    inserted_specs: List[ConjectureSpec] = []
    now = int(time.time())
    for spec in specs:
        f_norm = _norm(spec.formula)
        if f_norm in existing_formulas:
            continue
        name = spec.name or "auto"
        if name in used_names:
            suffix = 1
            while f"{name}_{suffix}" in used_names:
                suffix += 1
            name = f"{name}_{suffix}"
        entry = {
            "name": name,
            "formula": canonicalize_formula(spec.formula),
            "status": "new",
            "created_at": now,
        }
        iris = iris_by_name.get(spec.name)
        if iris:
            entry["iris"] = iris
        data["unsolved"].append(entry)
        used_names.add(name)
        existing_formulas.add(f_norm)
        inserted.append(name)
        inserted_specs.append(ConjectureSpec(name=name, formula=entry["formula"]))

    if inserted:
        _write_raw_dataset(data, dest)
        # Registry entry from day one, so attempts_without_ce accumulates no
        # matter which CE entry point later runs the conjecture (the survivor
        # signal died once because only one RL path ever created entries).
        # Only for the canonical layout — a custom `dest` has no registry.
        if dest is None:
            try:
                reg = ensure_registry_for_specs(inserted_specs, load_registry())
                save_registry(reg)
            except Exception:
                pass
    return inserted


# Which bucket does each status live in? Only the terminal outcomes
# (`refuted` = has CE, `proven` = has Lean proof) move out of unsolved.
# `new` and `prover_failed` both mean "still undecided": a prover_failed
# conjecture might be true — the prover just couldn't close it.
_STATUS_BUCKET = {
    "new": "unsolved",
    "prover_failed": "unsolved",
    "refuted": "failed",
    "proven": "proved",
}


def set_conjecture_status(
    name: str,
    status: str,
    dest: Optional[str] = None,
    detail: Optional[Dict[str, Any]] = None,
) -> bool:
    """Update a conjecture's status in conjectures.json and move it to the
    bucket that matches the terminal outcome. Returns False if not found.

    Buckets: ``unsolved`` (new / prover_failed), ``failed`` (refuted CE
    exists), ``proved`` (Lean proof exists)."""
    data = _load_raw_dataset(dest)
    entry, src = None, None
    for key in _BUCKETS:
        for e in data[key]:
            if e.get("name") == name:
                entry, src = e, key
                break
        if entry is not None:
            break
    if entry is None:
        return False
    entry["status"] = status
    entry["status_at"] = int(time.time())
    if detail:
        entry["status_detail"] = detail
    dst = _STATUS_BUCKET.get(status, src)
    if dst != src:
        data[src].remove(entry)
        data[dst].append(entry)
    _write_raw_dataset(data, dest)
    return True


def get_conjectures_by_status(status: str, dest: Optional[str] = None) -> List[ConjectureSpec]:
    """Return specs whose entry carries exactly this status (any bucket)."""
    data = _load_raw_dataset(dest)
    out: List[ConjectureSpec] = []
    for e in _all_entries(data):
        if e.get("status") == status and e.get("name") and e.get("formula"):
            out.append(ConjectureSpec(name=e["name"],
                                      formula=canonicalize_formula(e["formula"])))
    return out


def mark_conjecture_as_solved(name: str, dest: Optional[str] = None) -> None:
    """Legacy API kept for the RL CE finder: marks a conjecture as refuted
    (which moves it to the ``failed`` bucket).  The name comes from the
    old schema where 'solved' meant 'falsified'."""
    if not name:
        return
    set_conjecture_status(name, "refuted", dest)


# ── artifact reconcile — the single status-sync implementation ──────────────
#
# Every terminal outcome the pipeline produces leaves an artifact on disk:
#   CE found     → output/conjecture_with_ce/<Cx>/<Cx>.json
#   Lean proof   → output/conjecture_without_ce/<cx>/<cx>.lean  (or legacy flat)
#   prover stuck → output/conjecture_without_ce/<Cx>.json  (evolution-loop record)
# but not every entry point that produces them also updates conjectures.json
# (a direct `formalize` run updates nothing). Reconcile folds the on-disk
# truth back into the dataset; it is idempotent and cheap, so both run.py and
# the conjecture generator call it unconditionally before reading statuses.

_TRAILING_NUM_RE = re.compile(r"(\d+)$")


def _entry_num(name: str) -> Optional[int]:
    m = _TRAILING_NUM_RE.search(name or "")
    return int(m.group(1)) if m else None


def _has_active_sorry(lean_text: str) -> bool:
    """True if a `sorry` survives outside `--` comments. The pipeline never
    saves dirty proofs, but reconcile re-checks before trusting a .lean file
    as a proof — the no-new-sorry rule is enforced at every layer."""
    for line in lean_text.splitlines():
        code = line.split("--", 1)[0]
        if re.search(r"\bsorry\b", code):
            return True
    return False


def reconcile_from_artifacts(dest: Optional[str] = None,
                             verbose: bool = True) -> Dict[str, str]:
    """Scan pipeline output artifacts and fold terminal outcomes into
    conjectures.json. Returns {name: new_status} for entries that changed.

    Precedence: a verified CE beats a proof file (both present for one
    conjecture means something is deeply wrong — warned loudly, refuted
    wins because the CE is machine-checked data, not LLM output). The
    evolution loop's `prover_failed` records only apply to entries that
    have no terminal outcome."""
    root = os.path.normpath(os.path.join(os.path.dirname(__file__), ".."))
    ce_dir = os.path.join(root, "output", "conjecture_with_ce")
    no_ce_dir = os.path.join(root, "output", "conjecture_without_ce")
    proof_dir = os.path.join(root, "output", "conjecture_proof")  # legacy

    data = _load_raw_dataset(dest)
    by_num: Dict[int, Tuple[str, dict]] = {}
    for bucket in _BUCKETS:
        for e in data[bucket]:
            num = _entry_num(e.get("name") or "")
            if num is not None:
                by_num[num] = (bucket, e)

    import glob as _glob

    # Collect proofs: per-stem subdirs + legacy flat files, both output dirs.
    # A .lean artifact is a proof of C<num> ONLY if the ROOT theorem is
    # actually declared in it. Step 8 of the prover saves partial artifacts
    # (proved sub-lemmas only, zero sorry) even when the run FAILED — those
    # must land in `partials`, not `proofs`, or a failed formalization gets
    # recorded as proven (C1/C193 incident, 2026-07-03).
    proofs: Dict[int, str] = {}
    partials: Dict[int, str] = {}
    _failed_hdr = re.compile(r"^--\s*Failed\s*\((\d+)\)", re.MULTILINE)
    for pattern in (os.path.join(no_ce_dir, "*", "*.lean"),
                    os.path.join(no_ce_dir, "*.lean"),
                    os.path.join(proof_dir, "*", "*.lean"),
                    os.path.join(proof_dir, "*.lean")):
        for lf in sorted(_glob.glob(pattern)):
            num = _entry_num(os.path.splitext(os.path.basename(lf))[0])
            if num is None or num in proofs:
                continue
            try:
                text = open(lf).read()
            except Exception:
                continue
            rel = os.path.relpath(lf, root)
            if _has_active_sorry(text):
                if verbose:
                    print(f"[reconcile] WARNING: {lf} contains an active "
                          f"`sorry` — not treated as a proof", flush=True)
                partials.setdefault(num, rel)
                continue
            m = _failed_hdr.search(text)
            root_decl = re.search(
                rf"^\s*(?:private\s+|protected\s+)?(?:theorem|lemma)\s+"
                rf"C{num}(?:_Main)?\b", text, re.MULTILINE)
            if (m and int(m.group(1)) > 0) or root_decl is None:
                if verbose:
                    why = (f"header declares {m.group(1)} failed node(s)"
                           if m and int(m.group(1)) > 0
                           else f"root theorem C{num} not declared")
                    print(f"[reconcile] {rel}: partial formalization "
                          f"({why}) — not treated as a proof", flush=True)
                partials.setdefault(num, rel)
                continue
            proofs[num] = rel
            partials.pop(num, None)

    # Collect CEs (with detail for the refuted signal).
    ces: Dict[int, Dict[str, Any]] = {}
    for jf in sorted(_glob.glob(os.path.join(ce_dir, "*", "*.json"))):
        num = _entry_num(os.path.splitext(os.path.basename(jf))[0])
        if num is None or num in ces:
            continue
        try:
            payload = json.load(open(jf))
        except Exception:
            continue
        ce = payload.get("counterexample") or {}
        detail: Dict[str, Any] = {}
        vec = ce.get("p_vector")
        if isinstance(vec, list):
            pv = {str(i + 3): int(v) for i, v in enumerate(vec) if int(v or 0)}
            if pv:
                detail["ce_p_vector"] = pv
        if payload.get("violation_detail"):
            detail["violation"] = payload["violation_detail"]
        ces[num] = detail

    # Collect evolution-loop prover_failed records (top-level {Cx}.json).
    # A record contradicted by hard evidence (a proof file or a CE artifact
    # that arrived later) is STALE — delete it so the directory listing and
    # the prover-stuck signal stay truthful.
    stuck: Dict[int, str] = {}
    for jf in sorted(_glob.glob(os.path.join(no_ce_dir, "*.json"))):
        num = _entry_num(os.path.splitext(os.path.basename(jf))[0])
        if num is None:
            continue
        try:
            payload = json.load(open(jf))
        except Exception:
            continue
        if payload.get("status") != "prover_failed":
            continue
        if num in proofs or num in ces:
            try:
                os.remove(jf)
                if verbose:
                    evidence = "proof" if num in proofs else "CE"
                    print(f"[reconcile] removed stale prover_failed record "
                          f"{os.path.basename(jf)} (superseded by {evidence})",
                          flush=True)
            except Exception:
                pass
            continue
        stuck[num] = payload.get("outcome") or "failed"

    changes: Dict[str, str] = {}

    def _apply(num: int, status: str, detail: Optional[Dict[str, Any]]) -> None:
        bucket, entry = by_num[num]
        target_bucket = _STATUS_BUCKET.get(status, bucket)
        if entry.get("status") == status and bucket == target_bucket:
            return
        entry["status"] = status
        entry["status_at"] = int(time.time())
        if detail:
            entry.setdefault("status_detail", {}).update(detail)
        if target_bucket != bucket:
            data[bucket].remove(entry)
            data[target_bucket].append(entry)
            by_num[num] = (target_bucket, entry)
        changes[entry.get("name") or str(num)] = status

    for num, path in proofs.items():
        if num in by_num and num not in ces:
            _apply(num, "proven", {"proof": path})
    for num, detail in ces.items():
        if num not in by_num:
            continue
        if num in proofs and verbose:
            print(f"[reconcile] WARNING: #{num} has BOTH a CE artifact and a "
                  f"proof file — keeping refuted; inspect immediately",
                  flush=True)
        _apply(num, "refuted", detail or None)
    # Demotion: an entry sitting in `proved` with no qualifying proof
    # artifact must not stay proven — artifacts on disk are the truth
    # source. A partial artifact (prover ran and failed) demotes to
    # prover_failed; no artifact at all demotes to new.
    for num in list(by_num):
        bucket, entry = by_num[num]
        if bucket != "proved" or num in proofs or num in ces:
            continue
        entry.get("status_detail", {}).pop("proof", None)  # stale pointer
        if num in partials:
            _apply(num, "prover_failed",
                   {"outcome": "partial_formalization",
                    "partial": partials[num]})
        else:
            _apply(num, "new", None)
        if verbose:
            print(f"[reconcile] DEMOTED {entry.get('name') or num}: was in "
                  f"'proved' without a qualifying proof artifact", flush=True)
    for num, outcome in stuck.items():
        if num in by_num and num not in ces and num not in proofs:
            bucket, entry = by_num[num]
            if bucket == "unsolved" and entry.get("status") in (None, "new"):
                _apply(num, "prover_failed", {"outcome": outcome})

    if changes:
        _write_raw_dataset(data, dest)
        if verbose:
            print(f"[reconcile] {len(changes)} status change(s): "
                  + ", ".join(f"{n}→{s}" for n, s in sorted(changes.items())),
                  flush=True)
    return changes
