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


def canonicalize_hypothesis_tokens(expr: str) -> str:
    """Normalize hypothesis tokens: `sum_pk_k>=7_at_least_j` → `sum_pk_k>=7 >= j`."""
    if not isinstance(expr, str) or not expr:
        return expr

    def _replace(match: re.Match[str]) -> str:
        value = match.group(1)
        try:
            value = str(int(value))
        except Exception:
            pass
        return f"sum_pk_k>=7 >= {value}"

    return _SUM_AT_LEAST_RE.sub(_replace, expr)


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
                for status_key, items in data.items():
                    if status_key not in ("unsolved", "solved") or not isinstance(items, list):
                        continue
                    for i, obj in enumerate(items):
                        if isinstance(obj, dict):
                            spec = _from_json_obj(obj, i)
                            if spec:
                                specs.append(spec)
                                statuses[spec.name] = "falsified" if status_key == "solved" else "unsolved"
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


def export_conjectures(specs: List[ConjectureSpec], dest: Optional[str] = None) -> str:
    """Append or write conjectures to a JSONL file in the conjectures dir."""
    dest_dir = _default_conjecture_dir()
    if dest is None:
        dest = os.path.join(dest_dir, "conjectures.jsonl")
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    with open(dest, "a") as f:
        for i, s in enumerate(specs):
            f.write(json.dumps({"name": s.name, "formula": canonicalize_formula(s.formula)}) + "\n")
    return dest


def write_conjectures_dataset(unsolved: List[ConjectureSpec], solved: Optional[List[ConjectureSpec]] = None,
                              dest: Optional[str] = None) -> str:
    """Write a JSON object with {"unsolved": [...], "solved": [...]} to conjectures.json.

    Overwrites the file to reflect current dataset.
    """
    if solved is None:
        solved = []
    dest_dir = _default_conjecture_dir()
    if dest is None:
        dest = os.path.join(dest_dir, "conjectures.json")
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    obj = {
        "unsolved": [{"name": s.name, "formula": canonicalize_formula(s.formula)} for s in unsolved],
        "solved": [{"name": s.name, "formula": canonicalize_formula(s.formula)} for s in solved],
    }
    tmp = dest + ".tmp"
    with open(tmp, "w") as f:
        json.dump(obj, f, indent=2)
    os.replace(tmp, dest)
    return dest


def _dataset_path(dest: Optional[str] = None) -> str:
    dest_dir = _default_conjecture_dir() if dest is None else dest
    if os.path.isdir(dest_dir):
        return os.path.join(dest_dir, 'conjectures.json')
    return dest_dir


def load_conjecture_dataset(dest: Optional[str] = None) -> Tuple[List[ConjectureSpec], List[ConjectureSpec]]:
    path = _dataset_path(dest)
    if not os.path.isfile(path):
        return [], []
    try:
        with open(path, 'r') as f:
            data = json.load(f)
    except Exception:
        return [], []
    unsolved_specs: List[ConjectureSpec] = []
    solved_specs: List[ConjectureSpec] = []
    for entry in data.get('unsolved', []):
        if isinstance(entry, dict) and entry.get('name') and entry.get('formula'):
            formula = canonicalize_formula(entry['formula'])
            unsolved_specs.append(ConjectureSpec(name=entry['name'], formula=formula))
    for entry in data.get('solved', []):
        if isinstance(entry, dict) and entry.get('name') and entry.get('formula'):
            formula = canonicalize_formula(entry['formula'])
            solved_specs.append(ConjectureSpec(name=entry['name'], formula=formula))
    return unsolved_specs, solved_specs


def _load_raw_dataset(dest: Optional[str] = None) -> Dict[str, List[dict]]:
    """Load conjectures.json preserving every per-entry field (status, …)."""
    path = _dataset_path(dest)
    if not os.path.isfile(path):
        return {"unsolved": [], "solved": []}
    try:
        with open(path, "r") as f:
            data = json.load(f)
    except Exception:
        return {"unsolved": [], "solved": []}
    return {
        "unsolved": [e for e in data.get("unsolved", []) if isinstance(e, dict)],
        "solved": [e for e in data.get("solved", []) if isinstance(e, dict)],
    }


def _write_raw_dataset(data: Dict[str, List[dict]], dest: Optional[str] = None) -> str:
    path = _dataset_path(dest)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        json.dump({"unsolved": data.get("unsolved", []),
                   "solved": data.get("solved", [])}, f, indent=2)
    os.replace(tmp, path)
    return path


def upsert_conjectures(specs: Iterable[ConjectureSpec], dest: Optional[str] = None) -> List[str]:
    """Insert new conjectures, de-duping by normalized formula against BOTH
    lists. New entries land in unsolved with status='new'; existing entries
    and all their fields are preserved verbatim. Returns inserted names."""
    specs = list(specs)
    if not specs:
        return []

    data = _load_raw_dataset(dest)

    def _norm(formula: str) -> str:
        try:
            return canonicalize_formula(formula or "")
        except Exception:
            return (formula or "").strip()

    all_entries = data["unsolved"] + data["solved"]
    existing_formulas = {_norm(e.get("formula", "")) for e in all_entries}
    used_names = {e.get("name") for e in all_entries}

    inserted: List[str] = []
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
        data["unsolved"].append({
            "name": name,
            "formula": canonicalize_formula(spec.formula),
            "status": "new",
            "created_at": now,
        })
        used_names.add(name)
        existing_formulas.add(f_norm)
        inserted.append(name)

    if inserted:
        _write_raw_dataset(data, dest)
    return inserted


def set_conjecture_status(
    name: str,
    status: str,
    dest: Optional[str] = None,
    detail: Optional[Dict[str, Any]] = None,
) -> bool:
    """Update a conjecture's status in conjectures.json.

    status ∈ {'new', 'refuted', 'proven', 'prover_failed'}. 'refuted' entries
    move to the legacy 'solved' list (solved == falsified for older
    consumers); other statuses update in place. Returns False if not found.
    """
    data = _load_raw_dataset(dest)
    entry, src = None, None
    for key in ("unsolved", "solved"):
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
    if status == "refuted" and src == "unsolved":
        data["unsolved"].remove(entry)
        data["solved"].append(entry)
    _write_raw_dataset(data, dest)
    return True


def get_conjectures_by_status(status: str, dest: Optional[str] = None) -> List[ConjectureSpec]:
    """Return specs whose entry carries exactly this status (both lists)."""
    data = _load_raw_dataset(dest)
    out: List[ConjectureSpec] = []
    for e in data["unsolved"] + data["solved"]:
        if e.get("status") == status and e.get("name") and e.get("formula"):
            out.append(ConjectureSpec(name=e["name"],
                                      formula=canonicalize_formula(e["formula"])))
    return out


def mark_conjecture_as_solved(name: str, dest: Optional[str] = None) -> None:
    """Legacy API: a solved conjecture is a falsified one — now also records
    status='refuted' and preserves all entry fields."""
    if not name:
        return
    set_conjecture_status(name, "refuted", dest)
