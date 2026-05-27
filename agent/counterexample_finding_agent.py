import copy
import re
import numpy as np
import math
import networkx as nx
import torch
import torch.nn as nn
import torch.optim as optim
import torch.nn.functional as F
from torch.distributions import Categorical
from collections import defaultdict, deque
from datetime import datetime
import json
import os
from typing import Dict, List, Tuple, Optional
from tqdm import tqdm

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

import graphcalc as gc
from pathlib import Path
from dataclasses import dataclass as _dataclass


@_dataclass
class ConjectureFormula:
    coefficients: dict        # {'p3': float, 'p4': float, 'p5': float, 'sum_pk': float, 'const': float}
    threshold: Optional[float]  # e.g. sum_pk_k>=7 >= 10 → 10.0
    relation: str             # ">=" or "<="
    condition_code: str       # Python expr for: lambda G, props: <this>
    conjecture_code: str      # Python expr for: lambda G, props: <this>
    rhs_code: str             # Python expr evaluated with {"props": props}


@_dataclass
class ConjectureSpec:
    name: str
    formula: str


class AdvancedConjectureParser:
    """Parse formula strings like 'if (...), then p6 >= RHS' into ConjectureFormula."""

    _VAR_SUBS = [
        (re.compile(r'sum_pk_k>=\d+'), "props.get('sum_pk_after_p6', 0)"),
        (re.compile(r'\bsum_pk\b'),    "props.get('sum_pk_after_p6', 0)"),
        # p3-p6 must be substituted BEFORE f2, so the f2 replacement string
        # (which contains literal 'p3','p4',... as dict keys) is not double-substituted.
        (re.compile(r'\bp3\b'), "props.get('p3', 0)"),
        (re.compile(r'\bp4\b'), "props.get('p4', 0)"),
        (re.compile(r'\bp5\b'), "props.get('p5', 0)"),
        (re.compile(r'\bp6\b'), "props.get('p6', 0)"),
        (re.compile(r'\bf2\b'),
            "(props.get('p3',0)+props.get('p4',0)+props.get('p5',0)"
            "+props.get('p6',0)+props.get('sum_pk_after_p6',0))"),
    ]

    def _to_props_expr(self, s: str) -> str:
        for pattern, replacement in self._VAR_SUBS:
            s = pattern.sub(replacement, s)
        return s

    def _extract_threshold(self, cond: str) -> Optional[float]:
        m = re.search(r'sum_pk_k>=\d+\s*>=\s*(\d+(?:\.\d+)?)', cond)
        if m:
            return float(m.group(1))
        m = re.search(r'(?:f2|p\d+)\s*>=\s*(\d+(?:\.\d+)?)', cond)
        if m:
            return float(m.group(1))
        return None

    def _extract_coefficients(self, rhs_code: str) -> dict:
        keys = ['p3', 'p4', 'p5', 'sum_pk_after_p6']

        def _eval(props_dict):
            try:
                return float(eval(rhs_code, {'__builtins__': {}}, {'props': props_dict}))
            except Exception:
                return 0.0

        base = {k: 0.0 for k in keys}
        const_val = _eval(base)
        coeffs: dict = {'const': const_val}
        for key in keys:
            test = {k: 0.0 for k in keys}
            test[key] = 1.0
            out_key = 'sum_pk' if key == 'sum_pk_after_p6' else key
            coeffs[out_key] = round(_eval(test) - const_val, 8)
        return coeffs

    def parse_formula_with_coefficients(self, formula: str) -> ConjectureFormula:
        f = formula.strip()
        lower_f = f.lower()

        if lower_f.startswith("if "):
            then_idx = lower_f.rfind(", then ")
            if then_idx != -1:
                cond_raw = f[3:then_idx].strip()
                conc_raw = f[then_idx + 7:].strip()
            else:
                then_idx = lower_f.rfind(" then ")
                cond_raw = f[3:then_idx].strip() if then_idx != -1 else ""
                conc_raw = f[then_idx + 6:].strip() if then_idx != -1 else f[3:].strip()
        elif lower_f.startswith("then "):
            cond_raw = ""
            conc_raw = f[5:].strip()
        else:
            cond_raw = ""
            conc_raw = f

        if cond_raw.startswith("(") and cond_raw.endswith(")"):
            cond_raw = cond_raw[1:-1]

        m_conc = re.match(r'p6\s*(>=|<=)\s*(.+)$', conc_raw, re.DOTALL)
        if m_conc:
            relation = m_conc.group(1)
            rhs_str = m_conc.group(2).strip()
        else:
            relation = ">="
            rhs_str = conc_raw

        rhs_code = self._to_props_expr(rhs_str)
        condition_code = self._to_props_expr(cond_raw) if cond_raw else "True"
        conjecture_code = f"props.get('p6', 0) {relation} ({rhs_code})"

        return ConjectureFormula(
            coefficients=self._extract_coefficients(rhs_code),
            threshold=self._extract_threshold(cond_raw) if cond_raw else None,
            relation=relation,
            condition_code=condition_code,
            conjecture_code=conjecture_code,
            rhs_code=rhs_code,
        )

if torch.cuda.is_available():
    major, minor = torch.cuda.get_device_capability()
    if major < 7:
        device = torch.device('cpu')
    else:
        device = torch.device('cuda')
else:
    device = torch.device('cpu')


def chop_y_insert_triangle(G, v):
    if G.degree(v) != 3:
        raise ValueError(f"Vertex {v} degree != 3")
    G2 = G.copy()
    neighbors = list(G2.neighbors(v))
    G2.remove_node(v)
    next_id = max(G2.nodes()) + 1 if G2.nodes() else 0
    a, b, c = next_id, next_id + 1, next_id + 2
    G2.add_nodes_from([a, b, c])
    G2.add_edges_from([(a, b), (b, c), (c, a), (a, neighbors[0]), (b, neighbors[1]), (c, neighbors[2])])
    return G2, [a, b, c], neighbors


def compute_graph_properties(G):
    try:
        is_polytope = gc.simple_polytope_graph(G) if G.number_of_nodes() >= 4 and all(d == 3 for _, d in G.degree()) else False
        p_vec = gc.p_vector(G) if is_polytope else [G.number_of_nodes(), 0, 0, 0]
    except Exception:
        is_polytope = False
        p_vec = [G.number_of_nodes(), 0, 0, 0]
    return {
        'num_vertices': G.number_of_nodes(),
        'num_edges': G.number_of_edges(),
        'is_cubic': all(d == 3 for _, d in G.degree()),
        'is_polytope': is_polytope,
        'p_vector': p_vec,
        'p3':  p_vec[0] if len(p_vec) > 0 else 0,
        'p4':  p_vec[1] if len(p_vec) > 1 else 0,
        'p5':  p_vec[2] if len(p_vec) > 2 else 0,
        'p6':  p_vec[3] if len(p_vec) > 3 else 0,
        'p7':  p_vec[4] if len(p_vec) > 4 else 0,
        'p8':  p_vec[5] if len(p_vec) > 5 else 0,
        'p9':  p_vec[6] if len(p_vec) > 6 else 0,
        'p10': p_vec[7] if len(p_vec) > 7 else 0,
        'p11plus': sum(p_vec[8:]) if len(p_vec) > 8 else 0,
        'sum_pk_after_p6': sum(p_vec[4:]) if len(p_vec) > 4 else 0,
    }


def evaluate_rhs(conjecture_or_coeffs, props: Dict[str, float]) -> float:
    """Compute RHS for both linear dicts and ConjectureFormula with rhs_code."""
    rhs_code = getattr(conjecture_or_coeffs, "rhs_code", None)
    if rhs_code:
        try:
            return float(eval(rhs_code, {"np": np, "math": math, "min": min, "max": max}, {"props": props}))
        except Exception:
            pass

    coefficients: Dict[str, float] = conjecture_or_coeffs if isinstance(conjecture_or_coeffs, dict) else getattr(conjecture_or_coeffs, "coefficients", {}) or {}
    rhs = float(coefficients.get('const', 0.0))
    for key, coef in coefficients.items():
        if key == 'const':
            continue
        attr = 'sum_pk_after_p6' if key == 'sum_pk' else key
        rhs += float(coef) * float(props.get(attr, 0.0))
    return rhs


class AdaptiveNodeFeatureExtractor:
    def __init__(self, history_window=10):
        self.history_window = history_window
        self.node_history = defaultdict(lambda: deque(maxlen=history_window))
        self.node_counts = defaultdict(int)
        self.gap_history = defaultdict(lambda: deque(maxlen=history_window))
        self.creation_step: Dict[int, int] = {}
        self.current_step = 0

    def reset(self):
        self.node_history.clear()
        self.node_counts.clear()
        self.gap_history.clear()
        self.creation_step.clear()
        self.current_step = 0

    def bootstrap_from_graph(self, G: nx.Graph, step: int = 0) -> None:
        for node in G.nodes():
            self.creation_step.setdefault(node, step)

    def record_operation(self, nodes, step: int, gap_delta: float = 0.0):
        self.current_step = step
        target_nodes = nodes if isinstance(nodes, (list, tuple)) else [nodes]
        for node in target_nodes:
            self.creation_step.setdefault(node, step)
            self.node_history[node].append(step)
            self.node_counts[node] += 1
            self.gap_history[node].append(float(gap_delta))

    def compute_node_features(self, G, node, props, current_step: int):
        self.creation_step.setdefault(node, current_step)
        neighbors = list(G.neighbors(node))
        in_triangle = any(G.has_edge(neighbors[i], neighbors[j]) for i in range(len(neighbors)) for j in range(i + 1, len(neighbors)))

        ring_lengths = self._three_prism_cycle_lengths(G, node, neighbors)
        recent_ops = self.node_history[node]
        gaps = self.gap_history[node]
        avg_gap_delta = (sum(gaps) / len(gaps)) if gaps else 0.0
        last_gap_delta = gaps[-1] if gaps else 0.0
        positive_gap_frac = (sum(1 for g in gaps if g > 0) / len(gaps)) if gaps else 0.0
        age = current_step - self.creation_step.get(node, current_step)
        age_ratio = age / max(1, current_step)

        num_nodes = max(G.number_of_nodes(), 1)

        features = [
            1.0,
            num_nodes / 100.0,
            props.get('gap', 0) / 10.0,
            float(in_triangle),
            self.node_counts[node] / 10.0,
            1.0 if recent_ops and (current_step - recent_ops[-1]) < 5 else 0.0,
            len(recent_ops) / max(self.history_window, 1),
            min((current_step - recent_ops[-1]) / 50.0, 1.0) if recent_ops else 1.0,
            props.get('p3', 0) / num_nodes,
            props.get('p4', 0) / num_nodes,
            props.get('p5', 0) / num_nodes,
            props.get('p6', 0) / num_nodes,
            props.get('sum_pk_after_p6', 0) / 10.0,
            min(max(age_ratio, 0.0), 1.0),
            avg_gap_delta / 10.0,
            last_gap_delta / 10.0,
            positive_gap_frac,
            ring_lengths[0],
            ring_lengths[1],
            ring_lengths[2],
        ]
        return np.array(features, dtype=np.float32)

    def _three_prism_cycle_lengths(self, G: nx.Graph, node: int, neighbors: List[int]) -> Tuple[float, float, float]:
        if len(neighbors) < 3:
            return (0.0, 0.0, 0.0)
        lengths = []
        base_adj_list = set(G.neighbors(node))
        for i in range(3):
            u = neighbors[i]
            v = neighbors[(i + 1) % 3]
            path = self._shortest_path_avoiding(G, u, v, forbidden=node)
            if path is None:
                lengths.append(0.0)
            else:
                cycle_len = len(path) + 1
                lengths.append(float(cycle_len))
        return tuple(lengths[:3])

    def _shortest_path_avoiding(self, G: nx.Graph, src: int, dst: int, forbidden: int) -> Optional[List[int]]:
        try:
            H = G.copy()
            if H.has_node(forbidden):
                H.remove_node(forbidden)
            return nx.shortest_path(H, src, dst)
        except (nx.NetworkXNoPath, nx.NodeNotFound):
            return None


class FiLMGraphLayer(nn.Module):
    def __init__(self, in_dim: int, out_dim: int):
        super().__init__()
        self.linear = nn.Linear(in_dim, out_dim)
        self.norm = nn.LayerNorm(out_dim)

    def forward(self, x, adj, gamma, beta):
        support = self.linear(x)
        norm = adj / adj.sum(dim=1, keepdim=True).clamp(min=1)
        agg = torch.matmul(norm, support)
        transformed = agg * gamma + beta
        return F.relu(self.norm(transformed + support))


class ConditionalGraphPolicy(nn.Module):
    def __init__(self, node_dim=15, hidden_dim=128, global_dim=12, coefficient_dim=5, num_layers: int = 3):
        super().__init__()
        self.input_linear = nn.Linear(node_dim, hidden_dim)
        self.layers = nn.ModuleList([FiLMGraphLayer(hidden_dim, hidden_dim) for _ in range(num_layers)])
        cond_dim = global_dim + coefficient_dim
        self.film_generator = nn.ModuleList([
            nn.Linear(cond_dim, hidden_dim * 2) for _ in range(num_layers)
        ])
        self.node_head = nn.Linear(hidden_dim, 1)
        self.stop_head = nn.Sequential(
            nn.Linear(hidden_dim + cond_dim, hidden_dim),
            nn.ReLU(),
            nn.Linear(hidden_dim, 1),
        )
        self._reset_parameters()

    def _reset_parameters(self):
        nn.init.xavier_uniform_(self.input_linear.weight)
        nn.init.zeros_(self.input_linear.bias)
        for layer, film in zip(self.layers, self.film_generator):
            nn.init.xavier_uniform_(layer.linear.weight)
            nn.init.zeros_(layer.linear.bias)
            nn.init.xavier_uniform_(film.weight)
            nn.init.zeros_(film.bias)
        nn.init.xavier_uniform_(self.node_head.weight)
        nn.init.zeros_(self.node_head.bias)
        for m in self.stop_head:
            if isinstance(m, nn.Linear):
                nn.init.xavier_uniform_(m.weight)
                nn.init.zeros_(m.bias)

    def forward(self, node_features, adj_matrix, global_features, coefficients):
        dev = node_features.device
        cond = torch.cat([global_features, coefficients], dim=-1)
        h = F.relu(self.input_linear(node_features))
        for layer, film in zip(self.layers, self.film_generator):
            gamma_beta = film(cond)
            gamma, beta = gamma_beta.chunk(2, dim=-1)
            gamma = torch.sigmoid(gamma)
            beta = beta
            h = layer(h, adj_matrix, gamma, beta)

        node_logits = self.node_head(h).squeeze(-1)
        graph_repr = h.mean(dim=0)
        stop_logit = self.stop_head(torch.cat([graph_repr, cond], dim=-1)).squeeze(-1)
        logits = torch.cat([node_logits, stop_logit.unsqueeze(0)], dim=0)
        return logits


class AdaptiveCubicGraphEnv:
    """Simplified environment for conditional GNN policy (only node chop + stop actions)."""

    def __init__(self, conjecture_formula: ConjectureFormula, max_steps=100,
                 max_nodes_cap: Optional[int] = 128, end_on_caps: bool = True,
                 attempts_without_ce: int = 0):
        self.formula = conjecture_formula
        self.max_steps = max_steps
        self.max_nodes_cap = max_nodes_cap
        self.end_on_caps = end_on_caps
        self.attempts_without_ce = attempts_without_ce
        self.best_start_graph = None
        self.best_start_props = None
        self.best_start_gap = None
        self.node_extractor = AdaptiveNodeFeatureExtractor()
        self.condition_fn = eval(f"lambda G, props: {conjecture_formula.condition_code}")
        self.conjecture_fn = eval(f"lambda G, props: {conjecture_formula.conjecture_code}", {"np": np, "math": math, "min": min, "max": max})
        self.coefficient_vector = np.array([
            conjecture_formula.coefficients.get('p3', 0.0),
            conjecture_formula.coefficients.get('p4', 0.0),
            conjecture_formula.coefficients.get('p5', 0.0),
            conjecture_formula.coefficients.get('sum_pk', 0.0),
            (float(conjecture_formula.threshold) / 20.0) if conjecture_formula.threshold else 0.0
        ], dtype=np.float32)
        self.reset()

    def reset(self):
        self.G = nx.complete_graph(4)
        self.step_count = 0
        self.episode_reward = 0
        self.operation_history = []
        self.node_extractor.reset()

        target_thresh = float(self.formula.threshold) if self.formula.threshold else None
        # Only warm-start after enough failed tries to avoid overhead on fresh conjectures
        if target_thresh and self.attempts_without_ce >= 3:
            if self.best_start_graph is not None:
                self.G = self.best_start_graph.copy()
                self.props = copy.deepcopy(self.best_start_props)
                self.operation_history.append({
                    'step': 0,
                    'action': 'warm_start_best',
                    'gap': self.best_start_gap,
                    'threshold': target_thresh,
                })
            else:
                # Chop until the actual conjecture condition is satisfied (f2, p_k, etc.)
                warm_steps = 0
                for _ in range(50):
                    props = compute_graph_properties(self.G)
                    try:
                        cond_met = bool(self.condition_fn(self.G, props))
                    except Exception:
                        cond_met = False
                    if cond_met:
                        break
                    n = np.random.choice(list(self.G.nodes()))
                    try:
                        self.G, _, _ = chop_y_insert_triangle(self.G, n)
                        warm_steps += 1
                    except Exception:
                        break
                self.operation_history.append({
                    'step': 0,
                    'action': 'warm_start_random',
                    'warm_chops': warm_steps,
                    'threshold': target_thresh,
                })
        self.props = compute_graph_properties(self.G)
        self._update_props()
        self.node_extractor.bootstrap_from_graph(self.G, step=0)
        return self._get_observation()

    def _update_props(self):
        rhs = evaluate_rhs(self.formula, self.props)
        lhs = float(self.props.get('p6', 0))
        # margin positive ⇒ violation
        if getattr(self.formula, "relation", ">=") == ">=":
            margin = rhs - lhs  # need p6 to be at least rhs
            conj_ok = (lhs + 1e-3 >= rhs)
        else:
            margin = lhs - rhs  # need p6 to be at most rhs
            conj_ok = (lhs - 1e-3 <= rhs)
        eps = 1e-3

        try:
            self.satisfies_condition = bool(self.condition_fn(self.G, self.props))
        except Exception:
            self.satisfies_condition = False

        try:
            conj_eval = bool(self.conjecture_fn(self.G, self.props))
        except Exception:
            conj_eval = conj_ok

        # Accept conjecture if any of: raw eval true, or within tolerance.
        within_tol = (margin <= eps) or conj_ok
        self.satisfies_conjecture = bool(conj_eval) or within_tol
        self.is_counterexample = (self.props['is_polytope']
                                   and self.satisfies_condition
                                   and not self.satisfies_conjecture)

        self.props['rhs'] = rhs
        self.props['gap'] = margin
        self.props['conjecture_eval'] = conj_eval
        self.props['within_tol'] = within_tol

    def step(self, action_idx: int):
        nodes = sorted(self.G.nodes())
        total = len(nodes) + 1  # nodes + stop
        if action_idx >= total:
            action_idx = total - 1

        self.step_count += 1
        old_props = self.props.copy()

        if action_idx == len(nodes):
            # stop
            done = True
            reward = 100 if self.is_counterexample else (5 if self.satisfies_condition else -5)
            # Record stop action with current state for full trajectory trace.
            self.operation_history.append({
                'step': self.step_count,
                'action': 'stop',
                'properties': self.props.copy(),
                'stopped': True,
            })
        else:
            target = nodes[action_idx]
            try:
                self.G, new_nodes, neighbors = chop_y_insert_triangle(self.G, target)
                touched = list(new_nodes) + neighbors
                self.props = compute_graph_properties(self.G)
                self._update_props()
                gap_delta = float(self.props.get('gap', 0)) - float(old_props.get('gap', 0))
                self.node_extractor.record_operation(touched, step=self.step_count, gap_delta=gap_delta)
                self.operation_history.append({'step': self.step_count, 'properties': self.props.copy()})

                reward = self._compute_reward(old_props)
                done = self.step_count >= self.max_steps or self.is_counterexample

                if self.satisfies_condition:
                    gap_abs = abs(float(self.props.get('gap', 1e9)))
                    if (self.best_start_gap is None) or (gap_abs < self.best_start_gap):
                        self.best_start_gap = gap_abs
                        self.best_start_graph = self.G.copy()
                        self.best_start_props = self.props.copy()

                if not done and self.end_on_caps and self.max_nodes_cap and self.G.number_of_nodes() >= self.max_nodes_cap:
                    done = True
                    reward -= 5.0 if not self.is_counterexample else 0.0

                if self.is_counterexample:
                    reward += 100
            except Exception:
                reward, done = -10, True

        self.episode_reward += reward
        return self._get_observation(), reward, done, {
            'props': self.props,
            'satisfies_condition': self.satisfies_condition,
            'satisfies_conjecture': self.satisfies_conjecture,
            'is_counterexample': self.is_counterexample,
            'graph': nx.node_link_data(self.G, edges="links"),
            'operations': self.operation_history,
            'stopped': (action_idx == len(nodes)),
            'step': self.step_count,
        }

    def _compute_reward(self, old_props):
        # 条件距离 shaping：鼓励更快满足 if
        cond_margin_prev = float(old_props.get('cond_margin', 0))
        cond_margin_now = float(self.props.get('cond_margin', 0))

        reward = 2.0 if self.satisfies_condition else -1.0
        if self.satisfies_condition and not self.satisfies_conjecture:
            reward += 10.0

        for k, coef in self.formula.coefficients.items():
            if k == 'const':
                continue
            key = 'sum_pk_after_p6' if k == 'sum_pk' else k
            delta = self.props.get(key, 0) - old_props.get(key, 0)
            # Reward moves that push RHS higher (making p6 < RHS violation easier):
            # positive-coeff vars: increasing them raises RHS → reward delta > 0
            # negative-coeff vars: decreasing them raises RHS → reward delta < 0
            if (coef > 0 and delta > 0) or (coef < 0 and delta < 0):
                reward += 5.0 * abs(coef) * abs(delta)

        if self.props['is_polytope']:
            reward += 1.0

        if self.formula.threshold and self.props['sum_pk_after_p6'] >= self.formula.threshold:
            reward += 3.0

        if self.satisfies_condition:
            rhs_old = evaluate_rhs(self.formula, old_props)
            rhs_new = self.props.get('rhs', evaluate_rhs(self.formula, self.props))
            if getattr(self.formula, "relation", ">=") == ">=":
                m_old = rhs_old - float(old_props.get('p6', 0))
                m_new = rhs_new - float(self.props.get('p6', 0))
            else:
                m_old = float(old_props.get('p6', 0)) - rhs_old
                m_new = float(self.props.get('p6', 0)) - rhs_new
            reward += 2.0 * (max(m_new, 0) - max(m_old, 0)) + 0.5 * m_new

        # 直接奖励条件 margin 的改善（无论条件是否已满足）
        reward += 1.5 * (cond_margin_prev - cond_margin_now)

        return reward

    def _get_observation(self):
        nodes = sorted(self.G.nodes())
        node_features = np.array(
            [self.node_extractor.compute_node_features(self.G, n, self.props, self.step_count) for n in nodes],
            dtype=np.float32,
        )
        adj_matrix = nx.adjacency_matrix(self.G, nodelist=nodes).todense()

        global_features = np.array([
            self.props.get('gap', 0) / 10.0,
            self.props['num_vertices'] / 100.0,
            self.props['num_edges'] / 150.0,
            1.0 if self.props['is_polytope'] else 0.0,
            1.0 if self.satisfies_condition else 0.0,
            self.step_count / 100.0,
            self.props.get('p3', 0) / max(self.props['num_vertices'], 1),
            self.props.get('p4', 0) / 10.0,
            self.props.get('p5', 0) / 10.0,
            self.props.get('p6', 0) / 10.0,
            # Individual large-face counts (replaces single sum_pk_after_p6)
            self.props.get('p7', 0) / 5.0,
            self.props.get('p8', 0) / 5.0,
            self.props.get('p9', 0) / 3.0,
            self.props.get('p10', 0) / 3.0,
            self.props.get('p11plus', 0) / 3.0,
            self.episode_reward / 100.0,
        ], dtype=np.float32)

        num_actions = len(nodes) + 1
        valid_mask = np.ones(num_actions, dtype=np.float32)

        return {
            'node_features': torch.FloatTensor(node_features),
            'adj_matrix': torch.FloatTensor(adj_matrix),
            'global_features': torch.FloatTensor(global_features),
            'coefficients': torch.FloatTensor(self.coefficient_vector),
            'num_actions': num_actions,
            'valid_mask': torch.FloatTensor(valid_mask),
        }


class PPOAgent:
    def __init__(self, network, lr=3e-4, gamma=0.99, gae_lambda=0.95,
                 eps_clip=0.2, k_epochs=10, batch_size=64, update_steps=2048, entropy_coef=0.003):
        self.network = network.to(device)
        self.optimizer = optim.Adam(network.parameters(), lr=lr, eps=1e-5)
        self.gamma = gamma
        self.gae_lambda = gae_lambda
        self.eps_clip = eps_clip
        self.k_epochs = k_epochs
        self.batch_size = batch_size
        self.update_steps = update_steps
        self.entropy_coef = entropy_coef
        self.buffer = defaultdict(list)
        self.scheduler = optim.lr_scheduler.LambdaLR(self.optimizer, lambda step: 1 - step / 10000, last_epoch=-1)

    def select_action(self, obs):
        with torch.no_grad():
            logits = self.network(
                obs['node_features'].to(device),
                obs['adj_matrix'].to(device),
                obs['global_features'].to(device),
                obs['coefficients'].to(device),
            )
            num_actions = obs['num_actions']
            if logits.shape[0] != num_actions:
                logits = torch.cat([logits, logits.new_zeros(num_actions - logits.shape[0])], dim=0)[:num_actions]
            masked_logits = logits.clone()
            masked_logits[obs['valid_mask'].to(device) == 0] = -1e10
            probs = F.softmax(masked_logits, dim=-1)
            dist = Categorical(probs)
            action = dist.sample()
            stop_prob = probs[-1].item()
            entropy = dist.entropy().item()
            return action.item(), dist.log_prob(action).item(), masked_logits[action].item(), stop_prob, entropy

    def store(self, obs, action, reward, logit, log_prob, done):
        self.buffer['obs'].append(obs)
        self.buffer['actions'].append(action)
        self.buffer['rewards'].append(reward)
        self.buffer['logits'].append(logit)
        self.buffer['log_probs'].append(log_prob)
        self.buffer['dones'].append(done)

    def update(self):
        if len(self.buffer['rewards']) < self.update_steps:
            return

        rewards = np.array(self.buffer['rewards'][:self.update_steps], dtype=np.float32)
        dones = np.array(self.buffer['dones'][:self.update_steps], dtype=np.float32)

        returns = []
        discounted = 0.0
        for r, d in zip(reversed(rewards), reversed(dones)):
            discounted = r + self.gamma * discounted * (1 - d)
            returns.insert(0, discounted)
        returns = torch.FloatTensor(returns).to(device)
        advantages = returns - returns.mean()
        advantages /= (advantages.std() + 1e-8)

        old_log_probs = torch.FloatTensor(self.buffer['log_probs'][:self.update_steps]).to(device)
        actions = torch.LongTensor(self.buffer['actions'][:self.update_steps]).to(device)

        obs_batch = self.buffer['obs'][:self.update_steps]

        for _ in range(self.k_epochs):
            indices = torch.randperm(self.update_steps)
            for start in range(0, self.update_steps, self.batch_size):
                batch_idx = indices[start:start + self.batch_size]
                batch_loss = 0.0
                for idx in batch_idx:
                    ob = obs_batch[idx]
                    logits = self.network(
                        ob['node_features'].to(device),
                        ob['adj_matrix'].to(device),
                        ob['global_features'].to(device),
                        ob['coefficients'].to(device),
                    )
                    num_actions = ob['num_actions']
                    if logits.shape[0] != num_actions:
                        logits = torch.cat([logits, logits.new_zeros(num_actions - logits.shape[0])], dim=0)[:num_actions]
                    masked_logits = logits.clone()
                    masked_logits[ob['valid_mask'].to(device) == 0] = -1e10
                    probs = F.softmax(masked_logits, dim=-1)
                    dist = Categorical(probs)
                    new_log_prob = dist.log_prob(actions[idx])
                    ratio = torch.exp(new_log_prob - old_log_probs[idx])
                    surr1 = ratio * advantages[idx]
                    surr2 = torch.clamp(ratio, 1 - self.eps_clip, 1 + self.eps_clip) * advantages[idx]
                    entropy = dist.entropy()
                    loss = -torch.min(surr1, surr2) - self.entropy_coef * entropy
                    batch_loss += loss
                self.optimizer.zero_grad()
                batch_loss.backward()
                torch.nn.utils.clip_grad_norm_(self.network.parameters(), 0.5)
                self.optimizer.step()

        for key in list(self.buffer.keys()):
            self.buffer[key] = self.buffer[key][self.update_steps:]
        self.scheduler.step()


def plot_metrics(
    result_path: str,
    episodes: List[int],
    rewards: List[float],
    best_gaps: List[Optional[float]],
    stop_probs: List[float],
    entropies: List[float],
    ce_rates: List[float],
) -> None:
    if not episodes:
        return
    os.makedirs(result_path, exist_ok=True)
    xs = episodes

    fig, ax = plt.subplots(figsize=(8, 4.5))
    ax.plot(xs, rewards, label="Episode reward", color="#1f77b4")
    ax.set_xlabel("Episode")
    ax.set_ylabel("Reward")
    ax.set_title("Episode Reward")
    ax.grid(True, alpha=0.3)
    ax.legend()
    fig.tight_layout()
    fig.savefig(os.path.join(result_path, "reward_curve.png"))
    plt.close(fig)

    if best_gaps:
        gaps = [float(g) if isinstance(g, (int, float)) else float("nan") for g in best_gaps]
        fig, ax = plt.subplots(figsize=(8, 4.5))
        ax.plot(xs, gaps, label="Best gap per episode", color="#d62728")
        ax.set_xlabel("Episode")
        ax.set_ylabel("Gap (rhs - p6)")
        ax.set_title("Best Gap per Episode")
        ax.grid(True, alpha=0.3)
        ax.legend()
        fig.tight_layout()
        fig.savefig(os.path.join(result_path, "best_gap_curve.png"))
        plt.close(fig)

    if stop_probs:
        fig, ax = plt.subplots(figsize=(8, 4.5))
        ax.plot(xs[: len(stop_probs)], stop_probs, label="Avg stop probability", color="#2ca02c")
        ax.set_xlabel("Episode")
        ax.set_ylabel("Probability")
        ax.set_title("Stop Head Probability")
        ax.grid(True, alpha=0.3)
        ax.legend()
        fig.tight_layout()
        fig.savefig(os.path.join(result_path, "stop_probability_curve.png"))
        plt.close(fig)

    if entropies:
        fig, ax = plt.subplots(figsize=(8, 4.5))
        ax.plot(xs[: len(entropies)], entropies, label="Policy entropy", color="#ff7f0e")
        ax.set_xlabel("Episode")
        ax.set_ylabel("Entropy")
        ax.set_title("Policy Entropy")
        ax.grid(True, alpha=0.3)
        ax.legend()
        fig.tight_layout()
        fig.savefig(os.path.join(result_path, "entropy_curve.png"))
        plt.close(fig)

    if ce_rates:
        fig, ax = plt.subplots(figsize=(8, 4.5))
        ax.plot(xs[: len(ce_rates)], ce_rates, label="Cumulative CE rate", color="#9467bd")
        ax.set_xlabel("Episode")
        ax.set_ylabel("CE rate")
        ax.set_title("Cumulative Counterexample Rate")
        ax.grid(True, alpha=0.3)
        ax.legend()
        fig.tight_layout()
        fig.savefig(os.path.join(result_path, "ce_rate_curve.png"))
        plt.close(fig)


def train_on_conjecture(formula: str, name: str = None, num_episodes: int = 5000,
                        max_nodes_cap: int = 128, end_on_caps: bool = True,
                        exit_on_first_ce: bool = False, update_steps: int = 512,
                        attempts_without_ce: int = 0, status_file: str = None):
    import time
    start_time = time.time()  
    ce_found_time: float = 0.0  # elapsed seconds when first CE was found
    
    # Normalise -(p6) >= -(rhs) -> p6 <= rhs before parsing
    def _strip_balanced_parens(s: str) -> str:
        s = s.strip()
        if not (s.startswith('(') and s.endswith(')')):
            return s
        depth = 0
        for i, ch in enumerate(s):
            if ch == '(': depth += 1
            elif ch == ')':
                depth -= 1
                if depth == 0:
                    return s[1:-1].strip() if i == len(s) - 1 else s
        return s

    def _strip_outer_neg(s: str) -> str:
        s = s.strip()
        unwrapped = _strip_balanced_parens(s)
        if unwrapped != s:
            return _strip_outer_neg(unwrapped)
        m_neg = re.match(r'^\-\s*\((.+)\)\s*$', s, re.DOTALL)
        if m_neg:
            return m_neg.group(1).strip()
        if s.startswith('-'):
            return s[1:].strip()
        return s

    _no_space = formula.replace(" ", "")
    # Match both -(p6) and -(props.get('p6', 0)) forms
    _negated_lhs = (
        ("then-(p6)>=" in _no_space and "then(-p6)>=" not in _no_space) or
        ("then-(props.get('p6" in _no_space) or
        re.search(r"then\s*-\s*\(props\.get", formula, re.IGNORECASE) is not None
    )
    if _negated_lhs:
        _lower_f = formula.strip().lower()
        _then_idx = _lower_f.rfind(", then")
        if _then_idx != -1:
            _cond_part  = formula.strip()[:_then_idx]
            _conclusion = formula.strip()[_then_idx + len(", then"):].strip()
            # Use .+? so commas inside props.get('p6', 0) don't break the match
            _m = re.match(r'-\s*\((.+?)\)\s*>=\s*(.+)$', _conclusion, re.DOTALL | re.IGNORECASE)
            if _m and re.search(r'p6', _m.group(1), re.IGNORECASE):
                _rhs_inner = _strip_outer_neg(_m.group(2).strip())
                formula = f"{_cond_part}, then p6 <= ({_rhs_inner})"

    parser = AdvancedConjectureParser()
    conj_formula = parser.parse_formula_with_coefficients(formula)

    env = AdaptiveCubicGraphEnv(
        conj_formula,
        max_steps=100,
        max_nodes_cap=max_nodes_cap,
        end_on_caps=end_on_caps,
        attempts_without_ce=attempts_without_ce,
    )
    global_dim = 16
    coeff_dim = 5
    node_dim = env._get_observation()['node_features'].shape[1]
    network = ConditionalGraphPolicy(node_dim=node_dim, global_dim=global_dim, coefficient_dim=coeff_dim)
    network = network.to(device)
    agent = PPOAgent(network, lr=3e-4, update_steps=update_steps)

    counterexamples, episode_rewards, gaps, ep_lens = [], [], [], []
    best_gaps_per_episode: List[Optional[float]] = []
    stop_probs_history: List[float] = []
    entropy_history: List[float] = []
    ce_rate_history: List[float] = []
    trajectories: List[List[dict]] = []  # store full operation histories per episode (including stop)
    stop0_count, ce_count, cond_margins = 0, 0, []
    episode_indices = list(range(num_episodes))
    cumulative_ce = 0
    total_operations = 0  

    print(f"[rl agent] Round 1/{num_episodes} ...")

    for episode in range(num_episodes):
        obs = env.reset()
        done = False
        best_gap_episode = float("-inf")
        episode_stop_probs: List[float] = []
        episode_entropies: List[float] = []
        ce_found_this_episode = False
        while not done:
            action, log_prob, logit, stop_prob, entropy = agent.select_action(obs)
            next_obs, reward, done, info = env.step(action)
            agent.store(obs, action, reward, logit, log_prob, done)
            obs = next_obs
            episode_stop_probs.append(stop_prob)
            episode_entropies.append(entropy)
            gap_val = info.get('props', {}).get('gap')
            if isinstance(gap_val, (int, float)):
                best_gap_episode = max(best_gap_episode, float(gap_val))

        episode_rewards.append(env.episode_reward)
        gaps.append(env.props.get('gap', -100))
        ep_lens.append(env.step_count)
        total_operations += env.step_count

        if status_file:
            try:
                with open(status_file, 'w') as _sf:
                    json.dump({"conjecture": name or formula[:40], "episode": episode + 1, "total_episodes": num_episodes, "ce_count": ce_count}, _sf)
            except Exception:
                pass
        
        if info.get('stopped') and info.get('step') == 1:
            stop0_count += 1
        if info.get('is_counterexample'):
            ce_count += 1
            ce_found_this_episode = True
        if info.get('satisfies_condition') and isinstance(env.props.get('gap'), (int, float)):
            cond_margins.append(float(env.props['gap']))
        best_gaps_per_episode.append(best_gap_episode if best_gap_episode != float("-inf") else None)
        if episode_stop_probs:
            stop_probs_history.append(float(np.mean(episode_stop_probs)))
        if episode_entropies:
            entropy_history.append(float(np.mean(episode_entropies)))
        cumulative_ce += 1 if ce_found_this_episode else 0
        ce_rate_history.append(cumulative_ce / float(episode + 1))

        if env.is_counterexample:
            rhs = evaluate_rhs(conj_formula, env.props)
            p6_val = float(env.props.get('p6', 0))
            if conj_formula.relation == ">=":
                # Positive margin means RHS still larger than p6 (violation for lower-bound form).
                margin = rhs - p6_val
            else:  # "<=" upper-bound conjecture
                # Positive margin means p6 exceeds RHS (violation for upper-bound form).
                margin = p6_val - rhs
            ce_info = {
                'episode': episode,
                'gap': env.props.get('gap', 0),
                'p_vector': env.props['p_vector'],
                'vertices': env.props['num_vertices'],
                'properties': env.props.copy(),
                'operations': env.operation_history,
                'graph': nx.node_link_data(env.G, edges="links"),
                'coefficients': conj_formula.coefficients,
                'relation': conj_formula.relation,
                'threshold': conj_formula.threshold,
                'rhs': rhs,
                'margin': margin,
                'formula_text': formula,
                'conjecture_name': name or 'Formula',
                'found_at': datetime.now().isoformat(timespec='seconds'),
            }
            # Only append if this p_vector is new (deduplicate by p_vector)
            _seen_pvecs = {str(c['p_vector']) for c in counterexamples}
            if str(env.props['p_vector']) not in _seen_pvecs:
                counterexamples.append(ce_info)

            print(f"\n*** CE #{len(counterexamples)} | Ep {episode} | V={env.props['num_vertices']} ***")
            print(f"p3={env.props['p3']}, p4={env.props['p4']}, p5={env.props['p5']}, p6={env.props['p6']}, sum_pk>6={env.props['sum_pk_after_p6']}")
            print(f"rhs={rhs:.6f}, margin={margin:.6f}\n")

            if len(counterexamples) == 1:  # record time of first CE
                ce_found_time = time.time() - start_time
            if exit_on_first_ce:
                print("Stopping early after first counterexample (exit_on_first_ce).")
                break

        if len(agent.buffer['rewards']) >= agent.update_steps:
            agent.update()

        # Persist full trajectory for this episode
        trajectories.append(list(env.operation_history))

        if episode % 100 == 0 and episode > 0:
            r_avg = np.mean(episode_rewards[-100:])
            len_avg = np.mean(ep_lens[-100:])
            max_gap = max(gaps[-100:]) if gaps else -100
            print(f"Ep {episode:4d} | R:{r_avg:6.2f} | Len:{len_avg:5.1f} | Stop0:{stop0_count/max(1,len(ep_lens)):5.2%} | CE:{ce_count/max(1,len(ep_lens)):5.2%} | Gap:{max_gap:7.3f}")

    total_time = time.time() - start_time
    
    actual_episodes = len(episode_rewards)
    avg_ops_per_episode = total_operations / actual_episodes if actual_episodes > 0 else 0.0
    avg_time_per_episode = total_time / actual_episodes if actual_episodes > 0 else 0.0
    final_lr = agent.optimizer.param_groups[0]["lr"]

    return {
        'name': name or 'Formula',
        'formula': formula,
        'relation': conj_formula.relation,
        'coefficients': conj_formula.coefficients,
        'counterexamples': counterexamples,
        'episode_rewards': episode_rewards,
        'gaps': gaps,
        'best_gaps': best_gaps_per_episode,
        'episode_indices': episode_indices,
        'stop_probs': stop_probs_history,
        'entropies': entropy_history,
        'ce_rates': ce_rate_history,
        'trajectories': trajectories,
        'metrics': {
            'episodes': num_episodes,
            'total_reward': float(sum(episode_rewards)) if episode_rewards else 0.0,
            'avg_len': float(np.mean(ep_lens)) if ep_lens else 0.0,
            'stop0_rate': float(stop0_count / max(1, len(ep_lens))),
            'number_of_ce': ce_count,
            'ce_rate': float(ce_count / num_episodes),
            'avg_stop_prob': float(np.mean(stop_probs_history)) if stop_probs_history else 0.0,
            'avg_entropy': float(np.mean(entropy_history)) if entropy_history else 0.0,
            'cond_margin_mean': float(np.mean(cond_margins)) if cond_margins else float('nan'),
        },
        'total_ops': total_operations,
        'avg_ops_per_ep': avg_ops_per_episode,
        'avg_time_per_ep': avg_time_per_episode,
        'total_training_time': total_time,  
        'ce_found_time': ce_found_time if ce_found_time > 0 else None,
        "final_lr": final_lr,
    }


if __name__ == "__main__":
    import argparse

    np.random.seed(42)
    torch.manual_seed(42)
    if torch.cuda.is_available():
        torch.cuda.manual_seed(42)

    ap = argparse.ArgumentParser(description="Counterexample agent (built-in PPO)")
    ap.add_argument("--mode", choices=["train", "test"], default="test", help="train: single formula; test: built-in test formula")
    ap.add_argument("--episodes", type=int, default=600, help="Episodes per conjecture/run")
    ap.add_argument("--max-nodes", type=int, default=128, help="Maximum nodes cap inside the environment")
    ap.add_argument("--no-end-on-caps", action="store_true", help="Keep running when caps are reached (mask only)")
    ap.add_argument("--results-dir", default=None, help="Override output directory for test runs")
    ap.add_argument("--formula", default=None, help="Formula for --mode train (if (...), then p6 >= (...))")
    ap.add_argument("--name", default=None, help="Optional name for --mode train")
    ap.add_argument("--run-full-episodes", dest="exit_on_first_ce", action="store_false",
                    help="Disable early stop; run all episodes even after first CE (default: exit on first CE)")
    ap.set_defaults(exit_on_first_ce=False)
    ap.add_argument("--update-steps", type=int, default=512, help="PPO update_steps (buffer size before each update)")
    args = ap.parse_args()

    end_on_caps = not args.no_end_on_caps

    if args.mode == "test":
        test_formula = "if (sum_pk_k>=7 >= 10), then p6 >= (-1/4*p3 - 1/8*p4 - 1/12*p5 + 1/3*sum_pk_k>=7)"
        print("[test] Running counterexample search on test formula...")
        res = train_on_conjecture(
            test_formula,
            name="test_formula",
            num_episodes=args.episodes,
            max_nodes_cap=args.max_nodes,
            end_on_caps=end_on_caps,
            exit_on_first_ce=args.exit_on_first_ce,
            update_steps=args.update_steps,
        )
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        out_dir = args.results_dir or f"results/gpn_test_{timestamp}"
        os.makedirs(out_dir, exist_ok=True)
        with open(os.path.join(out_dir, "summary.json"), "w") as fh:
            json.dump(
                {
                    "formula": res["formula"],
                    "coefficients": res["coefficients"],
                    "episodes": len(res["episode_rewards"]),
                    "num_counterexamples": len(res["counterexamples"]),
                    "max_gap": max(res["gaps"]) if res["gaps"] else 0,
                    "metrics": res.get("metrics", {}),
                    "total_time": res.get("total_training_time"),
                    "mean_ops":   res.get("avg_ops_per_ep"),
                },
                fh,
                indent=2,
            )
        plot_metrics(
            out_dir,
            res.get("episode_indices", list(range(len(res.get("episode_rewards", []))))),
            res.get("episode_rewards", []),
            res.get("best_gaps", []),
            res.get("stop_probs", []),
            res.get("entropies", []),
            res.get("ce_rates", []),
        )
        # Save trajectories for test mode as well
        traj_path = os.path.join(out_dir, "trajectories.jsonl")
        with open(traj_path, "w") as tf:
            for ep_idx, ops in enumerate(res.get("trajectories", [])):
                tf.write(json.dumps({"episode": ep_idx, "operations": ops}, separators=(",", ":")) + "\n")
        if res["counterexamples"]:
            ce_dir = os.path.join(out_dir, "counterexamples")
            os.makedirs(ce_dir, exist_ok=True)
            for i, ce in enumerate(res["counterexamples"]):
                ce_path = os.path.join(ce_dir, f"ce_{i}")
                os.makedirs(ce_path, exist_ok=True)
                with open(os.path.join(ce_path, "info.json"), "w") as fh:
                    json.dump(
                        {k: ce.get(k) for k in ["episode", "properties", "coefficients", "rhs", "margin"]},
                        fh,
                        indent=2,
                    )
                nx.write_edgelist(nx.node_link_graph(ce["graph"], edges="links"), os.path.join(ce_path, "graph.edgelist"))
        print(f"[test] Outputs saved to {out_dir}")
    elif args.mode == "train":
        if not args.formula:
            ap.error("--formula is required for --mode train")
        res = train_on_conjecture(
            args.formula,
            name=args.name,
            num_episodes=args.episodes,
            max_nodes_cap=args.max_nodes,
            end_on_caps=end_on_caps,
            exit_on_first_ce=args.exit_on_first_ce,
            update_steps=args.update_steps,
        )
        print(f"[train] Finished {len(res['episode_rewards'])} episodes; counterexamples found: {len(res['counterexamples'])}")