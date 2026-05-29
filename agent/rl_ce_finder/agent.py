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
from agent.conjectures import (
    load_conjectures,
    ConjectureSpec,
    ConjectureFormula,
    AdvancedConjectureParser,
    load_registry,
    save_registry,
    ensure_registry_for_specs,
    mark_conjecture_status,
    mark_conjecture_as_solved,
    record_ce_found,
    increment_attempt,
    sync_registry_from_ce_map,
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
        'p3': p_vec[0] if len(p_vec) > 0 else 0,
        'p4': p_vec[1] if len(p_vec) > 1 else 0,
        'p5': p_vec[2] if len(p_vec) > 2 else 0,
        'p6': p_vec[3] if len(p_vec) > 3 else 0,
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
        self._reset_count = 0
        # Extract f2 lower-bound from condition_code (e.g. "sum(props.get('p_vector', [])) >= 19")
        import re as _re
        _f2m = _re.search(r'sum\(props\.get\(.p_vector[^)]*\)[^)]*\)\s*>=\s*(\d+)', conjecture_formula.condition_code)
        self._f2_min = int(_f2m.group(1)) if _f2m else None
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
        self._reset_count += 1
        self.step_count = 0
        self.episode_reward = 0
        self.operation_history = []
        self.node_extractor.reset()

        # Intra-run warm-start: after episode 5, reuse best-gap graph 50% of the time.
        # This avoids re-spending steps just satisfying the hypothesis every episode.
        if self._reset_count > 5 and self.best_start_graph is not None and np.random.random() < 0.5:
            self.G = self.best_start_graph.copy()
            self.operation_history.append({
                'step': 0,
                'action': 'warm_start_best',
                'gap': self.best_start_gap,
            })
        else:
            self.G = nx.complete_graph(4)
            # Pre-expand to satisfy f2 lower-bound so steps aren't wasted on
            # growing the graph just to meet the hypothesis.
            if self._f2_min and self._f2_min > 4:
                needed = self._f2_min - 4
                for _ in range(needed):
                    try:
                        n = np.random.choice(list(self.G.nodes()))
                        self.G, _, _ = chop_y_insert_triangle(self.G, n)
                    except Exception:
                        break
            target_thresh = float(self.formula.threshold) if self.formula.threshold else None
            target_var = "sum_pk_after_p6"
            if target_thresh and self.attempts_without_ce >= 3:
                warm_steps = 0
                for _ in range(30):
                    props = compute_graph_properties(self.G)
                    cur = props.get(target_var, 0)
                    if cur >= max(0.8 * target_thresh, target_thresh - 2):
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
                    'target_var': target_var,
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
        self.is_counterexample = self.satisfies_condition and not self.satisfies_conjecture

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
            if (coef < 0 and delta > 0) or (coef > 0 and delta < 0):
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
            self.props.get('sum_pk_after_p6', 0) / 10.0,
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
                        attempts_without_ce: int = 0, status_file: str = None,
                        stop_event=None):
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

    print(f"[rl ce finding] Episode 1/{num_episodes}")

    env = AdaptiveCubicGraphEnv(
        conj_formula,
        max_steps=100,
        max_nodes_cap=max_nodes_cap,
        end_on_caps=end_on_caps,
        attempts_without_ce=attempts_without_ce,
    )
    global_dim = 12
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

    for episode in range(num_episodes):
        if stop_event is not None and stop_event.is_set():
            break
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

            if len(counterexamples) == 1:
                ce_found_time = time.time() - start_time

            _ce_out_dir = Path(__file__).resolve().parents[1] / "output" / "conjecture_with_ce"
            _ce_out_dir.mkdir(parents=True, exist_ok=True)
            _ce_out_file = _ce_out_dir / f"{name or 'formula'}.json"
            _ce_record = {
                "name": name or "formula",
                "formula": formula,
                "counterexamples": [
                    {
                        "p_vector": c["p_vector"],
                        "p3": c["properties"].get("p3"),
                        "p4": c["properties"].get("p4"),
                        "p5": c["properties"].get("p5"),
                        "p6": c["properties"].get("p6"),
                        "sum_pk_after_p6": c["properties"].get("sum_pk_after_p6"),
                        "vertices": c["properties"].get("num_vertices"),
                        "episode": c["episode"],
                        "margin": c["margin"],
                    }
                    for c in counterexamples
                ],
            }
            with open(_ce_out_file, "w") as _f:
                json.dump(_ce_record, _f, indent=2)

            print(f"[rl ce finding] Episode {episode} ce found! p_vector={env.props['p_vector']}")
            if stop_event is not None and not stop_event.is_set():
                stop_event.set()
            break

        if len(agent.buffer['rewards']) >= agent.update_steps:
            agent.update()

        # Persist full trajectory for this episode
        trajectories.append(list(env.operation_history))

        if episode % 100 == 0 and episode > 0:
            r_avg = np.mean(episode_rewards[-100:])
            len_avg = np.mean(ep_lens[-100:])
            max_gap = max(gaps[-100:]) if gaps else -100
            print(f"[rl ce finding] Episode {episode} | R:{r_avg:6.2f} | Len:{len_avg:5.1f} | Stop0:{stop0_count/max(1,len(ep_lens)):5.2%} | CE:{ce_count/max(1,len(ep_lens)):5.2%} | Gap:{max_gap:7.3f}")

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


def run_loaded_conjectures(source: Optional[str] = None, episodes: int = 2000,
                           max_nodes_cap: int = 128, end_on_caps: bool = True,
                           target_names: Optional[List[str]] = None,
                           exit_on_first_ce: bool = True, update_steps: int = 512,
                           iris_sort: str = "TRL"):
    specs = load_conjectures(source)
    source_dir = source if source and os.path.isdir(source) else (os.path.dirname(str(source)) if source else None)
    reg = ensure_registry_for_specs(specs, load_registry(source_dir))
    reg = sync_registry_from_ce_map(reg)

    # Extract IRIS scores from registry (written there by conjecture_agent)
    iris_scores: Dict[str, Dict] = {}
    for spec_name, rec in reg.items():
        if isinstance(rec, dict):
            iris = rec.get("metrics", {}).get("iris")
            if iris and isinstance(iris, dict):
                iris_scores[spec_name] = iris

    name_to_spec = {s.name: s for s in specs}
    if target_names:
        ordered_targets = [n for n in target_names if n in name_to_spec]
        work_specs = [
            name_to_spec[n] for n in ordered_targets
            if reg.get(n, {}).get('status', 'unsolved') == 'unsolved'
        ]
        if not work_specs:
            work_specs = [name_to_spec[n] for n in ordered_targets]
    else:
        work_specs = [name_to_spec[n] for n in reg if n in name_to_spec and reg[n].get('status') == 'unsolved']

    _IRIS_SORT_LABEL = iris_sort.upper()
    def _iris_sort_key(spec):
        iris = iris_scores.get(spec.name) or {}
        T = iris.get('T', 0.0) or 0.0
        R = iris.get('R', 0.0) or 0.0
        L = iris.get('L', 0.0) or 0.0
        mapping = {
            'T':   T,
            'R':   R,
            'L':   L,
            'TR':  T * R,
            'TL':  T * L,
            'RL':  R * L,
            'TRL': T * R * L,
        }
        return mapping.get(_IRIS_SORT_LABEL, T * R * L)

    work_specs.sort(key=_iris_sort_key, reverse=True)

    if not work_specs:
        work_specs = [
            ConjectureSpec("conj_1", "if (sum_pk_k>=7 >= 10), then p6 >= (-1/4*p3 - 1/8*p4 - 1/12*p5 + 1/3*sum_pk_k>=7)"),
            ConjectureSpec("conj_2", "if (sum_pk_k>=7 >= 10), then p6 >= (-1/4*p3 - 1/4*p4 - 1/9*p5 + 1/3*sum_pk_k>=7)"),
        ]

    # Always place results under the project root/rl_agent/results
    # Use a stable directory name (no timestamp) so restarts reuse the same folder
    repo_root = Path(__file__).resolve().parents[1]
    results_dir = repo_root / "results" / f"gpn_ce_ablation_{iris_sort}"
    results_dir.mkdir(parents=True, exist_ok=True)

    # ── Checkpoint: load already-completed conjectures ────────────────────────
    _checkpoint_file = results_dir / "checkpoint.json"
    _checkpoint: dict = {}
    if _checkpoint_file.exists():
        try:
            _checkpoint = json.load(open(_checkpoint_file))
            print(f"[resume] Loaded checkpoint: {len(_checkpoint)} conjectures already done.")
        except Exception as _ce:
            print(f"[resume] Warning: could not load checkpoint ({_ce}), starting fresh.")
            _checkpoint = {}

    def _save_checkpoint(name: str, res: dict):
        """Save one conjecture result to checkpoint immediately after it finishes."""
        # Store only the fields needed to reconstruct results_list and ablation data
        _checkpoint[name] = {
            "formula":           res.get("formula", ""),
            "coefficients":      res.get("coefficients", {}),
            "episodes":          len(res.get("episode_rewards", [])),
            "num_counterexamples": len(res.get("counterexamples", [])),
            "max_gap":           max(res["gaps"]) if res.get("gaps") else 0,
            "metrics":           res.get("metrics", {}),
            "total_ops":         res.get("total_ops"),
            "avg_ops_per_ep":    res.get("avg_ops_per_ep"),
            "total_training_time": res.get("total_training_time"),
            "avg_time_per_ep":   res.get("avg_time_per_ep"),
            "final_lr":          res.get("final_lr"),
            "episode_rewards":   res.get("episode_rewards", []),
            "best_gaps":         res.get("best_gaps", []),
            "stop_probs":        res.get("stop_probs", []),
            "entropies":         res.get("entropies", []),
            "ce_rates":          res.get("ce_rates", []),
            "counterexamples":   [
                {k: v for k, v in ce.items() if k != "graph"}
                for ce in res.get("counterexamples", [])
            ],
        }
        try:
            # Atomic write: write to temp file then rename to avoid corrupt checkpoint
            _tmp_ckpt = _checkpoint_file.with_suffix(".tmp")
            with open(_tmp_ckpt, "w") as _cf:
                json.dump(_checkpoint, _cf)
            _tmp_ckpt.replace(_checkpoint_file)
        except Exception as _ce:
            print(f"[resume] Warning: failed to save checkpoint ({_ce})")

    print(f"Training on {len(work_specs)} conjectures | Device: {device} | Output: {results_dir}\n")

    def _is_trivial_nonneg(formula: str) -> bool:
        # fast substring check for trivial lower bound p6 >= 0
        f = formula.replace(" ", "")
        return "thenp6>=(0)" in f

    def _save_conjecture_outputs(name: str, res: dict):
        """Write all files for one conjecture right after it finishes."""
        _has_ce = len(res.get('counterexamples', [])) > 0
        _group  = "conjectures_with_ces" if _has_ce else "conjectures_without_ces"
        result_path = results_dir / _group / name
        result_path.mkdir(parents=True, exist_ok=True)

        _ce_list = res.get('counterexamples', [])
        _ce_pvec = None
        if _ce_list:
            _ce_pvec = [
                {
                    'p_vector':        str(ce.get('p_vector') or ce.get('properties', {}).get('p_vector', '')),
                    'p3':              ce.get('properties', {}).get('p3', ''),
                    'p4':              ce.get('properties', {}).get('p4', ''),
                    'p5':              ce.get('properties', {}).get('p5', ''),
                    'p6':              ce.get('properties', {}).get('p6', ''),
                    'sum_pk_after_p6': ce.get('properties', {}).get('sum_pk_after_p6', ''),
                    'episode':         ce.get('episode', ''),
                    'gap':             ce.get('gap', ''),
                    'margin':          ce.get('margin', ''),
                }
                for ce in _ce_list
            ]

        with open(result_path / 'summary.json', 'w') as f:
            json.dump({
                'formula': res['formula'],
                'coefficients': res['coefficients'],
                'episodes': len(res['episode_rewards']),
                'num_counterexamples': len(res['counterexamples']),
                'max_gap': max(res['gaps']) if res['gaps'] else 0,
                'counterexamples': _ce_pvec,
                'metrics': res.get('metrics', {}),
                'total_ops': res.get('total_ops'),
                'avg_ops_per_ep': res.get('avg_ops_per_ep'),
                'total_training_time': res.get('total_training_time'),
                'avg_time_per_ep': res.get('avg_time_per_ep'),
                'final_lr': res.get('final_lr'),
                'iris': {k: v for k, v in (iris_scores.get(name) or {}).items() if k not in ('name', 'formula')},
            }, f, indent=2)

        traj_path = result_path / 'trajectories.jsonl'
        with open(traj_path, 'w') as tf:
            for ep_idx, ops in enumerate(res.get('trajectories', [])):
                tf.write(json.dumps({'episode': ep_idx, 'operations': ops}, separators=(",", ":")) + "\n")

        if res['counterexamples']:
            ce_dir = result_path / 'counterexamples'
            ce_dir.mkdir(parents=True, exist_ok=True)
            for i, ce in enumerate(res['counterexamples']):
                ce_path = os.path.join(ce_dir, f'ce_{i}')
                os.makedirs(ce_path, exist_ok=True)
                _G = nx.node_link_graph(ce['graph'], edges="links")
                nx.write_edgelist(_G, os.path.join(ce_path, 'graph.edgelist'))
                import pandas as pd
                _nodes = sorted(_G.nodes())
                _adj = nx.to_numpy_array(_G, nodelist=_nodes)
                _adj_df = pd.DataFrame(_adj.astype(int), index=_nodes, columns=_nodes)
                _adj_df.to_csv(os.path.join(ce_path, 'adjacency_matrix.csv'))
                _adj_list = _adj.astype(int).tolist()
                with open(os.path.join(ce_path, 'adjacency_matrix.json'), 'w') as _adj_fh:
                    json.dump({"nodes": _nodes, "adjacency_matrix": _adj_list}, _adj_fh)
                _ce_props = ce.get('properties', {})
                with open(os.path.join(ce_path, 'p_vector.json'), 'w') as _pv_fh:
                    json.dump({
                        'p_vector':        ce.get('p_vector', _ce_props.get('p_vector', [])),
                        'p3':              _ce_props.get('p3', ''),
                        'p4':              _ce_props.get('p4', ''),
                        'p5':              _ce_props.get('p5', ''),
                        'p6':              _ce_props.get('p6', ''),
                        'sum_pk_after_p6': _ce_props.get('sum_pk_after_p6', ''),
                        'num_vertices':    _ce_props.get('num_vertices', ''),
                        'num_edges':       _ce_props.get('num_edges', ''),
                        'episode':         ce.get('episode', ''),
                        'gap':             ce.get('gap', ''),
                        'margin':          ce.get('margin', ''),
                        'rhs':             ce.get('rhs', ''),
                        'relation':        ce.get('relation', ''),
                        'found_at':        ce.get('found_at', ''),
                        'polytope_id':     ce.get('polytope_id', ''),
                    }, _pv_fh, indent=2)
                _fig, _ax = plt.subplots(figsize=(max(4, len(_nodes)//2), max(4, len(_nodes)//2)))
                _im = _ax.imshow(_adj, cmap="Blues", vmin=0, vmax=1)
                _ax.set_xticks(range(len(_nodes)))
                _ax.set_yticks(range(len(_nodes)))
                _ax.set_xticklabels(_nodes, fontsize=6, rotation=90)
                _ax.set_yticklabels(_nodes, fontsize=6)
                _ax.set_title(f"Adjacency Matrix - CE #{i} (Ep {ce.get('episode','?')})", fontsize=10)
                _fig.colorbar(_im, ax=_ax, shrink=0.8)
                _fig.tight_layout()
                _fig.savefig(os.path.join(ce_path, 'adjacency_matrix.png'), dpi=150)
                plt.close(_fig)

            with open(os.path.join(ce_dir, 'all_p_vectors.json'), 'w') as _all_pv_fh:
                json.dump([
                    {
                        'ce_index':        i,
                        'p_vector':        ce.get('p_vector', ce.get('properties', {}).get('p_vector', [])),
                        'p3':              ce.get('properties', {}).get('p3', ''),
                        'p4':              ce.get('properties', {}).get('p4', ''),
                        'p5':              ce.get('properties', {}).get('p5', ''),
                        'p6':              ce.get('properties', {}).get('p6', ''),
                        'sum_pk_after_p6': ce.get('properties', {}).get('sum_pk_after_p6', ''),
                        'num_vertices':    ce.get('properties', {}).get('num_vertices', ''),
                        'episode':         ce.get('episode', ''),
                        'gap':             ce.get('gap', ''),
                        'margin':          ce.get('margin', ''),
                    }
                    for i, ce in enumerate(res['counterexamples'])
                ], _all_pv_fh, indent=2)

        plot_metrics(
            result_path,
            list(range(len(res.get('episode_rewards', [])))),
            res.get('episode_rewards', []),
            res.get('best_gaps', []),
            res.get('stop_probs', []),
            res.get('entropies', []),
            res.get('ce_rates', []),
        )


    results_list = []
    _total_conj = sum(1 for s in work_specs if not _is_trivial_nonneg(s.formula))
    _status_file = f"/tmp/ablation_status_{iris_sort}.json"
    _conj_idx = 0
    _pbar = tqdm(
        total=_total_conj,
        desc=f"[{iris_sort:>3s}]",
        unit="conj",
        leave=False,
        dynamic_ncols=True,
        bar_format="{desc} {n_fmt}/{total_fmt}",
    )
    for spec in work_specs:
        # Skip trivial non‑negative bounds (always true, no CE to find)
        if _is_trivial_nonneg(spec.formula):
            mark_conjecture_status(spec.name, 'trivial', reg)
            save_registry(reg, source_dir)
            continue
        attempts_wo_ce = reg.get(spec.name, {}).get('attempts_without_ce', 0)
        _conj_idx += 1

        # ── Resume: skip already-completed conjectures ────────────────────────
        if spec.name in _checkpoint:
            print(f"[resume] Skipping {spec.name} (already done)")
            _ckpt_res = _checkpoint[spec.name]
            # Reconstruct a minimal res dict so results_list stays consistent
            _fake_res = {
                "formula": _ckpt_res.get("formula", spec.formula),
                "coefficients": _ckpt_res.get("coefficients", {}),
                "episode_rewards": _ckpt_res.get("episode_rewards", []),
                "best_gaps": _ckpt_res.get("best_gaps", []),
                "gaps": [_ckpt_res.get("max_gap", 0)],
                "stop_probs": _ckpt_res.get("stop_probs", []),
                "entropies": _ckpt_res.get("entropies", []),
                "ce_rates": _ckpt_res.get("ce_rates", []),
                "counterexamples": _ckpt_res.get("counterexamples", []),
                "metrics": _ckpt_res.get("metrics", {}),
                "total_ops": _ckpt_res.get("total_ops"),
                "avg_ops_per_ep": _ckpt_res.get("avg_ops_per_ep"),
                "total_training_time": _ckpt_res.get("total_training_time"),
                "avg_time_per_ep": _ckpt_res.get("avg_time_per_ep"),
                "final_lr": _ckpt_res.get("final_lr"),
                "trajectories": [],
            }
            results_list.append((spec.name, _fake_res))
            _pbar.update(1)
            continue
        # ─────────────────────────────────────────────────────────────────────

        try:
            with open(_status_file, 'w') as _sf:
                json.dump({"conjecture": spec.name, "conj_idx": _conj_idx, "total_conj": _total_conj, "episode": 0, "total_episodes": episodes, "ce_count": 0}, _sf)
        except Exception:
            pass
        res = train_on_conjecture(spec.formula, name=spec.name, num_episodes=episodes,
                                  max_nodes_cap=max_nodes_cap, end_on_caps=end_on_caps,
                                  exit_on_first_ce=exit_on_first_ce, update_steps=update_steps,
                                  attempts_without_ce=attempts_wo_ce, status_file=_status_file)
        results_list.append((spec.name, res))

        ce_found_this = bool(res.get('counterexamples'))
        _pbar.update(1)

        if ce_found_this:
            ce_id = res['counterexamples'][0].get('polytope_id')
            record_ce_found(spec.name, reg)
            mark_conjecture_status(spec.name, 'falsified', reg, ce_polytope_id=ce_id)
            try:
                mark_conjecture_as_solved(spec.name, source_dir)
            except Exception:
                pass
        else:
            # No CE found this run → increment attempt counter, possibly mark potentially_valid
            increment_attempt(spec.name, reg)

        # ── Save per-conjecture outputs immediately (function defined above loop)
        # Only save outputs for newly-computed conjectures (not resumed ones,
        # which already have their files on disk)
        if spec.name not in _checkpoint:
            _save_conjecture_outputs(spec.name, res)

        # ── Save checkpoint immediately after each conjecture ─────────────────
        _save_checkpoint(spec.name, res)

        # Persist registry after each conjecture to avoid data loss on later failures
        save_registry(reg, source_dir)

    _pbar.close()
    print("\n" + "="*30 + " Final Summary " + "="*30)
    for name, res in results_list:
        m = res.get('metrics', {})
        ce_found = len(res['counterexamples'])
        avg_ops = res.get('avg_ops_per_ep', 0)
        avg_time = res.get('avg_time_per_ep', 0)
        print(f"-> {name:20} | CEs: {ce_found:3} | Avg Ops: {avg_ops:6.1f} | Avg Time: {avg_time:5.2f}s")
    print(f"\nResults saved to: {results_dir}")

    # ── Mean Curves across all conjectures ────────────────────────────────────
    try:
        _entropy_seqs   = [res.get('entropies', [])    for _, res in results_list if res.get('entropies')]
        _reward_seqs    = [res.get('episode_rewards', []) for _, res in results_list if res.get('episode_rewards')]
        _stopprob_seqs  = [res.get('stop_probs', [])   for _, res in results_list if res.get('stop_probs')]

        def _mean_curve(seqs):
            """Element-wise mean across sequences; handles variable lengths safely."""
            if not seqs:
                return [], []
            min_len = min(len(s) for s in seqs)
            if min_len == 0:
                return [], []
            mean_vals = [float(np.mean([s[i] for s in seqs])) for i in range(min_len)]
            return list(range(min_len)), mean_vals

        _mean_curves_dir = repo_root / "Performance_Analysis" / "mean_curves"
        _mean_curves_dir.mkdir(parents=True, exist_ok=True)

        # mean entropy
        _xs, _ys = _mean_curve(_entropy_seqs)
        if _xs:
            fig, ax = plt.subplots(figsize=(8, 4.5))
            ax.plot(_xs, _ys, color="#ff7f0e", label="Mean policy entropy")
            ax.set_xlabel("Episode")
            ax.set_ylabel("Entropy")
            ax.set_title(f"Mean Policy Entropy (across {len(_entropy_seqs)} conjectures)")
            ax.grid(True, alpha=0.3)
            ax.legend()
            fig.tight_layout()
            fig.savefig(_mean_curves_dir / "mean_entropy_curve.png", dpi=150)
            plt.close(fig)
            print(f"[mean_curves] mean_entropy_curve      -> {_mean_curves_dir / 'mean_entropy_curve.png'}")

        # mean reward
        _xs, _ys = _mean_curve(_reward_seqs)
        if _xs:
            fig, ax = plt.subplots(figsize=(8, 4.5))
            ax.plot(_xs, _ys, color="#1f77b4", label="Mean episode reward")
            ax.set_xlabel("Episode")
            ax.set_ylabel("Reward")
            ax.set_title(f"Mean Episode Reward (across {len(_reward_seqs)} conjectures)")
            ax.grid(True, alpha=0.3)
            ax.legend()
            fig.tight_layout()
            fig.savefig(_mean_curves_dir / "mean_reward_curve.png", dpi=150)
            plt.close(fig)
            print(f"[mean_curves] mean_reward_curve       -> {_mean_curves_dir / 'mean_reward_curve.png'}")

        # mean stop probability
        _xs, _ys = _mean_curve(_stopprob_seqs)
        if _xs:
            fig, ax = plt.subplots(figsize=(8, 4.5))
            ax.plot(_xs, _ys, color="#2ca02c", label="Mean stop probability")
            ax.set_xlabel("Episode")
            ax.set_ylabel("Probability")
            ax.set_title(f"Mean Stop Probability (across {len(_stopprob_seqs)} conjectures)")
            ax.grid(True, alpha=0.3)
            ax.legend()
            fig.tight_layout()
            fig.savefig(_mean_curves_dir / "mean_stop_probability_curve.png", dpi=150)
            plt.close(fig)
            print(f"[mean_curves] mean_stop_probability   -> {_mean_curves_dir / 'mean_stop_probability_curve.png'}")

    except Exception as _exc:
        print(f"[mean_curves] Warning: failed to generate mean curves ({_exc})")
    # ─────────────────────────────────────────────────────────────────────────


    # Written to <repo_root>/summary/summary_of_{iris_sort}/
    try:
        import csv
        _summary_root = repo_root / "summary"
        _summary_root.mkdir(parents=True, exist_ok=True)
        # Use a stable directory name so reruns overwrite/update incrementally
        _base_name = f"summary_of_{iris_sort}"
        summary_dir = _summary_root / _base_name

        run_ts = datetime.now().strftime("%Y%m%d_%H%M%S")

        fieldnames = [
            "conjecture_name",
            "formula",
            "p_vector",
            "p_3", "p_4", "p_5", "p_6", "sum_pk_k>=7",
            "episode_to_find_first_ce",
            "coefficients_for_p3", "coefficients_for_p4", "coefficients_for_p5",
            "coefficients_for_p6", "coefficients_for_sum_pk_k>=7",
            "number_of_ce",
            "number_of_episodes_found_ce",
            "total_training_time",
            "total_episodes",
            "ce_rate",
            "total_reward(x10³)",
            "T", "R", "L", "iris_score",
            "final_lr",
        ]

        # Conjecture-level fields: only written on the FIRST row of each conjecture.
        # CE-level fields (p_vector, p_3~p_6, sum_pk, ce_episode, ce_gap,
        # ce_margin, ce_vertices): one row per CE, subsequent rows leave all
        # conjecture-level fields blank so dropna() naturally de-duplicates them.
        _CONJ_LEVEL_FIELDS = [
            "conjecture_name", "formula",
            "coefficients_for_p3", "coefficients_for_p4", "coefficients_for_p5",
            "coefficients_for_p6", "coefficients_for_sum_pk_k>=7",
            "number_of_ce", "number_of_episodes_found_ce",
            "total_training_time", "total_episodes", "ce_rate",
            "total_reward(x10³)", "T", "R", "L", "iris_score", "final_lr",
        ]

        rows = []
        for name, res in results_list:
            m = res.get("metrics", {})
            iris = iris_scores.get(name) or {}

            coeffs = res.get("coefficients", {}) or {}
            c_p3   = coeffs.get("p3", 0) or 0
            c_p4   = coeffs.get("p4", 0) or 0
            c_p5   = coeffs.get("p5", 0) or 0
            c_p6   = coeffs.get("p6", 0) or 0
            c_sum7 = coeffs.get("sum_pk_after_p6", 0) or coeffs.get("sum_pk", 0) or 0

            ce_list = res.get("counterexamples", [])

            # Conjecture-level values (filled only on first row)
            _conj_vals = {
                "conjecture_name":               name,
                "formula":                       res.get("formula", ""),
                "coefficients_for_p3":           c_p3 if c_p3 != 0 else "",
                "coefficients_for_p4":           c_p4 if c_p4 != 0 else "",
                "coefficients_for_p5":           c_p5 if c_p5 != 0 else "",
                "coefficients_for_p6":           c_p6 if c_p6 != 0 else "",
                "coefficients_for_sum_pk_k>=7":  c_sum7 if c_sum7 != 0 else "",
                "number_of_ce":                  len(ce_list),
                "number_of_episodes_found_ce":   round(m.get("ce_rate", 0.0) * episodes),
                "total_training_time":           round(res.get("total_training_time") or 0.0, 2),
                "total_episodes":                episodes,
                "ce_rate":                       round(m.get("ce_rate", 0.0), 6),
                "total_reward(x10³)":           round(sum(res.get("episode_rewards", []) or []) / 1000.0, 4),
                "T":                             iris.get("T", ""),
                "R":                             iris.get("R", ""),
                "L":                             iris.get("L", ""),
                "iris_score":                    iris.get("iris_score", ""),
                "final_lr":                      res.get("final_lr", ""),
                "_relation":                     res.get("relation", ">="),
            }
            # Blank conjecture-level values for 2nd+ CE rows
            _conj_blank = {k: "" for k in _CONJ_LEVEL_FIELDS}
            _conj_blank["_relation"] = res.get("relation", ">=")

            if ce_list:
                for ce_idx, ce in enumerate(ce_list):
                    ce_props = ce.get("properties", {})
                    _ce_fields = {
                        "p_vector":                 str(ce.get("p_vector") or ce_props.get("p_vector", "")),
                        "p_3":                      ce_props.get("p3", ""),
                        "p_4":                      ce_props.get("p4", ""),
                        "p_5":                      ce_props.get("p5", ""),
                        "p_6":                      ce_props.get("p6", ""),
                        "sum_pk_k>=7":              ce_props.get("sum_pk_after_p6", ""),
                        "episode_to_find_first_ce": ce.get("episode", ""),
                    }
                    if ce_idx == 0:
                        rows.append({**_conj_vals, **_ce_fields})
                    else:
                        rows.append({**_conj_blank, **_ce_fields})
            else:
                rows.append({
                    **_conj_vals,
                    "p_vector": "", "p_3": "", "p_4": "", "p_5": "", "p_6": "",
                    "sum_pk_k>=7": "", "episode_to_find_first_ce": "",
                })

        def _write_csv(path, data):
            with open(path, "w", newline="", encoding="utf-8") as fh:
                writer = csv.DictWriter(fh, fieldnames=fieldnames)
                writer.writeheader()
                writer.writerows({k: v for k, v in r.items() if not k.startswith("_")} for r in data)

        # Tag every row with its conjecture's _has_ce flag.
        # Propagate downward since 2nd+ CE rows have blank number_of_ce.
        _cur_name = None
        _cur_has_ce = False
        for r in rows:
            if r["conjecture_name"] != "":
                _cur_name = r["conjecture_name"]
                n = r.get("number_of_ce", "")
                _cur_has_ce = (int(n) > 0) if n != "" else False
            r["_has_ce"] = _cur_has_ce

        rows_with_ce    = [r for r in rows if r["_has_ce"]]
        rows_without_ce = [r for r in rows if not r["_has_ce"]]

        # lowerbound / upperbound splits within each group
        rows_lb            = [r for r in rows            if r["_relation"] == ">="]
        rows_ub            = [r for r in rows            if r["_relation"] == "<="]
        rows_with_ce_lb    = [r for r in rows_with_ce    if r["_relation"] == ">="]
        rows_with_ce_ub    = [r for r in rows_with_ce    if r["_relation"] == "<="]
        rows_without_ce_lb = [r for r in rows_without_ce if r["_relation"] == ">="]
        rows_without_ce_ub = [r for r in rows_without_ce if r["_relation"] == "<="]

        # Directory structure:
        # summary_{iris_sort}/
        #   summary_all.csv / summary_lowerbound.csv / summary_upperbound.csv
        #   summary_with_ce/    summary_all.csv / _lowerbound.csv / _upperbound.csv
        #   summary_without_ce/ summary_all.csv / _lowerbound.csv / _upperbound.csv
        _all_dir        = summary_dir / "summary_all"
        _with_ce_dir    = summary_dir / "summary_with_ce"
        _without_ce_dir = summary_dir / "summary_without_ce"
        _all_dir.mkdir(parents=True, exist_ok=True)
        _with_ce_dir.mkdir(parents=True, exist_ok=True)
        _without_ce_dir.mkdir(parents=True, exist_ok=True)

        # summary_all/ summary_with_ce/ summary_without_ce/ — each with 3 CSVs
        _write_csv(_all_dir        / "summary.csv",        rows)
        _write_csv(_all_dir        / "summary_lb_p6.csv",  rows_lb)
        _write_csv(_all_dir        / "summary_ub_p6.csv",  rows_ub)
        _write_csv(_with_ce_dir    / "summary.csv",        rows_with_ce)
        _write_csv(_with_ce_dir    / "summary_lb_p6.csv",  rows_with_ce_lb)
        _write_csv(_with_ce_dir    / "summary_ub_p6.csv",  rows_with_ce_ub)
        _write_csv(_without_ce_dir / "summary.csv",        rows_without_ce)
        _write_csv(_without_ce_dir / "summary_lb_p6.csv",  rows_without_ce_lb)
        _write_csv(_without_ce_dir / "summary_ub_p6.csv",  rows_without_ce_ub)
        print(f"[summary] summary_all/all                -> {len(rows)} rows")
        print(f"[summary] summary_all/lowerbound         -> {len(rows_lb)} rows")
        print(f"[summary] summary_all/upperbound         -> {len(rows_ub)} rows")
        print(f"[summary] summary_with_ce/all            -> {len(rows_with_ce)} rows")
        print(f"[summary] summary_with_ce/lowerbound     -> {len(rows_with_ce_lb)} rows")
        print(f"[summary] summary_with_ce/upperbound     -> {len(rows_with_ce_ub)} rows")
        print(f"[summary] summary_without_ce/all         -> {len(rows_without_ce)} rows")
        print(f"[summary] summary_without_ce/lowerbound  -> {len(rows_without_ce_lb)} rows")
        print(f"[summary] summary_without_ce/upperbound  -> {len(rows_without_ce_ub)} rows")

    except Exception as exc:
        print(f"[summary] Warning: failed to write summary table ({exc})")
    # ─────────────────────────────────────────────────────────────────────────

    # ── P-Vector Charts (one set per summary subset) ─────────────────────────
    def _draw_charts(chart_rows, charts_dir, title_suffix, ts):
        """Draw charts for a given list of rows into charts_dir.
        Conjecture-level fields (coefficients, etc.) are only on the first row
        of each conjecture; CE-level fields (p_3~p_6, etc.) appear on every
        CE row. Charts respect this distinction automatically.
        """
        try:
            import matplotlib.pyplot as plt
            coeff_cols = ["coefficients_for_p3", "coefficients_for_p4", "coefficients_for_p5",
                          "coefficients_for_p6", "coefficients_for_sum_pk_k>=7"]
            labels     = ["p3", "p4", "p5", "p6", "sum_pk_k>=7"]
            colors     = ["#4C8BE2", "#E2724C", "#4CE2A0", "#E2C44C", "#A04CE2"]

            charts_dir.mkdir(parents=True, exist_ok=True)

            # Collect non-zero coefficient values per component.
            # Coefficients are conjecture-level: only present on first row
            # (subsequent CE rows have blank coefficients), so iterating over
            # all rows and skipping blanks naturally gives one entry per conjecture.
            p_data = {col: [] for col in coeff_cols}
            for row in chart_rows:
                for col in coeff_cols:
                    val = row.get(col, "")
                    if val != "":
                        try:
                            p_data[col].append(float(val))
                        except (ValueError, TypeError):
                            pass

            counts = [len(p_data[col]) for col in coeff_cols]

            # Bar chart: number of conjectures with non-zero coefficient
            fig, ax = plt.subplots(figsize=(8, 5))
            bars = ax.bar(labels, counts, color="#4C8BE2", edgecolor="white", linewidth=0.8)
            ax.bar_label(bars, padding=3, fontsize=10)
            ax.set_title(f"Non-zero coefficient count ({title_suffix})", fontsize=13)
            ax.set_xlabel("p-vector component")
            ax.set_ylabel("Number of conjectures")
            ax.set_ylim(0, max(counts) * 1.15 if counts and max(counts) > 0 else 10)
            ax.spines[["top", "right"]].set_visible(False)
            fig.tight_layout()
            bar_path = charts_dir / f"number_of_nonzero_coefficients_{ts}.png"
            fig.savefig(bar_path, dpi=150)
            plt.close(fig)
            print(f"[summary] Saved bar chart    -> {bar_path}")

            # Boxplot: coefficient value distribution
            plot_labels = [lbl for lbl, col in zip(labels, coeff_cols) if p_data[col]]
            plot_vals   = [p_data[col] for col in coeff_cols if p_data[col]]

            if plot_vals:
                fig, ax = plt.subplots(figsize=(9, 5))
                bp = ax.boxplot(plot_vals, labels=plot_labels, patch_artist=True,
                                medianprops=dict(color="white", linewidth=2))
                for patch, color in zip(bp["boxes"], colors[:len(bp["boxes"])]):
                    patch.set_facecolor(color)
                    patch.set_alpha(0.75)
                for i, vals in enumerate(plot_vals):
                    x = i + 1
                    mn, mean, mx = min(vals), sum(vals)/len(vals), max(vals)
                    ax.text(x + 0.3, mn,   f"min={mn:.2f}",  fontsize=7, va="center", color="#555")
                    ax.text(x + 0.3, mean, f"avg={mean:.2f}", fontsize=7, va="center", color="#222")
                    ax.text(x + 0.3, mx,   f"max={mx:.2f}",  fontsize=7, va="center", color="#555")
                ax.set_title(f"Coefficient distribution ({title_suffix})", fontsize=13)
                ax.set_xlabel("p-vector component")
                ax.set_ylabel("Coefficient value")
                ax.spines[["top", "right"]].set_visible(False)
                fig.tight_layout()
                box_path = charts_dir / f"boxplot_of_coefficients_{ts}.png"
                fig.savefig(box_path, dpi=150)
                plt.close(fig)
                print(f"[summary] Saved coeff boxplot -> {box_path}")

            # ── Histograms + Boxplot: p-vector actual values across ALL CEs ───
            pv_cols   = ["p_3", "p_4", "p_5", "p_6", "sum_pk_k>=7"]
            pv_labels = ["p3",  "p4",  "p5",  "p6",  "sum_pk_k>=7"]
            pv_colors = ["#4C8BE2", "#E2724C", "#4CE2A0", "#E2C44C", "#A04CE2"]

            pv_data = {}
            for col, lbl, clr in zip(pv_cols, pv_labels, pv_colors):
                vals = []
                for row in chart_rows:
                    v = row.get(col, "")
                    if v != "":
                        try:
                            vals.append(float(v))
                        except (ValueError, TypeError):
                            pass
                pv_data[lbl] = vals
                if not vals:
                    continue

                # Histogram (one per component)
                fig, ax = plt.subplots(figsize=(7, 4))
                ax.hist(vals, bins="auto", color=clr, edgecolor="white", linewidth=0.6, alpha=0.85)
                mean_v = sum(vals) / len(vals)
                ax.axvline(mean_v, color="#222", linewidth=1.5,
                           linestyle="--", label=f"mean={mean_v:.2f}")
                ax.set_title(f"{lbl} distribution — all CEs ({title_suffix})", fontsize=13)
                ax.set_xlabel(lbl)
                ax.set_ylabel("Count")
                ax.legend(fontsize=9)
                ax.spines[["top", "right"]].set_visible(False)
                fig.tight_layout()
                hist_path = charts_dir / f"histogram_{lbl}_{ts}.png"
                fig.savefig(hist_path, dpi=150)
                plt.close(fig)
                print(f"[summary] Saved histogram    -> {hist_path}")


        except Exception as exc:
            print(f"[summary] Warning: charts failed for {title_suffix}: {exc}")

    _draw_charts(rows,            summary_dir / "charts",            "all",        run_ts)
    _draw_charts(rows_with_ce,    summary_dir / "charts_with_ce",    "with CE",    run_ts)
    _draw_charts(rows_without_ce, summary_dir / "charts_without_ce", "without CE", run_ts)
    # ─────────────────────────────────────────────────────────────────────────

    return results_list, results_dir


if __name__ == "__main__":
    import argparse

    np.random.seed(42)
    torch.manual_seed(42)
    if torch.cuda.is_available():
        torch.cuda.manual_seed(42)

    ap = argparse.ArgumentParser(description="Counterexample agent (built-in PPO)")
    ap.add_argument("--mode", choices=["ce", "train", "test"], default="ce", help="ce: run registry CE; train: single formula; test: built-in test formula")
    ap.add_argument("--episodes", type=int, default=600, help="Episodes per conjecture/run")
    ap.add_argument("--max-nodes", type=int, default=128, help="Maximum nodes cap inside the environment")
    ap.add_argument("--no-end-on-caps", action="store_true", help="Keep running when caps are reached (mask only)")
    ap.add_argument("--source", default=None, help="Custom conjecture source for CE runs")
    ap.add_argument("--results-dir", default=None, help="Override output directory for test runs")
    ap.add_argument("--formula", default=None, help="Formula for --mode train (if (...), then p6 >= (...))")
    ap.add_argument("--name", default=None, help="Optional name for --mode train")
    ap.add_argument("--run-full-episodes", dest="exit_on_first_ce", action="store_false",
                    help="Disable early stop; run all episodes even after first CE (default: exit on first CE)")
    ap.set_defaults(exit_on_first_ce=False)
    ap.add_argument("--update-steps", type=int, default=512, help="PPO update_steps (buffer size before each update)")
    ap.add_argument("--target-names", nargs="+", default=None, help="Specific conjecture name(s) to run in CE mode (e.g. auto_20260226_234734_76)")
    ap.add_argument("--iris-sort", default="TRL",
                    choices=["T", "R", "L", "TR", "TL", "RL", "TRL", "all"],
                    help="IRIS metric combination used to sort conjectures. Use 'all' to run all 7 in parallel (default: TRL)")
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
    else:  # ce
        _ABLATION_ORDER = ["T", "R", "L", "TR", "TL", "RL", "TRL"]

        def _run_one_sort(iris_sort_val):
            """Run one iris_sort combination in a subprocess and return its results."""
            import subprocess, sys
            cmd = [sys.executable, "-m", "agents.counterexample_finding_agent",
                   "--mode", "ce",
                   "--episodes", str(args.episodes),
                   "--max-nodes", str(args.max_nodes),
                   "--update-steps", str(args.update_steps),
                   "--iris-sort", iris_sort_val,
                   ]
            if args.source:
                cmd += ["--source", args.source]
            if args.target_names:
                cmd += ["--target-names"] + args.target_names
            if not args.exit_on_first_ce:
                cmd += ["--run-full-episodes"]
            if args.no_end_on_caps:
                cmd += ["--no-end-on-caps"]
            print(f"[parallel] Launching iris-sort={iris_sort_val} ...")
            proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            out_lines = []
            for line in proc.stdout:
                out_lines.append(line)
            proc.wait()
            return iris_sort_val, proc.returncode

        if args.iris_sort == "all":
            # ── Parallel: spawn all 7 subprocesses at once ───────────────────
            import concurrent.futures
            print(f"\n{'='*60}")
            print(f"  ABLATION: running all 7 IRIS combinations in parallel")
            print(f"{'='*60}\n")

            with concurrent.futures.ThreadPoolExecutor(max_workers=7) as executor:
                futures = {executor.submit(_run_one_sort, s): s for s in _ABLATION_ORDER}
                for fut in concurrent.futures.as_completed(futures):
                    sort_val, rc = fut.result()
                    status = "OK" if rc == 0 else f"FAILED (code {rc})"
                    print(f"\n[parallel] iris-sort={sort_val} finished -> {status}")

            print(f"\n{'='*60}")
            print("  All 7 ablation runs complete.")
            print(f"{'='*60}")

            # Final consolidated chart from accumulated ablation_data.json
            try:
                _repo_root = Path(__file__).resolve().parents[1]
                _perf_ce = _repo_root / "Performance_Analysis" / "ablation_test_iris_ce"
                _perf_rw = _repo_root / "Performance_Analysis" / "ablation_test_iris_rewards"
                _data_file_ce = _perf_ce / "ablation_data.json"
                _data_file_rw = _perf_rw / "ablation_data.json"

                if _data_file_ce.exists():
                    _all_runs = json.load(open(_data_file_ce))
                    _labels   = [s for s in _ABLATION_ORDER if s in _all_runs]
                    _means_ce = [_all_runs[s]["mean_ce_rate"]    for s in _labels]
                    _means_rw = [_all_runs[s]["mean_total_reward"] for s in _labels]
                    _nc       = [_all_runs[s]["n_with_ce"]       for s in _labels]
                    _total    = [_all_runs[s]["n_conjectures"]   for s in _labels]

                    # CE Rate chart
                    _max_ce  = max(_means_ce) if _means_ce else 0.0
                    _cols_ce = ['#E2724C' if v == _max_ce and v > 0 else '#4C8BE2' if v > 0 else '#CCCCCC' for v in _means_ce]
                    _fig_ce, _ax_ce = plt.subplots(figsize=(max(8, len(_labels) * 1.4), 5))
                    _bars_ce = _ax_ce.bar(_labels, _means_ce, color=_cols_ce, edgecolor='white', linewidth=0.8, width=0.55)
                    for _b, _v, _nce, _tot in zip(_bars_ce, _means_ce, _nc, _total):
                        _ax_ce.text(_b.get_x() + _b.get_width() / 2,
                                    _v + (_max_ce * 0.015 if _max_ce > 0 else 0.0005),
                                    f'{_v:.4f}\n({_nce}/{_tot})',
                                    ha='center', va='bottom', fontsize=8, color='#222', linespacing=1.4)
                    _ax_ce.set_xlabel('IRIS Sort Combination', fontsize=11)
                    _ax_ce.set_ylabel('Mean CE Rate', fontsize=11)
                    _ax_ce.set_title('Ablation: IRIS Metric Combination vs CE Rate', fontsize=13, fontweight='bold')
                    _ax_ce.set_ylim(0, (_max_ce * 1.4) if _max_ce > 0 else 0.01)
                    _ax_ce.spines[['top', 'right']].set_visible(False)
                    if _max_ce > 0:
                        _best_ce = _labels[_means_ce.index(_max_ce)]
                        _ax_ce.annotate(f'Best: {_best_ce}', xy=(_best_ce, _max_ce),
                                        xytext=(_best_ce, _max_ce * 1.22), ha='center', fontsize=9, color='#E2724C',
                                        arrowprops=dict(arrowstyle='->', color='#E2724C', lw=1.2))
                    _fig_ce.tight_layout()
                    _fig_ce.savefig(_perf_ce / "ablation_iris_ce_rate_FINAL.png", dpi=150)
                    plt.close(_fig_ce)
                    print(f"[ablation] Final CE Rate chart   -> {_perf_ce / 'ablation_iris_ce_rate_FINAL.png'}")

                    # CE Rate boxplot (per-conjecture ce_rate distribution)
                    _ce_per = {
                        s: [v for v in _all_runs[s].get("per_conjecture", {}).values()
                            if isinstance(v, dict) and "ce_rate" in v]
                        for s in _labels
                    }
                    _ce_per_vals = {
                        s: [v["ce_rate"] for v in _ce_per[s]]
                        for s in _labels
                    }
                    _fig_cebp, _ax_cebp = plt.subplots(figsize=(max(9, len(_labels) * 1.4), 6))
                    _bp_ce = _ax_cebp.boxplot(
                        [_ce_per_vals[s] for s in _labels], labels=_labels, patch_artist=True,
                        medianprops=dict(color='#E2724C', linewidth=2),
                        whiskerprops=dict(color='#555', linewidth=1.2),
                        capprops=dict(color='#555', linewidth=1.2),
                        flierprops=dict(marker='o', markerfacecolor='#4C8BE2', markersize=4, alpha=0.5, linestyle='none'),
                    )
                    for _p in _bp_ce['boxes']:
                        _p.set_facecolor('#a8c4e0'); _p.set_alpha(0.85)
                    for _i, _s in enumerate(_labels, start=1):
                        _vs = _ce_per_vals[_s]
                        if not _vs: continue
                        _sr = np.array(_vs)
                        _nudge = (_sr.max() - _sr.min()) * 0.02 if _sr.max() != _sr.min() else max(abs(_sr.max()) * 0.01, 0.0001)
                        _ax_cebp.text(_i, _sr.max() + _nudge,                    f'max: {_sr.max():.4f}',    ha='center', va='bottom', fontsize=7.5, color='#333')
                        _ax_cebp.text(_i, _sr.min() - _nudge,                    f'min: {_sr.min():.4f}',    ha='center', va='top',    fontsize=7.5, color='#333')
                        _ax_cebp.text(_i + 0.3, float(np.mean(_sr)),             f'mean: {np.mean(_sr):.4f}', ha='left',  va='center', fontsize=7.5, color='#1f77b4', fontweight='bold')
                        _ax_cebp.text(_i + 0.3, float(np.median(_sr)) - _nudge,  f'med: {np.median(_sr):.4f}', ha='left', va='center', fontsize=7.5, color='#E2724C', fontweight='bold')
                    _ax_cebp.set_xlabel('IRIS Sort Combination', fontsize=11)
                    _ax_cebp.set_ylabel('CE Rate per Conjecture', fontsize=11)
                    _ax_cebp.set_title('CE Rate Distribution per IRIS Sort', fontsize=13, fontweight='bold')
                    _ax_cebp.spines[['top', 'right']].set_visible(False)
                    _ax_cebp.grid(axis='y', alpha=0.3)
                    _fig_cebp.tight_layout()
                    _fig_cebp.savefig(_perf_ce / "ablation_iris_ce_rate_boxplot_FINAL.png", dpi=150)
                    plt.close(_fig_cebp)
                    print(f"[ablation] Final CE Rate boxplot -> {_perf_ce / 'ablation_iris_ce_rate_boxplot_FINAL.png'}")

                    # Total Reward chart
                    _means_rw_k = [v / 1000.0 for v in _means_rw]
                    _max_rw = max(_means_rw_k) if _means_rw_k else 0.0
                    _min_rw = min(_means_rw_k) if _means_rw_k else 0.0
                    _cols_rw = ['#E2724C' if v == _max_rw and _max_rw != _min_rw else '#4C8BE2' for v in _means_rw_k]
                    _fig_rw, _ax_rw = plt.subplots(figsize=(max(8, len(_labels) * 1.4), 5))
                    _bars_rw = _ax_rw.bar(_labels, _means_rw_k, color=_cols_rw, edgecolor='white', linewidth=0.8, width=0.55)
                    _pad_rw = abs(_max_rw) * 0.03 if _max_rw != 0 else 0.5
                    for _b, _v in zip(_bars_rw, _means_rw_k):
                        _ax_rw.text(_b.get_x() + _b.get_width() / 2,
                                    _v + (_pad_rw if _v >= 0 else -_pad_rw * 2),
                                    f'{_v:.2f}', ha='center', va='bottom', fontsize=9, color='#222')
                    _ax_rw.set_xlabel('IRIS Sort Combination', fontsize=11)
                    _ax_rw.set_ylabel('Mean Total Reward (×10³)', fontsize=11)
                    _ax_rw.set_title('Ablation: IRIS Metric Combination vs Total Reward', fontsize=13, fontweight='bold')
                    _ax_rw.axhline(0, color='#999', linewidth=0.8, linestyle='--')
                    _y_margin = abs(_max_rw - _min_rw) * 0.3 if _max_rw != _min_rw else max(abs(_max_rw) * 0.2, 1.0)
                    _ax_rw.set_ylim(_min_rw - _y_margin * 0.3, _max_rw + _y_margin * 1.5)
                    _ax_rw.spines[['top', 'right']].set_visible(False)
                    if _max_rw != _min_rw:
                        _best_rw = _labels[_means_rw_k.index(_max_rw)]
                        _ax_rw.annotate(f'Best: {_best_rw}', xy=(_best_rw, _max_rw),
                                        xytext=(_best_rw, _max_rw + _y_margin),
                                        ha='center', fontsize=9, color='#E2724C',
                                        arrowprops=dict(arrowstyle='->', color='#E2724C', lw=1.2))
                    _fig_rw.tight_layout()
                    _fig_rw.savefig(_perf_rw / "ablation_iris_total_reward_FINAL.png", dpi=150)
                    plt.close(_fig_rw)
                    print(f"[ablation] Final Rewards chart   -> {_perf_rw / 'ablation_iris_total_reward_FINAL.png'}")

                    # Total Reward boxplot
                    _rw_per = {
                        s: [v / 1000.0 for v in _all_runs[s].get("per_conjecture", {}).values()]
                        for s in _labels
                    }
                    _fig_rwbp, _ax_rwbp = plt.subplots(figsize=(max(9, len(_labels) * 1.4), 6))
                    _bp_rw = _ax_rwbp.boxplot(
                        [_rw_per[s] for s in _labels], labels=_labels, patch_artist=True,
                        medianprops=dict(color='#E2724C', linewidth=2),
                        whiskerprops=dict(color='#555', linewidth=1.2),
                        capprops=dict(color='#555', linewidth=1.2),
                        flierprops=dict(marker='o', markerfacecolor='#4C8BE2', markersize=4, alpha=0.5, linestyle='none'),
                    )
                    for _p in _bp_rw['boxes']:
                        _p.set_facecolor('#a8c4e0'); _p.set_alpha(0.85)
                    for _i, _s in enumerate(_labels, start=1):
                        _vs = _rw_per[_s]
                        if not _vs: continue
                        _sr = np.array(_vs)
                        _nudge = (_sr.max() - _sr.min()) * 0.02 if _sr.max() != _sr.min() else max(abs(_sr.max()) * 0.01, 0.001)
                        _ax_rwbp.text(_i, _sr.max() + _nudge,           f'max: {_sr.max():.2f}',    ha='center', va='bottom', fontsize=7.5, color='#333')
                        _ax_rwbp.text(_i, _sr.min() - _nudge,           f'min: {_sr.min():.2f}',    ha='center', va='top',    fontsize=7.5, color='#333')
                        _ax_rwbp.text(_i + 0.3, float(np.mean(_sr)),    f'mean: {np.mean(_sr):.2f}', ha='left',  va='center', fontsize=7.5, color='#1f77b4', fontweight='bold')
                        _ax_rwbp.text(_i + 0.3, float(np.median(_sr)) - _nudge, f'med: {np.median(_sr):.2f}', ha='left', va='center', fontsize=7.5, color='#E2724C', fontweight='bold')
                    _ax_rwbp.set_xlabel('IRIS Sort Combination', fontsize=11)
                    _ax_rwbp.set_ylabel('Total Reward per Conjecture (×10³)', fontsize=11)
                    _ax_rwbp.set_title('Total Reward Distribution per IRIS Sort', fontsize=13, fontweight='bold')
                    _ax_rwbp.spines[['top', 'right']].set_visible(False)
                    _ax_rwbp.grid(axis='y', alpha=0.3)
                    _fig_rwbp.tight_layout()
                    _fig_rwbp.savefig(_perf_rw / "ablation_iris_total_reward_boxplot_FINAL.png", dpi=150)
                    plt.close(_fig_rwbp)
                    print(f"[ablation] Final Rewards boxplot -> {_perf_rw / 'ablation_iris_total_reward_boxplot_FINAL.png'}")

                # ── Final LR Boxplot ──────────────────────────────────────────
                import csv as _csv_mod
                _summary_root = _repo_root / "summary"
                _lr_data: dict[str, list[float]] = {}
                for _sort in _ABLATION_ORDER:
                    _sdir = _summary_root / f"summary_of_{_sort}"
                    if not _sdir.exists():
                        continue
                    _tables = _sdir / "summary_all"
                    # use fixed filename summary.csv
                    _csvs = [_tables / "summary.csv"] if (_tables / "summary.csv").exists() else []
                    if not _csvs:
                        continue
                    _vals = []
                    with open(_csvs[-1], newline="", encoding="utf-8") as _fh:
                        for _row in _csv_mod.DictReader(_fh):
                            # Skip 2nd+ CE rows (conjecture-level fields are blank)
                            if _row.get("conjecture_name", "").strip() == "":
                                continue
                            try:
                                _v = float(_row.get("final_lr", ""))
                                if _v > 0:
                                    _vals.append(_v)
                            except (ValueError, TypeError):
                                continue
                    if _vals:
                        _lr_data[_sort] = _vals

                if _lr_data:
                    _perf_lr = _repo_root / "Performance_Analysis" / "Final_LR"
                    _perf_lr.mkdir(parents=True, exist_ok=True)

                    _lr_labels = [s for s in _ABLATION_ORDER if s in _lr_data]
                    _lr_vals   = [_lr_data[s] for s in _lr_labels]

                    _fig_lr, _ax_lr = plt.subplots(figsize=(max(9, len(_lr_labels) * 1.4), 6))
                    _bp = _ax_lr.boxplot(
                        _lr_vals, labels=_lr_labels, patch_artist=True,
                        medianprops=dict(color='#E2724C', linewidth=2),
                        whiskerprops=dict(color='#555', linewidth=1.2),
                        capprops=dict(color='#555', linewidth=1.2),
                        flierprops=dict(marker='o', markerfacecolor='#aaa', markersize=4, linestyle='none'),
                    )
                    for _patch in _bp['boxes']:
                        _patch.set_facecolor('#a8c4e0')
                        _patch.set_alpha(0.85)

                    # annotate mean, median, min, max
                    for _i, (_lbl, _vs) in enumerate(zip(_lr_labels, _lr_vals), start=1):
                        _mn  = min(_vs)
                        _mx  = max(_vs)
                        _med = float(np.median(_vs))
                        _avg = float(np.mean(_vs))
                        _y_range = _ax_lr.get_ylim()[1] - _ax_lr.get_ylim()[0] if _ax_lr.get_ylim()[1] != _ax_lr.get_ylim()[0] else 1.0
                        _ax_lr.text(_i, _mx + _y_range * 0.01, f'max: {_mx:.2e}', ha='center', va='bottom', fontsize=7.5, color='#333')
                        _ax_lr.text(_i, _mn - _y_range * 0.01, f'min: {_mn:.2e}', ha='center', va='top',    fontsize=7.5, color='#333')
                        _ax_lr.text(_i + 0.32, _avg, f'mean: {_avg:.2e}', ha='left', va='center', fontsize=7.5, color='#1f77b4')
                        _ax_lr.text(_i + 0.32, _med, f'med: {_med:.2e}',  ha='left', va='center', fontsize=7.5, color='#E2724C')

                    _ax_lr.set_xlabel('IRIS Sort Combination', fontsize=11)
                    _ax_lr.set_ylabel('Final Learning Rate', fontsize=11)
                    _ax_lr.set_title('Final LR Distribution per IRIS Sort', fontsize=13, fontweight='bold')
                    _ax_lr.spines[['top', 'right']].set_visible(False)
                    _ax_lr.grid(axis='y', alpha=0.3)
                    _fig_lr.tight_layout()
                    _fig_lr.savefig(_perf_lr / "Final_LR_boxplot.png", dpi=150)
                    plt.close(_fig_lr)
                    print(f"[ablation] Final LR boxplot      -> {_perf_lr / 'Final_LR_boxplot.png'}")

                # ── helpers shared by all three plot blocks ───────────────────
                import csv as _csv_plots
                import pandas as _pd_plots

                def _get_main_csv(_sdir):
                    """Return summary_all/summary.csv for the given summary dir."""
                    _f = _sdir / "summary_all" / "summary.csv"
                    return _f if _f.exists() else None

                def _ep_plot_barchart(_iris_order, _total_vals, _out_path):
                    """plot_episodes.py: plot_barchart — exact copy."""
                    _fig, _ax = plt.subplots(figsize=(9, 5))
                    _max_val = max(_total_vals) if _total_vals else 1.0
                    _bars = _ax.bar(_iris_order, _total_vals, color="#4C8BE2",
                                    edgecolor="white", linewidth=0.8, width=0.55)
                    for _bar, _val in zip(_bars, _total_vals):
                        _ax.text(_bar.get_x() + _bar.get_width() / 2,
                                 _val + _max_val * 0.015, f"{int(_val):,}",
                                 ha="center", va="bottom", fontsize=9, color="#222")
                    _ax.set_xlabel("IRIS Sort Combination", fontsize=11)
                    _ax.set_ylabel("Total Episodes to Find CE", fontsize=11)
                    _ax.set_title("Total Episodes to Find CE per IRIS Sort", fontsize=13, fontweight="bold")
                    _ax.set_ylim(0, _max_val * 1.25)
                    _ax.spines[["top", "right"]].set_visible(False)
                    _fig.tight_layout()
                    _out_path.parent.mkdir(parents=True, exist_ok=True)
                    _fig.savefig(_out_path, dpi=150)
                    plt.close(_fig)
                    print(f"[ablation] {_out_path.name:45s} -> {_out_path}")

                def _ep_plot_boxplot(_iris_order, _per_vals, _out_path):
                    """plot_episodes.py: plot_boxplot — exact copy."""
                    _fig, _ax = plt.subplots(figsize=(9, 5))
                    _data = [_per_vals[l] for l in _iris_order]
                    _bp = _ax.boxplot(_data, labels=_iris_order, patch_artist=True,
                                      medianprops=dict(color="#E2724C", linewidth=2),
                                      whiskerprops=dict(color="#555"),
                                      capprops=dict(color="#555"),
                                      flierprops=dict(marker="o", markerfacecolor="#4C8BE2",
                                                      markersize=4, alpha=0.5, linestyle="none"))
                    for _patch in _bp["boxes"]:
                        _patch.set_facecolor("#4C8BE2"); _patch.set_alpha(0.6)
                    _ax.set_xlabel("IRIS Sort Combination", fontsize=11)
                    _ax.set_ylabel("Episodes to Find CE per Conjecture", fontsize=11)
                    _ax.set_title("Episodes-to-CE Distribution per IRIS Sort", fontsize=13, fontweight="bold")
                    _ax.spines[["top", "right"]].set_visible(False)
                    for _i, _d in enumerate(_data, start=1):
                        if not _d: continue
                        _s = _pd_plots.Series(_d)
                        _nudge = (_s.max() - _s.min()) * 0.02 if _s.max() != _s.min() else 1.0
                        for _y, _lbl, _va, _col, _wt in [
                            (_s.max() + _nudge,          f"max: {_s.max():.0f}",    "bottom", "#333",    "normal"),
                            (_s.mean(),                  f"mean: {_s.mean():.0f}",  "center", "#4C8BE2", "bold"),
                            (_s.median() - _nudge * 1.5, f"med: {_s.median():.0f}", "center", "#E2724C", "bold"),
                            (_s.min() - _nudge,          f"min: {_s.min():.0f}",    "top",    "#333",    "normal"),
                        ]:
                            _ax.text(_i + 0.28, _y, _lbl, ha="left", va=_va,
                                     fontsize=7, color=_col, fontweight=_wt)
                    _fig.tight_layout()
                    _fig.savefig(_out_path, dpi=150)
                    plt.close(_fig)
                    print(f"[ablation] {_out_path.name:45s} -> {_out_path}")

                def _tt_plot_barchart(_iris_order, _total_vals, _title, _ylabel, _out_path):
                    """plot_training_time.py: plot_barchart — exact copy."""
                    _fig, _ax = plt.subplots(figsize=(9, 5))
                    _max_val = max(_total_vals) if _total_vals else 1.0
                    _bars = _ax.bar(_iris_order, _total_vals, color="#4C8BE2",
                                    edgecolor="white", linewidth=0.8, width=0.55)
                    for _bar, _val in zip(_bars, _total_vals):
                        _ax.text(_bar.get_x() + _bar.get_width() / 2,
                                 _val + _max_val * 0.015, f"{_val:.2f}h",
                                 ha="center", va="bottom", fontsize=9, color="#222")
                    _ax.set_xlabel("IRIS Sort Combination", fontsize=11)
                    _ax.set_ylabel(_ylabel, fontsize=11)
                    _ax.set_title(_title, fontsize=13, fontweight="bold")
                    _ax.set_ylim(0, _max_val * 1.25)
                    _ax.spines[["top", "right"]].set_visible(False)
                    _fig.tight_layout()
                    _out_path.parent.mkdir(parents=True, exist_ok=True)
                    _fig.savefig(_out_path, dpi=150)
                    plt.close(_fig)
                    print(f"[ablation] {_out_path.name:45s} -> {_out_path}")

                def _tt_plot_boxplot(_iris_order, _per_vals, _title, _ylabel, _out_path):
                    """plot_training_time.py: plot_boxplot — exact copy."""
                    _fig, _ax = plt.subplots(figsize=(9, 5))
                    _data = [_per_vals[l] for l in _iris_order]
                    _bp = _ax.boxplot(_data, labels=_iris_order, patch_artist=True,
                                      medianprops=dict(color="#E2724C", linewidth=2),
                                      whiskerprops=dict(color="#555"),
                                      capprops=dict(color="#555"),
                                      flierprops=dict(marker="o", markerfacecolor="#4C8BE2",
                                                      markersize=4, alpha=0.5, linestyle="none"))
                    for _patch in _bp["boxes"]:
                        _patch.set_facecolor("#4C8BE2"); _patch.set_alpha(0.6)
                    _ax.set_xlabel("IRIS Sort Combination", fontsize=11)
                    _ax.set_ylabel(_ylabel, fontsize=11)
                    _ax.set_title(_title, fontsize=13, fontweight="bold")
                    _ax.spines[["top", "right"]].set_visible(False)
                    for _i, _d in enumerate(_data, start=1):
                        if not _d: continue
                        _s = _pd_plots.Series(_d)
                        _nudge = (_s.max() - _s.min()) * 0.02 if _s.max() != _s.min() else 0.01
                        for _y, _lbl, _va, _col, _wt in [
                            (_s.max() + _nudge,          f"max: {_s.max():.2f}",    "bottom", "#333",    "normal"),
                            (_s.mean(),                  f"mean: {_s.mean():.2f}",  "center", "#4C8BE2", "bold"),
                            (_s.median() - _nudge * 1.5, f"med: {_s.median():.2f}", "center", "#E2724C", "bold"),
                            (_s.min() - _nudge,          f"min: {_s.min():.2f}",    "top",    "#333",    "normal"),
                        ]:
                            _ax.text(_i + 0.28, _y, _lbl, ha="left", va=_va,
                                     fontsize=7, color=_col, fontweight=_wt)
                    _fig.tight_layout()
                    _fig.savefig(_out_path, dpi=150)
                    plt.close(_fig)
                    print(f"[ablation] {_out_path.name:45s} -> {_out_path}")

                _COMBOS_IR = {
                    "T":   lambda t, r, l: t,
                    "R":   lambda t, r, l: r,
                    "L":   lambda t, r, l: l,
                    "TR":  lambda t, r, l: t + r,
                    "TL":  lambda t, r, l: t + l,
                    "RL":  lambda t, r, l: r + l,
                    "TRL": lambda t, r, l: t + r + l,
                }
                _COLORS_IR = {
                    "T": "#4C8BE2", "R": "#E2724C", "L": "#2CA02C",
                    "TR": "#9467BD", "TL": "#E2C44C", "RL": "#17BECF", "TRL": "#D62728",
                }

                def _draw_iris_subplots(_records, _title_suffix, _out_path):
                    """plot_iris_vs_reward.py: draw_subplots — exact copy."""
                    if not _records: return
                    _fig2, _axes2 = plt.subplots(2, 4, figsize=(24, 11))
                    _flat = _axes2.flatten()
                    for _i, (_cname, _cfn) in enumerate(_COMBOS_IR.items()):
                        _ax2 = _flat[_i]
                        _xs2 = [_cfn(r["T"], r["R"], r["L"]) for r in _records]
                        _ys2 = [r["total_reward"] / 1000.0 for r in _records]
                        _col2 = _COLORS_IR[_cname]
                        _ax2.scatter(_xs2, _ys2, c=_col2, alpha=0.55, s=30,
                                     edgecolors='none', zorder=2)
                        _xs_a = np.array(_xs2); _ys_a = np.array(_ys2)
                        _slope2 = None
                        if len(_xs_a) > 2 and _xs_a.std() > 0:
                            _z2 = np.polyfit(_xs_a, _ys_a, 1)
                            _p2 = np.poly1d(_z2)
                            _xl2 = np.linspace(_xs_a.min(), _xs_a.max(), 300)
                            _ax2.plot(_xl2, _p2(_xl2), color=_col2, linewidth=1.5,
                                      linestyle='--', alpha=0.85,
                                      label=f"trend (slope={_z2[0]:.3f})")
                            _slope2 = _z2[0]
                        _ax2.set_title(
                            f"IRIS = {_cname}  (n={len(_xs2)})"
                            + (f"   slope={_slope2:.3f}" if _slope2 is not None else ""),
                            fontsize=11, fontweight='bold', color=_col2)
                        _ax2.set_xlabel(f'IRIS Score ({_cname})', fontsize=9)
                        _ax2.set_ylabel('Total Reward (×10³)', fontsize=9)
                        _ax2.spines[['top', 'right']].set_visible(False)
                        _ax2.grid(True, alpha=0.2, linewidth=0.5)
                        _ax2.legend(fontsize=8, framealpha=0.7)
                    _flat[7].axis('off')
                    _flat[7].text(
                        0.5, 0.5,
                        "IRIS combinations:\n\nT = T\nR = R\nL = L\n"
                        "TR = T + R\nTL = T + L\nRL = R + L\nTRL = T + R + L\n\n"
                        f"Group: {_title_suffix}\nTotal records: {len(_records)}",
                        transform=_flat[7].transAxes, ha='center', va='center', fontsize=11,
                        bbox=dict(boxstyle='round', facecolor='#f5f5f5', alpha=0.8))
                    _fig2.suptitle(f'IRIS Score vs Total Reward — {_title_suffix}',
                                   fontsize=14, fontweight='bold', y=1.01)
                    _fig2.tight_layout()
                    _out_path.parent.mkdir(parents=True, exist_ok=True)
                    _fig2.savefig(_out_path, dpi=150, bbox_inches='tight')
                    plt.close(_fig2)
                    print(f"[ablation] {_out_path.name:45s} -> {_out_path}")

                # ── plot_episodes ─────────────────────────────────────────────
                try:
                    _ep_total = {}; _ep_per = {}
                    for _sort in _ABLATION_ORDER:
                        _sdir = _summary_root / f"summary_of_{_sort}"
                        _csv_p = _get_main_csv(_sdir) if _sdir.exists() else None
                        if _csv_p is None: continue
                        _df_ep = _pd_plots.read_csv(_csv_p)
                        if "episode_to_find_first_ce" in _df_ep.columns:
                            # Only first CE row per conjecture has conjecture_name filled
                            _df_first = _df_ep[_df_ep["conjecture_name"].notna() & (_df_ep["conjecture_name"].astype(str).str.strip() != "")]
                            _ep_vals = _df_first["episode_to_find_first_ce"].dropna()
                            _ep_total[_sort] = int(_ep_vals.sum())
                            _ep_per[_sort]   = _ep_vals.tolist()
                            print(f"  [{_sort}] ep_to_first_ce={_ep_total[_sort]}")
                    _ep_labels = [s for s in _ABLATION_ORDER if s in _ep_total]
                    if _ep_labels:
                        _out_ep = _repo_root / "Performance_Analysis" / "Episodes"
                        _ep_plot_barchart(_ep_labels, [_ep_total[l] for l in _ep_labels],
                                          _out_ep / "Episodes_to_find_first_ce_barchart.png")
                        _ep_plot_boxplot(_ep_labels, _ep_per,
                                         _out_ep / "Episodes_to_find_first_ce_boxplot.png")
                except Exception as _e:
                    print(f"[ablation] Warning: plot_episodes failed ({_e})")

                # ── plot_training_time ────────────────────────────────────────
                try:
                    _tt_total = {}; _tt_per = {}
                    _ce_tt_total = {}; _ce_tt_per = {}
                    for _sort in _ABLATION_ORDER:
                        _sdir = _summary_root / f"summary_of_{_sort}"
                        _csv_p = _get_main_csv(_sdir) if _sdir.exists() else None
                        if _csv_p is None: continue
                        _df_tt = _pd_plots.read_csv(_csv_p)
                        if "total_training_time" not in _df_tt.columns: continue
                        _t_vals = _df_tt["total_training_time"].dropna()
                        _tt_total[_sort] = float(_t_vals.sum()) / 3600.0
                        _tt_per[_sort]   = [v / 60.0 for v in _t_vals.tolist()]
                        if "number_of_ce" in _df_tt.columns:
                            _nce = _pd_plots.to_numeric(_df_tt["number_of_ce"], errors="coerce")
                            _ce_vals = _df_tt.loc[_nce.fillna(0) > 0, "total_training_time"].dropna()
                            _ce_tt_total[_sort] = float(_ce_vals.sum()) / 3600.0
                            _ce_tt_per[_sort]   = [v / 60.0 for v in _ce_vals.tolist()]
                        print(f"  [{_sort}] total={_tt_total[_sort]:.2f}h | CE={_ce_tt_total.get(_sort, 0):.2f}h")
                    _tt_labels = [s for s in _ABLATION_ORDER if s in _tt_total]
                    if _tt_labels:
                        _out_tt = _repo_root / "Performance_Analysis" / "Total_time"
                        _tt_plot_barchart(_tt_labels, [_tt_total[l] for l in _tt_labels],
                                          "Total Training Time per IRIS Sort (hours)",
                                          "Total Training Time (hours)",
                                          _out_tt / "Total_training_time_barchart.png")
                        _tt_plot_boxplot(_tt_labels, _tt_per,
                                         "Training Time Distribution per IRIS Sort",
                                         "Training Time per Conjecture (minutes)",
                                         _out_tt / "Total_training_time_boxplot.png")
                        _tt_plot_barchart(_tt_labels, [_ce_tt_total.get(l, 0) for l in _tt_labels],
                                          "Total Time to Find First CE per IRIS Sort (hours)",
                                          "Total Time to Find First CE (hours)",
                                          _out_tt / "Total_training_time_to_find_first_ce_barchart.png")
                        _tt_plot_boxplot(_tt_labels, {l: _ce_tt_per.get(l, []) for l in _tt_labels},
                                         "Time-to-First-CE Distribution per IRIS Sort",
                                         "Time to Find First CE per Conjecture (minutes)",
                                         _out_tt / "Total_training_time_to_find_first_ce_boxplot.png")
                except Exception as _e:
                    print(f"[ablation] Warning: plot_training_time failed ({_e})")

                # ── plot_iris_vs_reward ───────────────────────────────────────
                try:
                    _all_records = []
                    for _sort in _ABLATION_ORDER:
                        _sdir = _summary_root / f"summary_of_{_sort}"
                        _csv_p = _get_main_csv(_sdir) if _sdir.exists() else None
                        if _csv_p is None: continue
                        with open(_csv_p, newline="", encoding="utf-8") as _fh:
                            for _row in _csv_plots.DictReader(_fh):
                                # Skip 2nd+ CE rows (conjecture-level fields are blank)
                                if _row.get("conjecture_name", "").strip() == "":
                                    continue
                                try:
                                    _all_records.append({
                                        # Column is "total_reward(x10³)"; multiply back to full scale
                                        "total_reward": float(_row.get("total_reward(x10³)", 0) or 0) * 1000,
                                        "ce_rate":    float(_row.get("ce_rate",    0) or 0),
                                        "T":          float(_row.get("T", 0) or 0),
                                        "R":          float(_row.get("R", 0) or 0),
                                        "L":          float(_row.get("L", 0) or 0),
                                        "source":     _sort,
                                    })
                                except (ValueError, TypeError):
                                    pass
                    print(f"\n  全部: {len(_all_records)} 条")
                    _ce_only_r = [r for r in _all_records if r["ce_rate"] >  0]
                    _no_ce_r   = [r for r in _all_records if r["ce_rate"] == 0]
                    print(f"  CE only: {len(_ce_only_r)} 条 | No CE: {len(_no_ce_r)} 条\n")
                    _out_ir = _repo_root / "Performance_Analysis" / "ablation_test_iris_rewards"
                    _draw_iris_subplots(_ce_only_r,   "CE only (ce_rate > 0)", _out_ir / "iris_subplots_ce_only.png")
                    _draw_iris_subplots(_no_ce_r,     "No CE  (ce_rate == 0)", _out_ir / "iris_subplots_no_ce.png")
                    _draw_iris_subplots(_all_records, "All records",           _out_ir / "iris_subplots_all.png")
                except Exception as _e:
                    print(f"[ablation] Warning: plot_iris_vs_reward failed ({_e})")

            except Exception as _exc:
                print(f"[ablation] Warning: final chart failed ({_exc})")

        else:
            # ── Single run ───────────────────────────────────────────────────
            results, results_dir = run_loaded_conjectures(
                source=args.source,
                episodes=args.episodes,
                max_nodes_cap=args.max_nodes,
                end_on_caps=end_on_caps,
                target_names=args.target_names,
                exit_on_first_ce=args.exit_on_first_ce,
                update_steps=args.update_steps,
                iris_sort=args.iris_sort,
            )
            print(f"\nDone: {results_dir}")

            # ── Save ablation data + redraw charts ────────────────────────────
            try:
                _repo_root = Path(__file__).resolve().parents[1]

                # CE Rate
                _perf_ce = _repo_root / "Performance_Analysis" / "ablation_test_iris_ce"
                _perf_ce.mkdir(parents=True, exist_ok=True)
                _data_file_ce = _perf_ce / "ablation_data.json"
                _all_runs = json.load(open(_data_file_ce)) if _data_file_ce.exists() else {}

                _rates   = [res.get("metrics", {}).get("ce_rate",    0.0) for _, res in results]
                _rewards = [sum(res.get("episode_rewards", []) or []) for _, res in results]
                _mean_ce_rate    = float(np.mean(_rates))   if _rates   else 0.0
                _mean_total_reward = float(np.mean(_rewards)) if _rewards else 0.0
                _n_conjectures   = len(_rates)
                _n_with_ce       = sum(1 for r in _rates if r > 0)

                _all_runs[args.iris_sort] = {
                    "iris_sort":        args.iris_sort,
                    "mean_ce_rate":     _mean_ce_rate,
                    "mean_total_reward":  _mean_total_reward,
                    "n_conjectures":    _n_conjectures,
                    "n_with_ce":        _n_with_ce,
                    "per_conjecture": {
                        name: {
                            "ce_rate":      res.get("metrics", {}).get("ce_rate", 0.0),
                            "total_reward": sum(res.get("episode_rewards", []) or []),
                        }
                        for name, res in results
                    },
                    "run_timestamp": datetime.now().strftime("%Y%m%d_%H%M%S"),
                }
                with open(_data_file_ce, "w") as _fh:
                    json.dump(_all_runs, _fh, indent=2)

                # Rewards data (saved for FINAL chart after all 7 runs)
                _perf_rw = _repo_root / "Performance_Analysis" / "ablation_test_iris_rewards"
                _perf_rw.mkdir(parents=True, exist_ok=True)
                _data_file_rw = _perf_rw / "ablation_data.json"
                _rewards_data = json.load(open(_data_file_rw)) if _data_file_rw.exists() else {}
                _rewards_data[args.iris_sort] = {
                    "iris_sort":       args.iris_sort,
                    "mean_total_reward": _mean_total_reward,
                    "n_conjectures":   _n_conjectures,
                    "per_conjecture": {
                        name: sum(res.get("episode_rewards", []) or [])
                        for name, res in results
                    },
                    "run_timestamp": datetime.now().strftime("%Y%m%d_%H%M%S"),
                }
                with open(_data_file_rw, "w") as _fh:
                    json.dump(_rewards_data, _fh, indent=2)
                print(f"[ablation] Rewards data   -> {_data_file_rw}")

            except Exception as _exc:
                print(f"[ablation] Warning: chart/data saving failed ({_exc})")