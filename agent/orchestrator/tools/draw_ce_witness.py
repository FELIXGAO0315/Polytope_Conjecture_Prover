#!/usr/bin/env python3
"""Render the witness graph stored in a CE JSON as a planar drawing.

Usage:
    python agent/orchestrator/tools/draw_ce_witness.py output/conjecture_with_ce/C5/C5.json
    python agent/orchestrator/tools/draw_ce_witness.py output/conjecture_with_ce/C5/C5.json -o /tmp/c5.png

The witness is drawn with its planar embedding, so every interior region of
the picture is an actual face of the polytope (the outer region is the
remaining face). The orchestrator calls render_witness() automatically when
it writes a CE JSON, placing <Cx>_witness.png next to the JSON.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import networkx as nx


def render_witness(json_path: Path | str, out_path: Path | str | None = None,
                   labels: bool = False) -> Path:
    """Draw the witness graph of a CE JSON; returns the PNG path."""
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    path = Path(json_path)
    data = json.loads(path.read_text())
    ce = data.get("counterexample", {})
    w = ce.get("witness_graph")
    if not w:
        raise ValueError(
            f"{path} has no counterexample.witness_graph — this CE predates "
            f"witness persistence; re-run the pipeline for this conjecture")

    G = nx.Graph()
    G.add_edges_from(tuple(e) for e in w["edges"])
    planar, emb = nx.check_planarity(G)
    pos = nx.planar_layout(G) if planar else nx.spring_layout(G, seed=0)

    plt.figure(figsize=(11, 11))
    nx.draw_networkx_edges(G, pos, width=0.9)
    nx.draw_networkx_nodes(G, pos, node_size=160 if labels else 60,
                           node_color="#1f77b4")
    if labels:
        nx.draw_networkx_labels(G, pos, font_size=6, font_color="white")

    pv = {k: v for k, v in ce.items()
          if k.startswith("p") and k[1:].isdigit() and v}
    plt.title(f"{data.get('conjecture_id', path.stem)} witness — "
              f"V={G.number_of_nodes()}, E={G.number_of_edges()}, "
              f"f2={ce.get('f2', '?')}  |  " +
              ", ".join(f"{k}={v}" for k, v in sorted(pv.items(),
                                                      key=lambda x: int(x[0][1:]))))
    plt.axis("off")
    out = Path(out_path) if out_path else path.with_name(f"{path.stem}_witness.png")
    plt.savefig(out, dpi=150, bbox_inches="tight")
    plt.close()
    return out


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("ce_json", help="CE JSON file (output/conjecture_with_ce/Cx/Cx.json)")
    ap.add_argument("-o", "--out", default=None, help="output PNG (default: <Cx>_witness.png next to the JSON)")
    ap.add_argument("--labels", action="store_true", help="draw vertex labels")
    args = ap.parse_args()
    try:
        print(render_witness(args.ce_json, args.out, labels=args.labels))
    except ValueError as exc:
        raise SystemExit(str(exc))


if __name__ == "__main__":
    main()
