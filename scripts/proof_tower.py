#!/usr/bin/env python3
"""Render the ground-truth proof tower: every lemma as a node in its tier,
every real cross-reference as an edge, from `0 + n = n` to rsa_correctness."""
import re
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.collections import LineCollection

ROOT = Path(__file__).resolve().parent.parent
TIER_RE = re.compile(r"Tier(\d+)_")
DECL_RE = re.compile(r"^(?:theorem|lemma)\s+([A-Za-z0-9_.']+)", re.M)

TIER_LABELS = {
    1: "naturals", 2: "ordering", 3: "div / mod", 4: "divisibility",
    5: "lists", 6: "gcd", 7: "primes", 8: "Fermat's little theorem",
    9: "Bezout", 10: "CRT", 11: "RSA bridge", 12: "RSA correctness",
}

files = sorted(ROOT.glob("ProofFarm/Tier*.lean"),
               key=lambda p: int(TIER_RE.search(p.name).group(1)))

decls = {}          # name -> (tier, index_in_tier)
tier_counts = {}
bodies = {}         # name -> proof text that follows the declaration
for f in files:
    tier = int(TIER_RE.search(f.name).group(1))
    text = f.read_text()
    matches = list(DECL_RE.finditer(text))
    for i, m in enumerate(matches):
        name = m.group(1).split(".")[-1]
        decls[name] = (tier, tier_counts.get(tier, 0))
        tier_counts[tier] = tier_counts.get(tier, 0) + 1
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        bodies[name] = text[m.end():end]

word = re.compile(r"[A-Za-z0-9_.']+")
edges = []
for name, body in bodies.items():
    t_to = decls[name][0]
    used = set()
    for tok in word.findall(body):
        tok = tok.split(".")[-1]
        if tok in decls and tok != name and tok not in used:
            t_from = decls[tok][0]
            if t_from <= t_to:
                edges.append((tok, name))
                used.add(tok)

# layout: tier = row, nodes spread across the row, narrower toward the top
pos = {}
for name, (tier, idx) in decls.items():
    n = tier_counts[tier]
    width = 9.0 * (n / max(tier_counts.values())) ** 0.55 + 0.8
    x = (idx - (n - 1) / 2) / max(n - 1, 1) * width
    pos[name] = (x, tier)
pos["rsa_correctness"] = (0.0, 12.85)

fig, ax = plt.subplots(figsize=(12, 14), dpi=200)
fig.patch.set_facecolor("#0b0e14")
ax.set_facecolor("#0b0e14")

segs, colors, widths = [], [], []
for a, b in edges:
    (x1, y1), (x2, y2) = pos[a], pos[b]
    same = y1 == y2
    segs.append([(x1, y1 + 0.07), (x2, y2 - (0.07 if not same else -0.07))])
    if b == "rsa_correctness":
        colors.append((1.0, 0.83, 0.30, 0.85))
        widths.append(1.4)
    else:
        colors.append((0.42, 0.62, 0.92, 0.14 if same else 0.26))
        widths.append(0.7)
ax.add_collection(LineCollection(segs, colors=colors, linewidths=widths, zorder=1))

for name, (x, y) in pos.items():
    if name == "rsa_correctness":
        continue
    ax.scatter(x, y, s=26, color="#7fb4ff", edgecolors="#cfe3ff",
               linewidths=0.4, zorder=3)

cx, cy = pos["rsa_correctness"]
ax.scatter(cx, cy, s=420, marker="*", color="#ffd34d",
           edgecolors="#fff3c4", linewidths=1.2, zorder=5)
ax.annotate("rsa_correctness", (cx, cy), xytext=(0, 16),
            textcoords="offset points", ha="center",
            color="#ffd34d", fontsize=13, fontweight="bold")

for tier, label in TIER_LABELS.items():
    n = tier_counts[tier]
    xs = [pos[d][0] for d, (t, _) in decls.items() if t == tier]
    ax.text(max(xs) + 0.8, tier, f"{label}  ·  {n}",
            color="#8fa3bf", fontsize=10, va="center", ha="left")

base = [d for d, (t, _) in decls.items() if t == 1]
bx = min(pos[d][0] for d in base)
ax.text(0, 0.25, "0 + n = n", color="#9fd49f", fontsize=12,
        ha="center", style="italic")

ax.text(0, 14.15, "the proof tower under RSA",
        color="#e8eef7", fontsize=19, ha="center", fontweight="bold")
ax.text(0, 13.78, "196 machine-checked lemmas · 12 tiers · 0 sorry · 0 dependencies · Lean 4",
        color="#8fa3bf", fontsize=11, ha="center")

ax.set_xlim(-8.5, 12.5)
ax.set_ylim(-0.2, 14.6)
ax.axis("off")
fig.tight_layout()
out = ROOT / "paper" / "proof_tower.png"
fig.savefig(out, facecolor=fig.get_facecolor(), bbox_inches="tight")
print(f"nodes={len(decls)} edges={len(edges)} -> {out}")
