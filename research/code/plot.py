"""
plot.py -- generic figure helper for the section scripts (line / errorbar plots).

Keeps the run scripts thin: hand it x, one or more y-series, and labels.
"""
from __future__ import annotations

import os

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

_PALETTE = ["#1f4e8c", "#b03030", "#2e7d32", "#8c6d1f"]


def line(path, x, series, *, xlabel="", ylabel="", title="",
         vline=None, vline_label=None, vspan=None, figsize=(6.4, 4.2)):
    """Plot one or more y-series vs ``x`` (optional error bars) and save to ``path``.

    ``series`` is a list of dicts, each {y, yerr?, label?, color?, marker?}.
    ``vline`` draws a dashed vertical marker (labelled ``vline_label``); ``vspan``
    shades an x-interval (lo, hi)."""
    fig, ax = plt.subplots(figsize=figsize)
    if vspan is not None:
        ax.axvspan(vspan[0], vspan[1], color="#e8f0ff", zorder=0)
    if vline is not None:
        ax.axvline(vline, color="#888", ls="--", lw=1, label=vline_label)
    for i, s in enumerate(series):
        ax.errorbar(x, s["y"], yerr=s.get("yerr"), marker=s.get("marker", "o"),
                    color=s.get("color", _PALETTE[i % len(_PALETTE)]), lw=1.8,
                    capsize=3, label=s.get("label"))
    ax.set_xlabel(xlabel)
    ax.set_ylabel(ylabel)
    ax.set_title(title)
    if vline_label or any(s.get("label") for s in series):
        ax.legend(loc="best", fontsize=8)
    fig.tight_layout()
    os.makedirs(os.path.dirname(path), exist_ok=True)
    fig.savefig(path, dpi=150)
    plt.close(fig)
    return path
