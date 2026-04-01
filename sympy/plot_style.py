"""
Shared matplotlib style for 3D Navier-Stokes book figures.

Based on mars-lnp PRE style, adapted for A4 book geometry.

Usage:
    from plot_style import apply_style, COLORS, save_panel, label_panel
    apply_style()
"""

import matplotlib as mpl
import matplotlib.pyplot as plt
from pathlib import Path

# ---------------------------------------------------------------------------
# Figure dimensions (A4 book, 11pt, ~6.27in text width)
# ---------------------------------------------------------------------------
FIGW_SINGLE = 5.0       # single panel (~80% text width)
FIGW_DOUBLE = 6.2       # full-width figure
FIGH_PANEL  = 3.5       # single panel height

# ---------------------------------------------------------------------------
# Wong 2011 colorblind-safe palette
# ---------------------------------------------------------------------------
COLORS = {
    "blue":   "#0072B2",
    "red":    "#D55E00",
    "green":  "#009E73",
    "orange": "#E69F00",
    "purple": "#CC79A7",
    "sky":    "#56B4E9",
    "black":  "#000000",
    "gray":   "#999999",
}
COLOR_CYCLE = [
    "#0072B2", "#D55E00", "#009E73",
    "#E69F00", "#CC79A7", "#56B4E9",
]

# ---------------------------------------------------------------------------
# Apply style
# ---------------------------------------------------------------------------
def apply_style():
    """Light-mode style: transparent background, black text and axes."""
    params = dict(_STYLE_BASE)
    params.update({
        "figure.facecolor": "none",
        "axes.facecolor": "none",
        "legend.edgecolor": "0.8",
        "savefig.transparent": True,
    })
    mpl.rcParams.update(params)


_LATEX_PREAMBLE = (
    r"\usepackage{lmodern}"
    r"\usepackage{amsmath}"
    r"\usepackage{amssymb}"
    r"\newcommand{\dd}{\mathrm{d}}"
    r"\newcommand{\R}{\mathbb{R}}"
    r"\newcommand{\Lsig}{L^2_\sigma}"
    r"\newcommand{\BS}{\mathcal{K}}"
)

_STYLE_BASE = {
    "text.usetex": True,
    "text.latex.preamble": _LATEX_PREAMBLE,
    "font.family": "serif",
    "font.serif": ["Computer Modern Roman"],
    "font.size": 11,
    "axes.labelsize": 11,
    "axes.titlesize": 11,
    "xtick.labelsize": 10,
    "ytick.labelsize": 10,
    "legend.fontsize": 10,
    "legend.frameon": True,
    "legend.framealpha": 0.85,
    "legend.borderpad": 0.4,
    "lines.linewidth": 1.4,
    "lines.markersize": 4.5,
    "axes.linewidth": 0.8,
    "xtick.major.width": 0.8,
    "ytick.major.width": 0.8,
    "xtick.minor.width": 0.5,
    "ytick.minor.width": 0.5,
    "xtick.direction": "in",
    "ytick.direction": "in",
    "xtick.top": True,
    "ytick.right": True,
    "axes.prop_cycle": mpl.cycler(color=COLOR_CYCLE),
    "figure.dpi": 150,
    "savefig.dpi": 300,
    "savefig.bbox": "tight",
    "savefig.pad_inches": 0.02,
}


def apply_dark_style():
    """Dark-mode variant: transparent background, white text and axes."""
    params = dict(_STYLE_BASE)
    params.update({
        "figure.facecolor": "none",
        "axes.facecolor": "none",
        "axes.edgecolor": "white",
        "text.color": "white",
        "axes.labelcolor": "white",
        "xtick.color": "white",
        "ytick.color": "white",
        "legend.edgecolor": "#666666",
        "legend.facecolor": "#333333",
        "legend.labelcolor": "white",
        "savefig.transparent": True,
    })
    mpl.rcParams.update(params)


def label_panel(ax, letter, x=-0.12, y=1.06, fontsize=12, fontweight="bold"):
    """Add a panel label like (a), (b) to an axes."""
    ax.text(
        x, y, f"({letter})",
        transform=ax.transAxes,
        fontsize=fontsize,
        fontweight=fontweight,
        va="top",
        ha="left",
    )


def save_panel(fig, name, dpi=300, subdir=None):
    """Save figure to ../latex/figures/[subdir]/ as both PDF and PNG."""
    base = Path(__file__).resolve().parent.parent / "latex" / "figures"
    out = base / subdir if subdir else base
    out.mkdir(parents=True, exist_ok=True)
    fig.savefig(out / f"{name}.pdf", dpi=dpi)
    fig.savefig(out / f"{name}.png", dpi=dpi)
    print(f"Saved {out / name}.{{pdf,png}}")
