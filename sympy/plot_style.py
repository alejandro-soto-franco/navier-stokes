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
    mpl.rcParams.update({
        # LaTeX rendering
        "text.usetex": True,
        "text.latex.preamble": (
            r"\usepackage{lmodern}"
            r"\usepackage{amsmath}"
            r"\usepackage{amssymb}"
            r"\newcommand{\dd}{\mathrm{d}}"
            r"\newcommand{\R}{\mathbb{R}}"
            r"\newcommand{\Lsig}{L^2_\sigma}"
            r"\newcommand{\BS}{\mathcal{K}}"
        ),
        # Font
        "font.family": "serif",
        "font.serif": ["Computer Modern Roman"],
        "font.size": 11,
        "axes.labelsize": 11,
        "axes.titlesize": 11,
        "xtick.labelsize": 10,
        "ytick.labelsize": 10,
        "legend.fontsize": 10,
        # Legend
        "legend.frameon": True,
        "legend.framealpha": 0.85,
        "legend.edgecolor": "0.8",
        "legend.borderpad": 0.4,
        # Lines
        "lines.linewidth": 1.4,
        "lines.markersize": 4.5,
        # Axes (ticks inside, all four spines)
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
        # Figure / save
        "figure.dpi": 150,
        "savefig.dpi": 300,
        "savefig.bbox": "tight",
        "savefig.pad_inches": 0.02,
    })


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


def save_panel(fig, name, dpi=300):
    """Save figure to ../latex/figures/ as both PDF and PNG."""
    out = Path(__file__).resolve().parent.parent / "latex" / "figures"
    out.mkdir(parents=True, exist_ok=True)
    fig.savefig(out / f"{name}.pdf", dpi=dpi)
    fig.savefig(out / f"{name}.png", dpi=dpi)
    print(f"Saved {out / name}.{{pdf,png}}")
