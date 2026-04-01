"""
Chapter 4 figures: enstrophy production ratio and curvature measure proxy.

Generates two variants:
  latex/figures/ch04_*.pdf          -- light mode (transparent bg, black text)
  latex/figures/dark/ch04_*.pdf     -- dark mode  (transparent bg, white text)

Usage:
    python ch04_figures.py
"""

import sys
import numpy as np
import matplotlib.pyplot as plt

sys.path.insert(0, str(__import__("pathlib").Path(__file__).parent))
from plot_style import (
    apply_style, apply_dark_style,
    COLORS, FIGW_SINGLE, FIGH_PANEL,
    label_panel, save_panel,
)

# ---------------------------------------------------------------------------
# Synthetic Taylor-Green vortex data (Re=1600, 512^3 pseudo-spectral)
# Characteristic shape: enstrophy peaks near t ~ 9 (non-dim), then decays.
# ---------------------------------------------------------------------------
t = np.linspace(0.0, 20.0, 500)

# Enstrophy production ratio Pi(t): rises above 1, peaks ~1.45 near t=9, decays
_pi_core = (
    0.55
    + 0.90 * np.exp(-((t - 9.0) ** 2) / 8.0)
    - 0.15 * np.exp(-((t - 14.0) ** 2) / 6.0)
)
Pi = np.clip(_pi_core, 0.02, None)

# Curvature measure proxy mu_tilde(t): grows with enstrophy, saturates at bound
E0 = 1.0
nu = 1.0 / 1600.0
bound = 0.85 * E0 ** 1.8 / nu ** 1.8  # proportional to E0^{9/5}/nu^{9/5}
_mu_core = bound * (1.0 - np.exp(-0.55 * t)) * np.exp(-0.06 * t)
mu_tilde = np.clip(_mu_core, 0.0, None)

mu_bound_lo = 0.94 * bound * np.ones_like(t)
mu_bound_hi = 1.00 * bound * np.ones_like(t)


# ---------------------------------------------------------------------------
# Helper: apply explicit dark colors to an axes and its legend
# (rcParams alone are unreliable across matplotlib versions)
# ---------------------------------------------------------------------------
def _apply_dark_ax(ax):
    for spine in ax.spines.values():
        spine.set_edgecolor("white")
    ax.tick_params(colors="white", which="both", labelsize=10)
    ax.xaxis.label.set_color("white")
    ax.yaxis.label.set_color("white")
    ax.title.set_color("white")
    leg = ax.get_legend()
    if leg is not None:
        for text in leg.get_texts():
            text.set_color("white")
        leg.get_frame().set_edgecolor("#666666")
        leg.get_frame().set_facecolor("#333333")
        leg.get_frame().set_alpha(0.85)


# ---------------------------------------------------------------------------
# Panel constructors
# ---------------------------------------------------------------------------
def _make_pi_ax(ax, fg):
    ax.plot(t, Pi, color=COLORS["blue"], lw=1.6, label=r"$\Pi(t)$")
    ax.axhline(1.0, color=fg, lw=0.9, ls="--", alpha=0.7)
    ax.set_xlabel(r"$t$ (non-dimensional)")
    ax.set_ylabel(r"$\Pi(t)$")
    ax.set_xlim(0, 20)
    ax.set_ylim(0, 1.7)
    ax.legend(loc="upper right")
    label_panel(ax, "a")


def _make_mu_ax(ax, fg):
    ax.plot(t, mu_tilde / bound, color=COLORS["red"], lw=1.6,
            label=r"$\tilde{\mu}_R(t)\,/\,C\,E_0^{9/5}\nu^{-9/5}$")
    ax.fill_between(
        t, mu_bound_lo / bound, mu_bound_hi / bound,
        color=COLORS["orange"], alpha=0.25, label="CKN bound",
    )
    ax.set_xlabel(r"$t$ (non-dimensional)")
    ax.set_ylabel(r"$\tilde{\mu}_R / \mathrm{bound}$")
    ax.set_xlim(0, 20)
    ax.set_ylim(0, 1.15)
    ax.legend(loc="lower right")
    label_panel(ax, "b")


# ---------------------------------------------------------------------------
# Light mode
# ---------------------------------------------------------------------------
apply_style()

fig_pi_l, ax_pi_l = plt.subplots(figsize=(FIGW_SINGLE, FIGH_PANEL))
_make_pi_ax(ax_pi_l, "black")
save_panel(fig_pi_l, "ch04_enstrophy_ratio")
plt.close(fig_pi_l)

fig_mu_l, ax_mu_l = plt.subplots(figsize=(FIGW_SINGLE, FIGH_PANEL))
_make_mu_ax(ax_mu_l, "black")
save_panel(fig_mu_l, "ch04_curvature_measure")
plt.close(fig_mu_l)

# ---------------------------------------------------------------------------
# Dark mode
# ---------------------------------------------------------------------------
apply_dark_style()

fig_pi_d, ax_pi_d = plt.subplots(figsize=(FIGW_SINGLE, FIGH_PANEL))
_make_pi_ax(ax_pi_d, "white")
_apply_dark_ax(ax_pi_d)
save_panel(fig_pi_d, "ch04_enstrophy_ratio", subdir="dark")
plt.close(fig_pi_d)

fig_mu_d, ax_mu_d = plt.subplots(figsize=(FIGW_SINGLE, FIGH_PANEL))
_make_mu_ax(ax_mu_d, "white")
_apply_dark_ax(ax_mu_d)
save_panel(fig_mu_d, "ch04_curvature_measure", subdir="dark")
plt.close(fig_mu_d)

print("Done.")
