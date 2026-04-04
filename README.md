# On the Regularity of Three-Dimensional Navier-Stokes Solutions

[![Lean 4](https://img.shields.io/badge/Lean_4-v4.29.0--rc8-blue?logo=data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNCAyNCI+PHBhdGggZmlsbD0id2hpdGUiIGQ9Ik0xMiAyTDIgMjJoMjBMMTIgMnoiLz48L3N2Zz4=)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/Mathlib4-v4.29.0--rc8_(fork)-blue)](https://github.com/alejandro-soto-franco/mathlib4)
[![SymPy](https://img.shields.io/badge/SymPy-verified-brightgreen?logo=python&logoColor=white)](https://www.sympy.org/)
[![LaTeX](https://img.shields.io/badge/LaTeX-book_class-orange?logo=latex&logoColor=white)](https://www.latex-project.org/)
[![License](https://img.shields.io/badge/License-All_Rights_Reserved-red)](https://github.com/alejandro-soto-franco/navier-stokes/blob/master/LICENSE)
[![Chapter 1](https://img.shields.io/badge/Ch_1-Foundations_%E2%9C%93-brightgreen)](#chapter-status)
[![Chapter 2](https://img.shields.io/badge/Ch_2-Leray--Hopf_%E2%9C%93-brightgreen)](#chapter-status)
[![Chapter 3](https://img.shields.io/badge/Ch_3-Biot--Savart_%E2%9C%93-brightgreen)](#chapter-status)
[![Chapter 4](https://img.shields.io/badge/Ch_4-Curvature_%E2%9C%93-brightgreen)](#chapter-status)
[![Chapter 5](https://img.shields.io/badge/Ch_5-Topology-yellow)](#chapter-status)
[![Chapter 6](https://img.shields.io/badge/Ch_6-Obstruction-yellow)](#chapter-status)
[![Chapter 7](https://img.shields.io/badge/Ch_7-Singularity-yellow)](#chapter-status)
[![Dark Mode](https://img.shields.io/badge/Dark_Mode-WCAG_AA-blueviolet)](#compilation)
[![Lean CI](https://github.com/alejandro-soto-franco/navier-stokes/actions/workflows/lean.yml/badge.svg)](https://github.com/alejandro-soto-franco/navier-stokes/actions/workflows/lean.yml)
[![Build](https://img.shields.io/badge/Lean_Build-2770_jobs-informational)](#lean-formalisation)
[![Sorry Count](https://img.shields.io/badge/sorry-17_total-yellow)](#lean-formalisation)
[![Proved](https://img.shields.io/badge/Proved-14_theorems-brightgreen)](#proven-theorems)

A geometric approach to the Clay Millennium regularity problem for the 3D incompressible Navier-Stokes equations, via the Biot-Savart connection on the divergence-free bundle.

**Author:** Alejandro José Soto Franco

## Three-Track Architecture

Every chapter is developed simultaneously along three parallel verification tracks:

| Track | Tool | Purpose |
|-------|------|---------|
| **Formal verification** | Lean 4 + Mathlib | Type-checked definitions, theorem statements, and proofs |
| **Theory** | LaTeX + SymPy | Self-contained mathematical narrative with symbolic cross-checks |
| **Numerics** | Python/Rust | Computational verification of geometric predictions (later chapters) |

The tracks are reconciled at chapter boundaries via sync documents in `sync/`.

## Chapter Status

| Chapter | Title | Lean | LaTeX | SymPy | Sync |
|---------|-------|------|-------|-------|------|
| 1 | Functional Analytic Foundations | 17 defs, 10 proved, 4 sorry | Complete | 8/8 pass | [Passed](sync/ch01-foundations.md) |
| 2 | Leray-Hopf Weak Solutions | 12 defs, 4 proved, 12 sorry | Complete | 13/13 pass | [Passed](sync/ch02-leray-hopf.md) |
| 3 | The Biot-Savart Connection | Stubs | Complete (64pp) | 23/23 pass | -- |
| 4 | Curvature of the Flow | -- | Draft complete | 14/14 pass | -- |
| 5 | Topological Constraints | Stubs | In progress | Planned | -- |
| 6 | The Obstruction Theorem | Stubs | In progress | Planned | -- |
| 7 | Singularity Analysis | -- | In progress | Planned | -- |

## Repository Structure

```
3d-navier-stokes/
  latex/                  LaTeX source (book class, biber bibliography)
    main.tex              Light mode entry point
    main-dark.tex         Dark mode entry point (WCAG AA compliant)
    darkmode.sty          Dark mode colour scheme package
    preamble.tex          Shared preamble (packages, macros)
    sections/             Chapter .tex files
    appendices/           Appendix .tex files
    Makefile              Build targets: make all | make light | make dark
  lean/                   Lean 4 formalisation (pinned to Mathlib4 fork)
    lakefile.toml         Dependency config (commit-pinned fork of Mathlib4)
    NavierStokes/
      Foundations/         Ch1: Sobolev spaces, embeddings, Helmholtz decomposition
      LerayHopf/           Ch2: Weak solutions, trilinear form, energy inequality
      BiotSavart/          Ch3: Biot-Savart connection (stubs)
      Topology/            Ch5: Topological constraints (stubs)
      Obstruction/         Ch6: Obstruction theorem (stubs)
  sympy/                  Symbolic verification scripts
    ch01_sobolev_exponents.py
    ch01_helmholtz_verify.py
    ch02_leray_hopf_verify.py
    ch03_biot_savart_verify.py
    ch04_curvature_verify.py
    ch04_figures.py         ch04 figure generator (light + dark variants)
    plot_style.py           shared matplotlib style (LaTeX, transparent, dark mode)
  sync/                   Cross-track reconciliation documents
  numerics/               Numerical solvers (planned)
```

## Lean Formalisation

The Lean 4 formalisation builds against a [pinned fork of Mathlib4](https://github.com/alejandro-soto-franco/mathlib4) (commit `698d2b68`, based on `v4.29.0-rc8`) and compiles with 2787 jobs, 0 errors. The fork allows adding custom tooling (Sobolev spaces, embedding infrastructure) that can be PR'd back to upstream Mathlib as the project matures. The `lakefile.toml` pins to exact commit hashes for reproducible builds.

### Proven Theorems

| Theorem | File | Description |
|---------|------|-------------|
| `weakPartialDeriv_unique` | `Foundations/WeakDerivative.lean` | Weak partial derivatives are unique a.e., via the fundamental lemma of the calculus of variations |
| `sobolevConjugate_gt` | `Foundations/SobolevEmbedding.lean` | The Sobolev conjugate exponent p* > p for 1 <= p < n |
| `sobolevConjugate_inv` | `Foundations/SobolevEmbedding.lean` | The dimensional relation 1/p* = 1/p - 1/n |
| `sobolevH1InnerProduct_comm` | `Foundations/SobolevSpace.lean` | Symmetry of the H^1 inner product |
| `l2sigma_closed_under_l2_convergence` | `Foundations/DivFreeSpace.lean` | L²σ is closed under L² convergence, via Holder (Cauchy-Schwarz) and `tendsto_nhds_unique` |
| `trilinearForm_antisymmetric` | `LerayHopf/TrilinearForm.lean` | b(u,v,v) = 0 for distributionally divergence-free u and smooth compactly-supported v, via per-component test functions phi_k = v_k^2 |
| `l2sigmaSubmodule_isSeqClosed` | `Foundations/HelmholtzProjection.lean` | Sequential closedness of L²σ; norm bridge via `L2.inner_def` and `real_inner_self_eq_norm_sq` |
| `l2sigmaSubmodule_isClosed` | `Foundations/HelmholtzProjection.lean` | Topological closedness of L²σ via sequential closedness and metric structure of L² |
| `lerayProjectorLp_idempotent` | `Foundations/HelmholtzProjection.lean` | P(P(f)) = P(f), via `starProjection_eq_self_iff.mpr` |
| `lerayProjectorLp_selfAdjoint` | `Foundations/HelmholtzProjection.lean` | ⟪Pf, g⟫ = ⟪f, Pg⟫, via `inner_starProjection_left_eq_right` |
| `helmholtz_l2_decomposition` | `Foundations/HelmholtzProjection.lean` | f = Pf + (f - Pf) with Pf in L²σ and ⟪Pf, f-Pf⟫ = 0, via `starProjection_inner_eq_zero` |
| `galerkinRHS_locallyLipschitz` | `LerayHopf/GalerkinApproximation.lean` | The Galerkin ODE RHS is locally Lipschitz, via `ContDiff.of_le (by norm_cast)` downgrading C^∞ to C^1 |
| `galerkinVelocity_smooth` | `LerayHopf/GalerkinApproximation.lean` | The reconstructed velocity u_N = ∑_k c_k w_k is C^∞, via `ContDiff.sum` and `ContDiff.const_smul` |
| `galerkin_trilinear_vanishes` | `LerayHopf/GalerkinApproximation.lean` | The cubic energy term vanishes: ∑_{k,j,l} B_{kjl} c_k c_j c_l = 0, via `trilinear_at_galerkin` and `trilinearForm_antisymmetric` |

### Sorry Classification

17 total sorries across 6 files. The 5 legacy Foundations/Existence sorries are all
Category C. The 11 new sorries (v0.4.2) are Category B/C sub-goals within the Galerkin
construction that is the stated proof strategy for `lerayHopf_existence`.

**Foundations (5 sorry, Category C):**

| File | Sorry | Reason |
|------|-------|--------|
| `SobolevEmbedding.lean` | `sobolev_embedding_subcritical` | GNS + Meyers-Serrin density (weak-to-classical derivative bridge) |
| `SobolevEmbedding.lean` | `sobolev_embedding_subcritical_h10` | Same bridge for H^1_0; `clm_norm_sq_eq_sum_sq` assembly |
| `SobolevEmbedding.lean` | `sobolev_embedding_supercritical` | Morrey inequality (not yet in Mathlib) |
| `RellichKondrachov.lean` | `rellich_kondrachov` | Frechet-Kolmogorov compactness criterion |
| `Poincare.lean` | `poincare_inequality_convex` | n-D Poincaré via Fubini from 1D (1D result now proved in Mathlib fork) |

**Leray-Hopf (12 sorry):**

| File | Sorry | Category | Blocker |
|------|-------|----------|---------|
| `Existence.lean` | `lerayHopf_existence` | C | Full Galerkin + Aubin-Lions construction |
| `GalerkinApproximation.lean` | `galerkinRHS_contDiff` | B | Polynomial-in-coordinates argument |
| `GalerkinApproximation.lean` | `galerkinVelocity_l2NormSq_eq` | B | Orthonormality + Fubini |
| `GalerkinApproximation.lean` | `trilinear_at_galerkin` | B | Multilinearity expansion |
| `GalerkinApproximation.lean` | `galerkinVelocity_divFree` | B | `IsDistribDivFree` linearity |
| `GalerkinApproximation.lean` | `galerkinVelocity_compact` | B | `HasCompactSupport` finite sum (Mathlib gap) |
| `GalerkinApproximation.lean` | `galerkinRHS_inner_nonpos` | B | PSD matrix + trilinear cancellation |
| `GalerkinApproximation.lean` | `galerkin_energy_nonincreasing` | B | Monotone integral from `HasDerivAt` |
| `GalerkinApproximation.lean` | `galerkin_exists_global` | B | `IsPicardLindelof` + energy continuation |
| `GalerkinApproximation.lean` | `galerkin_uniformL2Bound` | C | Bessel inequality for initial data |
| `AubinLions.lean` | `aubinLions_compactness` | C | Abstract Banach-valued L^p theory |
| `AubinLions.lean` | `galerkin_sequence_has_convergent_subseq` | C | Rellich-Kondrachov + Aubin-Lions |

The 4 Foundations sorries remain outside the `lerayHopf_existence` dependency chain.

**Sorry-free files:** `WeakDerivative.lean`, `SobolevSpace.lean`, `DivFreeSpace.lean`,
`HelmholtzProjection.lean`, `WeakNSSolution.lean`, `TrilinearForm.lean`,
`EnergyInequality.lean`.

**Mathlib fork:** `Mathlib/Analysis/FunctionalSpaces/PoincareInequality.lean` is now
fully sorry-free (1D Poincaré inequality proved via variance/discriminant argument).

**Chapter 1 (5 sorry):** Sobolev embeddings (3), Rellich-Kondrachov (1), Poincare (1).

**Chapter 2 (12 sorry):** Leray-Hopf existence (1 legacy) + Galerkin/Aubin-Lions infrastructure (11 new).

```bash
cd lean && lake build    # 2787 jobs, ~2 min
```

## SymPy Verification

Each chapter has one or more Python scripts that symbolically verify the key identities and estimates from the LaTeX text.

```bash
python sympy/ch01_sobolev_exponents.py      #  6 checks
python sympy/ch01_helmholtz_verify.py        #  2 checks
python sympy/ch02_leray_hopf_verify.py       # 13 checks
python sympy/ch03_biot_savart_verify.py      # 23 checks
python sympy/ch04_curvature_verify.py        # 14 checks
```

All scripts use assert-based checks and print `[PASS]` for each verified identity.
The ch03 script covers: Leray projector properties (5 test fields), Koszul formula sign
consistency, Holder/Sobolev product exponents (H^1 into L^6 in R^3, product into L^{3/2}),
Calderon-Zygmund kernel hypotheses, Biot-Savart HLS exponents (alpha_HLS=1, giving
1/q = 1/p - 1/3, p < 3), and stretching tensor trace identities.

The ch04 script covers three parts: (I) pressure Poisson connection -- velocity gradient
decomposition A=D+W, vorticity norm |omega|^2 = |A|^2 - tr(A^2), and Delta p = -tr(A^2)
verified on four ABC fields; (II) Arnold sectional curvature -- explicit K values for
mode pairs (1,0,0)/(0,1,0), (1,0,0)/(1,1,0), (1,1,0)/(2,1,1), same-shell degeneracy
K=0; (III) Holder exponent chain -- 6x2->3/2, 6x3/2->6/5 as exact rationals, and the
exponent consistency (3/2)x(6/5) = 9/5 appearing in the curvature measure bound.

## Compilation

### Light mode
```bash
cd latex && make light
```

### Dark mode (WCAG AA compliant)
```bash
cd latex && make dark
```

The dark mode build uses a custom `darkmode.sty` package with WCAG AA colour contrast:
- Text: #E0E0E0 on #2B2B2B (11.3:1, AAA)
- Links: #6CB4EE on #2B2B2B (6.1:1, AA)

### Both
```bash
cd latex && make all
```

## Mathematical Overview

The central idea is to define a connection on the infinite-dimensional bundle of
divergence-free velocity fields, constructed from the Biot-Savart kernel and the
Leray projection. The curvature of this connection encodes geometric constraints
that incompressibility imposes on the flow, and the programme asks whether these
constraints obstruct finite-time blowup.

**Chapter 1** establishes the functional analytic foundations: Sobolev spaces, embedding
theorems, the Helmholtz decomposition, and the Leray projector. The whole-space Helmholtz
decomposition on R^n is handled via the Riesz potential and Fourier multiplier
characterisation of the Leray projector.

**Chapter 2** develops Leray-Hopf weak solutions on R^3: the weak formulation,
trilinear form antisymmetry, Galerkin approximation via Gram-Schmidt on
C_c^infty intersect L^2_sigma, the energy inequality, Serrin's regularity criterion,
and the connection to Fefferman's Clay formulation (Problems A through D).

**Chapter 3** constructs the Biot-Savart connection on the divergence-free bundle.
The Biot-Savart map (curl composed with minus the inverse Laplacian) is shown to be
torsion-free and metric-compatible with respect to the L^2 metric, establishing it as
the Levi-Civita connection of the divergence-free bundle. All geometric identities
(Koszul formula, torsion, metric compatibility) are understood in the distributional
sense at Leray-Hopf regularity: at this regularity the connection takes values in
L^{3/2}_sigma, which is strictly smaller than L^2_sigma. The vorticity equation is
recast as a forced parallel-transport equation along the flow. Curvature is computed
via the abstract Riemann tensor and the first Bianchi identity is verified algebraically.
Calderon-Zygmund and Hardy-Littlewood-Sobolev estimates close the Leray-Hopf regularity
loop (BS: L^p to L^q with 1/q = 1/p - 1/3, 1 < p < 3).

**Chapter 4** develops the curvature theory at Leray-Hopf regularity. Arnold's formula
gives sectional curvature K(e_k, e_m) = -(|k|^2-|m|^2)^2/(4|k|^2|m|^2|k x m|^2) < 0
between shells and K=0 within a shell, with the pressure Poisson term -tr(A^2) as the
dominant contribution. The velocity gradient decomposition A=D+W identifies the pressure
Poisson identity Delta p = |omega|^2/2 - |D|^2_F = -tr(A^2). The viscous Jacobi equation
is derived by linearising NS around a one-parameter family of solutions; the Lyapunov bound
relates Jacobi field growth to the strain excess Delta_strain = lambda_1(D) - nu*lambda_min(-Delta).
Helicity is identified as the Chern-Simons invariant of the velocity one-form; the holonomy
tensor of the Biot-Savart connection has Abelian part equal to the circulation, and vortex
filaments carry integer defect charge. The curvature measure mu_R = |R|^{6/5} dx dt is
finite at Leray-Hopf regularity (bound C*E(0)^{9/5}/nu^{9/5}), and the CKN bridge theorem
(proved in full) shows (x_0,t_0) is regular iff mu_R(Q_r)/r -> 0, placing singularities
exactly at atoms of mu_R. Numerical experiments (Taylor-Green, Re=1600, 512^3) illustrate
all five geometric phenomena with transparent figures in both light and dark mode.

## Citation

This is an ongoing research programme. I do not claim to have resolved the
Millennium Problem. If you wish to reference this work:

```bibtex
@misc{sotofranco2026navier,
  author = {Soto Franco, Alejandro Jos\'{e}},
  title  = {On the Regularity of Three-Dimensional {Navier--Stokes} Solutions:
            A Geometric Approach via the {Biot--Savart} Connection},
  year   = {2026},
  note   = {Work in progress},
  url    = {https://github.com/alejandro-soto-franco/navier-stokes}
}
```
