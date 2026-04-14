# On the Regularity of 3D Navier-Stokes Solutions

[![Lean 4](https://img.shields.io/badge/Lean_4-v4.29.0--rc8-blue?logo=data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNCAyNCI+PHBhdGggZmlsbD0id2hpdGUiIGQ9Ik0xMiAyTDIgMjJoMjBMMTIgMnoiLz48L3N2Zz4=)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/Mathlib4-v4.29.0--rc8_(fork)-blue)](https://github.com/alejandro-soto-franco/mathlib4)
[![SymPy](https://img.shields.io/badge/SymPy-verified-brightgreen?logo=python&logoColor=white)](https://www.sympy.org/)
[![Cadabra2](https://img.shields.io/badge/Cadabra2-2.3.0-blueviolet?logo=python&logoColor=white)](https://cadabra.science/)
[![LaTeX](https://img.shields.io/badge/LaTeX-book_class-orange?logo=latex&logoColor=white)](https://www.latex-project.org/)
[![License](https://img.shields.io/badge/License-All_Rights_Reserved-red)](https://github.com/alejandro-soto-franco/navier-stokes/blob/master/LICENSE)
[![Chapter 1](https://img.shields.io/badge/Ch_1-Foundations_%E2%9C%93-brightgreen)](#chapter-status)
[![Chapter 2](https://img.shields.io/badge/Ch_2-Leray--Hopf_%E2%9C%93-brightgreen)](#chapter-status)
[![Chapter 3](https://img.shields.io/badge/Ch_3-Biot--Savart_%E2%9C%93-brightgreen)](#chapter-status)
[![Chapter 4](https://img.shields.io/badge/Ch_4-Curvature_%E2%9C%93-brightgreen)](#chapter-status)
[![Chapter 5](https://img.shields.io/badge/Ch_5-Determination_%E2%9C%93-brightgreen)](#chapter-status)
[![Chapter 6](https://img.shields.io/badge/Ch_6-Singularity-yellow)](#chapter-status)
[![Dark Mode](https://img.shields.io/badge/Dark_Mode-WCAG_AA-blueviolet)](#compilation)
[![Lean CI](https://github.com/alejandro-soto-franco/navier-stokes/actions/workflows/lean.yml/badge.svg)](https://github.com/alejandro-soto-franco/navier-stokes/actions/workflows/lean.yml)
[![Build](https://img.shields.io/badge/Lean_Build-2789_jobs-informational)](#lean-formalisation)
[![Sorry Count](https://img.shields.io/badge/sorry-23_lines_(12_decls)-yellow)](#lean-formalisation)
[![Proved](https://img.shields.io/badge/Proved-21_theorems-brightgreen)](#proven-theorems)

A geometric-analytic approach to the Clay Millennium regularity problem for the 3D incompressible Navier-Stokes equations, via the Biot-Savart connection on the divergence-free bundle.

**Author:** Alejandro José Soto Franco

## Three-Track Architecture

Every chapter is developed simultaneously along three parallel verification tracks:

| Track | Tool | Purpose |
|-------|------|---------|
| **Formal verification** | Lean 4 + Mathlib | Type-checked definitions, theorem statements, and proofs |
| **Theory** | LaTeX + SymPy + Cadabra2 | Self-contained mathematical narrative with symbolic cross-checks |
| **Numerics** | Python/Rust | Computational verification of geometric predictions (later chapters) |

The symbolic track uses two complementary tools. **SymPy** handles coordinate-based checks: Sobolev exponents, example-field identities, Leray projector algebra, Hölder/HLS exponents. **Cadabra2** handles abstract-index tensor algebra: structure-constant symmetries, Koszul formula manipulation, non-holonomic torsion conditions, and (from Chapter 5 onward) differential-form computations. All scripts run under a single pinned conda environment (`environment.yml`).

The tracks are reconciled at chapter boundaries via sync documents in `sync/`.

## Chapter Status

| Chapter | Title | Lean | LaTeX | SymPy | Sync |
|---------|-------|------|-------|-------|------|
| 1 | Functional Analytic Foundations | 17 defs, 11 proved, 6 sorry | Complete | 8/8 pass | [Passed](sync/ch01-foundations.md) |
| 2 | Leray-Hopf Weak Solutions | 12 defs, 11 proved, 5 sorry | Complete | 13/13 pass | [Passed](sync/ch02-leray-hopf.md) |
| 3 | The Biot-Savart Connection | Stubs | Complete (64pp) | 23/23 + 5LC pass | -- |
| 4 | Curvature of the Flow | -- | Draft complete | 14/14 pass | -- |
| 5 | The Topological Determination | 4 stubs | Complete | 3C + 5S pass | -- |
| 6 | The Singularity Analysis | -- | In progress | Planned | -- |

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
  environment.yml         Pinned conda environment (Python 3.9, cadabra2 2.3.0, sympy, numpy, matplotlib, scipy)
  sympy/                  Symbolic verification scripts
    ch01_sobolev_exponents.py
    ch01_helmholtz_verify.py
    ch02_leray_hopf_verify.py
    ch03_biot_savart_verify.py
    ch03_lc_cadabra.py      Cadabra2+SymPy: Levi-Civita uniqueness proof (fills ch03 check 13)
    ch04_curvature_verify.py
    ch05_topology_cadabra.py  Cadabra2: differential form identities (d^2=0, Chern-Simons, dissipation)
    ch05_topology_verify.py   SymPy: Beltrami helicity, Arnold bound, Freedman-He, local density
    ch04_figures.py         ch04 figure generator (light + dark variants)
    plot_style.py           shared matplotlib style (LaTeX, transparent, dark mode)
  sync/                   Cross-track reconciliation documents
  numerics/               Numerical solvers (planned)
```

## Lean Formalisation

The Lean 4 formalisation builds against a [pinned fork of Mathlib4](https://github.com/alejandro-soto-franco/mathlib4) (commit `698d2b68`, based on `v4.29.0-rc8`) and compiles with 2789 jobs, 0 errors. The fork includes a 1D Poincare inequality (`PoincareInequality.lean`, sorry-free) that feeds into the $n$-D Poincare proof. The `lakefile.toml` pins to exact commit hashes for reproducible builds.

### Proven Theorems

| Theorem | File | Description |
|---------|------|-------------|
| `weakPartialDeriv_unique` | `Foundations/WeakDerivative.lean` | Weak partial derivatives are unique a.e., via the fundamental lemma of the calculus of variations |
| `sobolevConjugate_gt` | `Foundations/SobolevEmbedding.lean` | The Sobolev conjugate exponent $p^* > p$ for $1 \leq p < n$ |
| `sobolevConjugate_inv` | `Foundations/SobolevEmbedding.lean` | The dimensional relation $1/p^* = 1/p - 1/n$ |
| `sobolevH1InnerProduct_comm` | `Foundations/SobolevSpace.lean` | Symmetry of the $H^1$ inner product |
| `l2sigma_closed_under_l2_convergence` | `Foundations/DivFreeSpace.lean` | $L^2_\sigma$ is closed under $L^2$ convergence, via Hölder (Cauchy-Schwarz) and `tendsto_nhds_unique` |
| `trilinearForm_antisymmetric` | `LerayHopf/TrilinearForm.lean` | $b(u,v,v) = 0$ for distributionally divergence-free $u$ and smooth compactly-supported $v$, via per-component test functions $\phi_k = v_k^2$ |
| `l2sigmaSubmodule_isSeqClosed` | `Foundations/HelmholtzProjection.lean` | Sequential closedness of $L^2_\sigma$; norm bridge via `L2.inner_def` and `real_inner_self_eq_norm_sq` |
| `l2sigmaSubmodule_isClosed` | `Foundations/HelmholtzProjection.lean` | Topological closedness of $L^2_\sigma$ via sequential closedness and metric structure of $L^2$ |
| `lerayProjectorLp_idempotent` | `Foundations/HelmholtzProjection.lean` | $P(P(f)) = P(f)$, via `starProjection_eq_self_iff.mpr` |
| `lerayProjectorLp_selfAdjoint` | `Foundations/HelmholtzProjection.lean` | $\langle Pf, g \rangle = \langle f, Pg \rangle$, via `inner_starProjection_left_eq_right` |
| `helmholtz_l2_decomposition` | `Foundations/HelmholtzProjection.lean` | $f = Pf + (f - Pf)$ with $Pf \in L^2_\sigma$ and $\langle Pf, f - Pf \rangle = 0$, via `starProjection_inner_eq_zero` |
| `galerkinRHS_locallyLipschitz` | `LerayHopf/GalerkinApproximation.lean` | The Galerkin ODE RHS is locally Lipschitz, via `ContDiff.of_le (by norm_cast)` downgrading $C^\infty$ to $C^1$ |
| `galerkinVelocity_smooth` | `LerayHopf/GalerkinApproximation.lean` | The reconstructed velocity $u_N = \sum_k c_k w_k$ is $C^\infty$, via `ContDiff.sum` and `ContDiff.const_smul` |
| `galerkin_trilinear_vanishes` | `LerayHopf/GalerkinApproximation.lean` | The cubic energy term vanishes: $\sum_{k,j,\ell} B_{kj\ell}\, c_k c_j c_\ell = 0$, via `trilinear_at_galerkin` and `trilinearForm_antisymmetric` |
| `galerkinVelocity_l2NormSq_eq` | `LerayHopf/GalerkinApproximation.lean` | $\|u_N\|^2_{L^2} = \|c\|^2$ by orthonormality of the basis, via `integral_finset_sum` and `basis_orthonorm` |
| `galerkin_energy_nonincreasing` | `LerayHopf/GalerkinApproximation.lean` | $\|c(t)\| \leq \|c_0\|$ for all $t \geq 0$, via `HasDerivAt.norm_sq` and `antitone_of_hasDerivAt_nonpos` |
| `galerkin_uniformL2Bound` | `LerayHopf/GalerkinApproximation.lean` | $\int\|u_N(t)\|^2 \leq \int\|u_0\|^2$ via Bessel inequality (projection argument: $0 \leq \int\|u_0 - \text{proj}\|^2$) |
| `bessel_l2_vector` | `LerayHopf/GalerkinApproximation.lean` | Bessel's inequality for vector-valued $L^2$ functions against finite orthonormal systems, via Holder ($L^2 \times L^2 \to L^1$) |
| `integrable_inner_basis` | `LerayHopf/GalerkinApproximation.lean` | Integrability of $\langle f, w_k \rangle$ for $f \in L^2$ and $w_k$ smooth with compact support, via `MemLp.mul'` with `HolderConjugate 2 2` |
| `poincare_smooth` | `Foundations/Poincare.lean` | Poincare for smooth functions: averaging $n$ per-direction bounds from `poincare_slice` |

### Sorry Classification

23 sorry lines (12 declarations) across 10 files. All Foundations/Chapter 1 files except
Poincare, SobolevEmbedding, and RellichKondrachov are sorry-free. The Galerkin infrastructure
(energy monotonicity, L^2 norm identity, uniform L^2 bound via Bessel inequality) is fully proved.

**Foundations (6 sorry):**

| File | Sorry | Blocker |
|------|-------|---------|
| `SobolevEmbedding.lean` | `sobolev_embedding_subcritical` | GNS + Meyers-Serrin density |
| `SobolevEmbedding.lean` | `sobolev_embedding_subcritical_h10` | Same bridge for $H^1_0$ |
| `SobolevEmbedding.lean` | `sobolev_embedding_supercritical` | Morrey inequality (not in Mathlib) |
| `RellichKondrachov.lean` | `rellich_kondrachov` | Frechet-Kolmogorov compactness |
| `Poincare.lean` | `poincare_slice` | Fubini decomposition for $n$-D to 1D slicing |
| `Poincare.lean` | `poincare_inequality_convex` | $H^1_0$ limit passage from smooth case |

**Leray-Hopf (7 sorry lines, 6 declarations):**

| File | Sorry | Blocker |
|------|-------|---------|
| `Existence.lean` | `lerayHopf_existence` | Full Galerkin + Aubin-Lions construction |
| `GalerkinApproximation.lean` | `trilinear_at_galerkin` (2 sorries) | Algebraic 5-fold sum-integral swap + integrability |
| `GalerkinApproximation.lean` | `galerkin_exists_local` | Picard-Lindelof application |
| `GalerkinApproximation.lean` | `galerkin_exists_global` | Global continuation via energy bound |
| `AubinLions.lean` | `aubinLions_compactness` | Abstract Banach-valued $L^p$ theory |
| `AubinLions.lean` | `galerkin_sequence_has_convergent_subseq` | Application of Aubin-Lions |

**Topology / Chapter 5 (10 sorry):** Helicity definitions (3), conservation/dissipation (2),
Arnold/Freedman-He bounds (2), topological regularity (3). All require curl operator definition.

**Sorry-free files:** `WeakDerivative.lean`, `SobolevSpace.lean`, `DivFreeSpace.lean`,
`HelmholtzProjection.lean`, `WeakNSSolution.lean`, `TrilinearForm.lean`,
`EnergyInequality.lean`.

**Proved in this session (previously sorry):**
- `galerkinVelocity_l2NormSq_eq`: $\|u_N\|^2_{L^2} = \|c\|^2$ by orthonormality
- `galerkin_uniformL2Bound`: $\int\|u_N(t)\|^2 \leq \int\|u_0\|^2$ via Bessel inequality
- `galerkin_energy_nonincreasing`: $\|c(t)\| \leq \|c_0\|$ along solutions
- `galerkinRHS_contDiff`, `galerkinVelocity_divFree`, `galerkinVelocity_compact`, `galerkinRHS_inner_nonpos`
- `poincare_smooth`: averaging bound over $n$ directions (uses `poincare_slice`)

```bash
cd lean && lake build    # 2787 jobs, ~2 min
```

## Symbolic Verification

All scripts run under the pinned conda environment:

```bash
conda activate navier-stokes   # Python 3.9, cadabra2 2.3.0, sympy 1.14, numpy, matplotlib, scipy
```

### SymPy scripts (coordinate-based)

```bash
python sympy/ch01_sobolev_exponents.py      #  6 checks
python sympy/ch01_helmholtz_verify.py        #  2 checks
python sympy/ch02_leray_hopf_verify.py       # 13 checks
python sympy/ch03_biot_savart_verify.py      # 23 checks
python sympy/ch04_curvature_verify.py        # 14 checks
python sympy/ch05_topology_verify.py        #  5 checks (T-4 to T-8)
```

All scripts use assert-based checks and print `[PASS]` for each verified identity.
The ch03 script covers: Leray projector properties (5 test fields), Koszul formula sign
consistency, Hölder/Sobolev product exponents ($H^1$ into $L^6$ in $\mathbb{R}^3$, product into $L^{3/2}$),
Calderón-Zygmund kernel hypotheses, Biot-Savart HLS exponents ($\alpha_{\text{HLS}} = 1$, giving
$1/q = 1/p - 1/3$, $p < 3$), and stretching tensor trace identities.

### Cadabra2 scripts (abstract-index tensor algebra)

```bash
python sympy/ch03_lc_cadabra.py             # 5 LC checks (Cadabra + SymPy)
python sympy/ch05_topology_cadabra.py       # 3 checks (T-1 to T-3)
```

`ch03_lc_cadabra.py` fills the one un-executed claim in ch03 ("Koszul formula: follows from
metric compatibility + torsion-freeness") with a concrete two-tool proof:

| Check | Tool | Statement |
|-------|------|-----------|
| LC-1 | Cadabra2 | $C_{kij} + C_{kji} = 0$ (structure-constant antisymmetry, abstract) |
| LC-2 | Cadabra2 | Koszul ansatz $2\Gamma_{kij} = C_{kij} - C_{ijk} + C_{jki}$ |
| LC-3 | Cadabra2 | Non-holonomic torsion-free: $\Gamma_{kij} - \Gamma_{kji} = C_{kij}$ |
| LC-4 | SymPy | IBP: Koszul integrand $- 2(u \cdot \nabla)v \cdot w$ = sum of 3 total divergences (5 triples) |
| LC-5 | SymPy | Metric compatibility: $u \cdot \nabla(v \cdot w) = (\nabla_u v) \cdot w + v \cdot (\nabla_u w)$ (5 triples) |

**Scope boundary:** Cadabra handles abstract claims valid for any right-invariant metric on
any Lie group (LC-1 to LC-3). SymPy handles the $L^2$ metric on $\mathrm{SDiff}(\mathbb{T}^3)$ specifically, where
the divergence-free constraint enters via integration by parts (LC-4, LC-5).

`ch05_topology_cadabra.py` verifies the differential form identities underpinning Chapter 5:

| Check | Tool | Statement |
|-------|------|-----------|
| T-1 | Cadabra2 | $\mathrm{div}(\mathrm{curl}\, A) = 0$ (Bianchi identity $\mathrm{d}^2 = 0$, contracted with $\epsilon$) |
| T-2 | Cadabra2 | $\epsilon \cdot \mathrm{sym}(\mathrm{d}A) = 0$ (exterior derivative antisymmetry) |
| T-3 | Cadabra2 | $\omega \cdot (\mathrm{curl}\, \omega) \neq \lvert\omega\rvert^2$ (dissipation has indefinite sign) |

`ch05_topology_verify.py` verifies the energy-helicity landscape on explicit Beltrami fields:

| Check | Tool | Statement |
|-------|------|-----------|
| T-4 | SymPy | Helicity density $h = \lambda \lvert u\rvert^2$ for Beltrami eigenmodes (2 fields) |
| T-5 | SymPy | Dissipation rate $\omega \cdot (\mathrm{curl}\, \omega) = \lambda^3 \lvert u\rvert^2$ (2 fields) |
| T-6 | SymPy | Arnold bound $E \geq \lvert H\rvert / (2\lambda_1)$, equality at $\lambda_1$ |
| T-7 | SymPy | Freedman-He exponent $3/4 > 1/2$ (rational arithmetic) |
| T-8 | SymPy | Local helicity density sign structure (linked vs. mixed) |

The ch04 script covers three parts: (I) pressure Poisson connection: velocity gradient
decomposition $A = D + W$, vorticity norm $\lvert\omega\rvert^2 = \lvert A\rvert^2 - \mathrm{tr}(A^2)$, and $\Delta p = -\mathrm{tr}(A^2)$
verified on four ABC fields; (II) Arnold sectional curvature: explicit $K$ values for
mode pairs $(1,0,0)/(0,1,0)$, $(1,0,0)/(1,1,0)$, $(1,1,0)/(2,1,1)$, same-shell degeneracy
$K = 0$; (III) Hölder exponent chain: $6 \times 2 \to 3/2$, $6 \times 3/2 \to 6/5$ as exact rationals, and the
exponent consistency $(3/2) \times (6/5) = 9/5$ appearing in the curvature measure bound.

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
decomposition on $\mathbb{R}^n$ is handled via the Riesz potential and Fourier multiplier
characterisation of the Leray projector.

**Chapter 2** develops Leray-Hopf weak solutions on $\mathbb{R}^3$: the weak formulation,
trilinear form antisymmetry, Galerkin approximation via Gram-Schmidt on
$C_c^\infty \cap L^2_\sigma$, the energy inequality, Serrin's regularity criterion,
and the connection to Fefferman's Clay formulation (Problems A through D).

**Chapter 3** constructs the Biot-Savart connection on the divergence-free bundle.
The Biot-Savart map ($\mathrm{curl} \circ (-\Delta)^{-1}$) is shown to be
torsion-free and metric-compatible with respect to the $L^2$ metric, establishing it as
the Levi-Civita connection of the divergence-free bundle. All geometric identities
(Koszul formula, torsion, metric compatibility) are understood in the distributional
sense at Leray-Hopf regularity: at this regularity the connection takes values in
$L^{3/2}_\sigma$, which is strictly smaller than $L^2_\sigma$. The vorticity equation is
recast as a forced parallel-transport equation along the flow. Curvature is computed
via the abstract Riemann tensor and the first Bianchi identity is verified algebraically.
Calderón-Zygmund and Hardy-Littlewood-Sobolev estimates close the Leray-Hopf regularity
loop (BS: $L^p \to L^q$ with $1/q = 1/p - 1/3$, $1 < p < 3$).

**Chapter 4** develops the curvature theory at Leray-Hopf regularity. Arnold's formula
gives sectional curvature $K(e_k, e_m) = -(|k|^2 - |m|^2)^2 / (4|k|^2 |m|^2 |k \times m|^2) < 0$
between shells and $K = 0$ within a shell, with the pressure Poisson term $-\mathrm{tr}(A^2)$ as the
dominant contribution. The velocity gradient decomposition $A = D + W$ identifies the pressure
Poisson identity $\Delta p = |\omega|^2/2 - |D|^2_F = -\mathrm{tr}(A^2)$. The viscous Jacobi equation
is derived by linearising NS around a one-parameter family of solutions; the Lyapunov bound
relates Jacobi field growth to the strain excess $\Delta_{\text{strain}} = \lambda_1(D) - \nu \lambda_{\min}(-\Delta)$.
Helicity is identified as the Chern-Simons invariant of the velocity one-form; the holonomy
tensor of the Biot-Savart connection has Abelian part equal to the circulation, and vortex
filaments carry integer defect charge. The curvature measure $\mu_R = |R|^{6/5}\, \mathrm{d}x\, \mathrm{d}t$ is
finite at Leray-Hopf regularity (bound $C \cdot E(0)^{9/5} / \nu^{9/5}$), and the CKN bridge theorem
(proved in full) shows $(x_0, t_0)$ is regular iff $\mu_R(Q_r)/r \to 0$, placing singularities
exactly at atoms of $\mu_R$. Numerical experiments (Taylor-Green, $Re = 1600$, $512^3$) illustrate
all five geometric phenomena with transparent figures in both light and dark mode.

**Chapter 5** constructs the topological determination: a systematic investigation of
whether vortex line topology constrains curvature concentration enough to prevent
singularities. The differential form framework (velocity one-form $A = u^\flat$, helicity
as Chern-Simons invariant) is established, followed by the energy-helicity landscape
(Arnold bound, Freedman-He crossing number bound). The topological dichotomy separates
potential singularities into helicity-constrained and helicity-free cases. The rate
competition between viscous reconnection (timescale $\delta^2/\nu$) and curvature concentration
(timescale $1/\Delta_{\text{strain}}$) yields a scale-independent time budget $T_\delta \leq C \cdot E(0)/\nu^3$.
The chapter concludes with a new conditional regularity criterion: if reconnection dominance
holds at every scale, the solution is smooth. The gap between this conditional result and
unconditional regularity is precisely identified.

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
