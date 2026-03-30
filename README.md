# On the Regularity of Three-Dimensional Navier-Stokes Solutions

[![Lean 4](https://img.shields.io/badge/Lean_4-v4.29.0--rc8-blue?logo=data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNCAyNCI+PHBhdGggZmlsbD0id2hpdGUiIGQ9Ik0xMiAyTDIgMjJoMjBMMTIgMnoiLz48L3N2Zz4=)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/Mathlib4-v4.29.0--rc8_(fork)-blue)](https://github.com/alejandro-soto-franco/mathlib4)
[![SymPy](https://img.shields.io/badge/SymPy-verified-brightgreen?logo=python&logoColor=white)](https://www.sympy.org/)
[![LaTeX](https://img.shields.io/badge/LaTeX-book_class-orange?logo=latex&logoColor=white)](https://www.latex-project.org/)
[![License](https://img.shields.io/badge/License-All_Rights_Reserved-red)](https://github.com/alejandro-soto-franco/navier-stokes/blob/master/LICENSE)
[![Chapter 1](https://img.shields.io/badge/Ch_1-Foundations_%E2%9C%93-brightgreen)](#chapter-status)
[![Chapter 2](https://img.shields.io/badge/Ch_2-Leray--Hopf_%E2%9C%93-brightgreen)](#chapter-status)
[![Chapter 3](https://img.shields.io/badge/Ch_3-Biot--Savart-yellow)](#chapter-status)
[![Chapter 4](https://img.shields.io/badge/Ch_4-Connection-yellow)](#chapter-status)
[![Chapter 5](https://img.shields.io/badge/Ch_5-Curvature-yellow)](#chapter-status)
[![Chapter 6](https://img.shields.io/badge/Ch_6-Topology-yellow)](#chapter-status)
[![Chapter 7](https://img.shields.io/badge/Ch_7-Obstruction-yellow)](#chapter-status)
[![Chapter 8](https://img.shields.io/badge/Ch_8-Singularity-yellow)](#chapter-status)
[![Dark Mode](https://img.shields.io/badge/Dark_Mode-WCAG_AA-blueviolet)](#compilation)
[![Build](https://img.shields.io/badge/Lean_Build-2753_jobs-informational)](#lean-formalisation)
[![Sorry Count](https://img.shields.io/badge/sorry-11_total-yellow)](#lean-formalisation)
[![Proved](https://img.shields.io/badge/Proved-5_theorems-brightgreen)](#proven-theorems)

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
| 1 | Functional Analytic Foundations | 9 defs, 5 proved, 8 sorry | Complete | 8/8 pass | [Passed](sync/ch01-foundations.md) |
| 2 | Leray-Hopf Weak Solutions | 8 defs, 3 sorry | Complete | 13/13 pass | [Passed](sync/ch02-leray-hopf.md) |
| 3 | The Biot-Savart Operator | Stubs | In progress | Planned | -- |
| 4 | The Biot-Savart Connection | Stubs | In progress | Planned | -- |
| 5 | Curvature of the Flow | -- | In progress | Planned | -- |
| 6 | Topological Constraints | Stubs | In progress | Planned | -- |
| 7 | The Obstruction Theorem | Stubs | In progress | Planned | -- |
| 8 | Singularity Analysis | -- | In progress | Planned | -- |

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
      BiotSavart/          Ch3: Biot-Savart operator (stubs)
      Topology/            Ch6: Topological constraints (stubs)
      Obstruction/         Ch7: Obstruction theorem (stubs)
  sympy/                  Symbolic verification scripts
    ch01_sobolev_exponents.py
    ch01_helmholtz_verify.py
    ch02_leray_hopf_verify.py
  sync/                   Cross-track reconciliation documents
  numerics/               Numerical solvers (planned)
```

## Lean Formalisation

The Lean 4 formalisation builds against a [pinned fork of Mathlib4](https://github.com/alejandro-soto-franco/mathlib4) (commit `698d2b68`, based on `v4.29.0-rc8`) and compiles with 2753 jobs, 0 errors. The fork allows adding custom tooling (Sobolev spaces, embedding infrastructure) that can be PR'd back to upstream Mathlib as the project matures. The `lakefile.toml` pins to exact commit hashes for reproducible builds.

### Proven Theorems

| Theorem | File | Description |
|---------|------|-------------|
| `weakPartialDeriv_unique` | `Foundations/WeakDerivative.lean` | Weak partial derivatives are unique a.e., via the fundamental lemma of the calculus of variations (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`) |
| `sobolevConjugate_gt` | `Foundations/SobolevEmbedding.lean` | The Sobolev conjugate exponent p* > p for 1 <= p < n |
| `sobolevConjugate_inv` | `Foundations/SobolevEmbedding.lean` | The dimensional relation 1/p* = 1/p - 1/n |
| `sobolevH1InnerProduct_comm` | `Foundations/SobolevSpace.lean` | Symmetry of the H^1 inner product |
| `l2sigma_closed_under_l2_convergence` | `Foundations/DivFreeSpace.lean` | L²σ is closed under L² convergence, via Hölder (Cauchy-Schwarz) and `tendsto_nhds_unique` |

### Sorry Classification

All 11 remaining sorries are Category C (fundamental PDE/functional analysis results not yet in Mathlib):

| File | Sorry | Reason |
|------|-------|--------|
| `DivFreeSpace.lean` | `helmholtz_decomposition` | Hilbert space orthogonal projection onto L2_sigma |
| `DivFreeSpace.lean` | `lerayProjector` (MemLp arg) | Depends on Helmholtz |
| `DivFreeSpace.lean` | `lerayProjector_idempotent` | Projection algebra (depends on Helmholtz) |
| `DivFreeSpace.lean` | `lerayProjector_selfAdjoint` | Orthogonal projection self-adjointness (depends on Helmholtz) |
| `SobolevEmbedding.lean` | `sobolev_embedding_subcritical` | Gagliardo-Nirenberg-Sobolev on domains |
| `SobolevEmbedding.lean` | `sobolev_embedding_supercritical` | Morrey inequality |
| `RellichKondrachov.lean` | `rellich_kondrachov` | Frechet-Kolmogorov compactness |
| `Poincare.lean` | `poincare_inequality` | Relies on Rellich-Kondrachov |
| `Poincare.lean` | `poincare_constant_bound_convex` | Payne-Weinberger optimal constant |
| `TrilinearForm.lean` | `trilinearForm_antisymmetric` | Integration by parts for H^1 |
| `Existence.lean` | `lerayHopf_existence` | Full Galerkin + Aubin-Lions construction |

**Definitions now sorry-free:**
- `SobolevH1Zero` (H^1_0 as subtype of H^1 via smooth approximation)
- `trilinearForm` (concrete integral: sum_{i,j} int u_j * d_j(v_i) * w_i)

**Chapter 1 (8 sorry):** Embedding theorems, Poincare inequality, Helmholtz decomposition, Leray projector.

**Chapter 2 (3 sorry):** Trilinear form antisymmetry, Leray-Hopf existence, energy inequality placeholder.

```bash
cd lean && lake build    # 2753 jobs, ~2 min
```

## SymPy Verification

Each chapter has one or more Python scripts that symbolically verify the key identities and estimates from the LaTeX text.

```bash
python sympy/ch01_sobolev_exponents.py     # 6 checks
python sympy/ch01_helmholtz_verify.py       # 2 checks
python sympy/ch02_leray_hopf_verify.py      # 13 checks
```

All scripts use assert-based checks and print `[PASS]` for each verified identity.

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
theorems, the Helmholtz decomposition, and the Leray projector.

**Chapter 2** develops Leray-Hopf weak solutions on R^3: the weak formulation,
trilinear form antisymmetry, Galerkin approximation via Gram-Schmidt on
C_c^infty intersect L^2_sigma, the energy inequality, Serrin's regularity criterion,
and the connection to Fefferman's Clay formulation (Problems A through D).

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
