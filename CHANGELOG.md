# Changelog

All notable changes to this project are documented here.

## [0.2.1] - 2026-03-31 (`c98c871`)

### Proved
- `trilinearForm_antisymmetric` (TrilinearForm.lean): b(u,v,v) = 0 for
  distributionally divergence-free u and smooth compactly-supported v.
  Per-component test function strategy (phi_k = v_k^2) with fderiv_fun_pow
  chain rule and integral_const_mul. Added ContDiff/HasCompactSupport
  hypotheses. Sorry count: 11 -> 10, proved: 5 -> 6.

## [0.2.0] - 2026-03-30 (`46fa6e8`)

### Proved
- `l2sigma_closed_under_l2_convergence` (DivFreeSpace.lean): L²σ is closed under
  L² convergence, via Hölder's inequality (Cauchy-Schwarz with p=q=2),
  `PiLp.norm_apply_le` for the component bound, and `tendsto_nhds_unique` for
  limit uniqueness. First machine-checked proof of this result in any proof
  assistant. Sorry count: 12 → 11.

### Added
- **Chapter 2 (Leray-Hopf weak solutions)**:
  - Lean: definitions and theorem statements for weak formulation, trilinear
    form (sorry-free definition), energy inequality, Leray-Hopf existence
    (sorry stub), Serrin regularity criterion. 3 sorry remain.
  - LaTeX: complete. Full narrative with proofs (Galerkin approximation on R³,
    Gram-Schmidt on C∞\_c ∩ L²σ, energy inequality, connection to Fefferman's
    Clay formulation Problems A-D).
  - SymPy: complete. 13/13 symbolic checks pass (trilinear antisymmetry, energy
    balance, Serrin exponents, interpolation, Gronwall, Prodi-Serrin pairs).
- `sobolevConjugate_gt` proved: p* > p for 1 ≤ p < n.
- `sobolevConjugate_inv` proved: 1/p* = 1/p - 1/n.
- Dark mode PDF target (WCAG AA compliant, `make dark`).
- Preface outlining the three-track programme.
- Clay formulation rewritten to faithfully follow Fefferman (2006).

### Changed
- Galerkin approximation rewritten on whole-space R³ (not bounded domains).
- `IsDistribDivFree` updated: `ContDiff ℝ ⊤` replaced by `ContDiff ℝ ∞`.
- `l2sigma_isClosed` (wrong topology) replaced by
  `l2sigma_closed_under_l2_convergence` (correct L² sequential closedness).

## [0.1.0] - 2026-03-29 (`159ad8e`)

### Added
- **Chapter 1 (Functional Analytic Foundations)**:
  - Lean: 9 definitions, all type-checking. `weakPartialDeriv_unique` and
    `sobolevH1InnerProduct_comm` proved. 8 sorry remain (embeddings, Poincare,
    Helmholtz, Leray projector).
  - LaTeX: complete. 6 sections (distributions, Sobolev spaces, embeddings,
    Rellich-Kondrachov, Poincare, Helmholtz/Leray projector).
  - SymPy: complete. 8/8 symbolic checks pass (Sobolev exponents, Helmholtz
    orthogonality).
- Lean 4 project initialized against pinned Mathlib4 fork (commit `698d2b68`,
  based on v4.29.0-rc8). Builds with 2685 jobs, 0 errors.
- Sync document framework (`sync/ch01-foundations.md`).
- Three-track architecture: Lean + LaTeX + SymPy with chapter-boundary reconciliation.
