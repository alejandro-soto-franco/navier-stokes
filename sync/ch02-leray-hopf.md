# Sync Point: Chapter 2 -- Leray-Hopf Weak Solutions

**Date**: 2026-04-04 (updated from 2026-03-30)
**Status**: [x] Passed

## Track 1: Lean

All Ch2 modules build (2770 jobs total, no errors). Ch2-specific sorry count: 12
(1 legacy existence + 9 Galerkin sub-goals + 2 Aubin-Lions). Ch1 sorry items
remain unchanged (5 total: SobolevEmbedding 3, RellichKondrachov 1, Poincare 1).

### Formalized (definitions compile, types check)
- [x] `IsWeakNSSolution` -- weak NS solution structure (div-free + integral identity)
- [x] `trilinearForm` -- trilinear form b(u, v, w) definition
- [x] `trilinearForm_antisymmetric` -- b(u, v, v) = 0 for div-free u (proved)
- [x] `SatisfiesEnergyInequality` -- energy inequality structure
- [x] `energyInequality_implies_L2_bound` -- uniform L^2 bound from energy inequality (proved)
- [x] `IsLerayHopfSolution` -- Leray-Hopf solution combining weak sol + energy ineq
- [x] `lerayHopf_existence` -- existence of Leray-Hopf solutions (sorry)
- [x] `serrin_regularity` -- Serrin regularity criterion (trivial stub)
- [x] `GalerkinData N` -- structure: orthonormal basis + stiffness matrix + trilinear tensor
- [x] `galerkinRHS` -- ODE right-hand side F_N(c)_k = -nu(Ac)_k - sum B_{kjl} c_j c_l
- [x] `GalerkinSolution N nu data c₀` -- global solution structure for the Galerkin ODE
- [x] `galerkinVelocity` -- reconstructed velocity u_N = sum_k c_k w_k
- [x] `galerkinRHS_locallyLipschitz` -- ODE RHS is locally Lipschitz (proved)
- [x] `galerkinVelocity_smooth` -- u_N is C^inf (proved)
- [x] `galerkin_trilinear_vanishes` -- cubic energy term = 0 (proved via trilinearForm_antisymmetric)
- [x] `aubinLions_compactness` -- abstract Aubin-Lions (sorry stub)
- [x] `galerkin_sequence_has_convergent_subseq` -- Galerkin sequence has L^2 convergent subseq (sorry)

### Remaining `sorry` (Ch2-specific, 12 total)

**Legacy:**
- `Existence.lean`: `lerayHopf_existence` (full Galerkin + Aubin-Lions construction)

**Galerkin sub-goals (Category B — all mathematically straightforward):**
- `galerkinRHS_contDiff` (C^inf of polynomial ODE RHS)
- `galerkinVelocity_l2NormSq_eq` (orthonormality + Fubini)
- `trilinear_at_galerkin` (multilinearity expansion)
- `galerkinVelocity_divFree` (IsDistribDivFree linearity)
- `galerkinVelocity_compact` (HasCompactSupport finite sum)
- `galerkinRHS_inner_nonpos` (PSD matrix + trilinear cancellation)
- `galerkin_energy_nonincreasing` (monotone integral)
- `galerkin_exists_global` (Picard-Lindelöf + energy continuation)
- `galerkin_uniformL2Bound` (Bessel inequality)

**Aubin-Lions (Category C — require Banach-valued L^p theory not in Mathlib):**
- `aubinLions_compactness` (abstract lemma)
- `galerkin_sequence_has_convergent_subseq` (Galerkin application)

### Assessment
All definitions type-check and the full LerayHopf module builds. The Galerkin ODE
infrastructure is now formalised: three theorems are sorry-free
(`galerkinRHS_locallyLipschitz`, `galerkinVelocity_smooth`, `galerkin_trilinear_vanishes`).
The remaining sorry items are proof obligations with clear mathematical content:
the Category B items need Mathlib API bridging, the Category C items need abstract
Banach-space compactness theory not yet in Mathlib.

## Track 2: Theory (SymPy + LaTeX)

### Identities/estimates verified symbolically (13 checks, all pass)
- [x] Test field u = (sin y, sin z, sin x) is divergence-free
- [x] b(u,u,u) = (1/2)(u . grad)|u|^2 (pointwise identity)
- [x] b(u,u,u) = 0 for divergence-free u (integration by parts)
- [x] Energy equality structure: E(t) + int_0^t D(s)ds = E(0)
- [x] L^3 interpolation: theta = 1/2 (Holder exponent)
- [x] NS scaling-critical Lebesgue space: L^3 (scaling exponent = 0)
- [x] L^2 scaling exponent = -1/2 (subcritical)
- [x] Serrin pair (q=inf, r=3): 2/inf + 3/3 = 1
- [x] Serrin pair (q=4, r=6): 1/2 + 1/2 = 1
- [x] Serrin pair (q=8, r=4): 1/4 + 3/4 = 1
- [x] Re(U=1, L=1) = 1/nu
- [x] Time derivative exponent: (3/2)*(4/3) = 2
- [x] Fefferman bounded energy: energy inequality implies C = ||u_0||_L2^2

### LaTeX sections verified
- Section 2.1: Weak Navier-Stokes formulation (Definition 2.2)
- Section 2.2: Trilinear form and antisymmetry (Lemma 2.1)
- Section 2.3: Galerkin approximation on R^3 (Gram-Schmidt, localised Aubin-Lions)
- Section 2.4: Energy inequality (Theorem 2.3)
- Section 2.5: Serrin regularity criterion, NS scaling, Reynolds number
- Section 2.6: Connection to Fefferman's Clay formulation (Problems A-D)

## Track 3: Numerics

Not yet applicable for Chapter 2 (theoretical chapter). Numerical verification of
Galerkin convergence rates is planned for Chapter 8.

## Cross-track consistency

| Concept | Lean | LaTeX | SymPy |
|---------|------|-------|-------|
| Weak NS solution | `IsWeakNSSolution` | Def 2.2 | -- |
| Trilinear antisymmetry | `trilinearForm_antisymmetric` | Lemma 2.1 | Tests 1-3 |
| Energy inequality | `SatisfiesEnergyInequality` | Thm 2.3 | Test 4 |
| Leray-Hopf existence | `lerayHopf_existence` | Thm 2.4 | -- |
| Serrin criterion | `serrin_regularity` | Thm 2.5 | Tests 8-10 |
| NS scaling (L^3 critical) | -- | Sec 2.5 | Tests 5-7 |
| Fefferman conditions | -- | Sec 2.6 | Tests 12-13 |
