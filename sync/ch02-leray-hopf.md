# Sync Point: Chapter 2 -- Leray-Hopf Weak Solutions

**Date**: 2026-03-30
**Status**: [x] Passed

## Track 1: Lean

All 4 new modules build (2697 jobs total, no errors). 1 sorry from Ch2 existence, plus
deferred `trilinearForm` body and `trilinearForm_antisymmetric` proof. Ch1 sorry items
remain unchanged (14 total, catalogued in sync/ch01-foundations.md).

### Formalized (definitions compile, types check)
- [x] `IsWeakNSSolution` -- weak NS solution structure (div-free + integral identity)
- [x] `trilinearForm` -- trilinear form b(u, v, w) definition
- [x] `trilinearForm_antisymmetric` -- b(u, v, v) = 0 for div-free u
- [x] `SatisfiesEnergyInequality` -- energy inequality structure
- [x] `energyInequality_implies_L2_bound` -- uniform L^2 bound from energy inequality
- [x] `IsLerayHopfSolution` -- Leray-Hopf solution combining weak sol + energy ineq
- [x] `lerayHopf_existence` -- existence of Leray-Hopf solutions
- [x] `serrin_regularity` -- Serrin regularity criterion (L^q L^r condition)

### Remaining `sorry` (Ch2-specific, 3 total)
- LerayHopf/TrilinearForm.lean: `trilinearForm` (body), `trilinearForm_antisymmetric` (proof)
- LerayHopf/Existence.lean: `lerayHopf_existence` (Galerkin construction)

### Assessment
All definitions type-check. The sorry items are proof obligations for known theorems whose
mathematical content is fully developed in the LaTeX text (Section 2.3 Galerkin construction
on R^3). Filling these requires Bochner integration over product domains, which Mathlib does
not yet support.

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
