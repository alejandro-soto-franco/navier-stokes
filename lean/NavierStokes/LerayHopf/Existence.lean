/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Navier-Stokes project -- existence of Leray-Hopf weak solutions.

The Leray-Hopf existence theorem (Theorem 2.4 in the text) states:

  For every u_0 in L^2_sigma(R^3) and nu > 0, there exists a
  weak solution u of the Navier-Stokes equations satisfying
  the energy inequality.

The proof proceeds via Galerkin approximation on R^3:
  1. Gram-Schmidt orthonormalisation of C_c^infty cap L^2_sigma
  2. Finite-dimensional ODE for Galerkin coefficients
  3. A priori energy estimates (trilinear antisymmetry)
  4. Localised Aubin-Lions compactness + diagonal argument
  5. Passage to the limit with compact support trick
  6. Energy inequality via weak lower semicontinuity (Fatou)

All proofs are deferred (sorry).
-/
import NavierStokes.LerayHopf.EnergyInequality
import NavierStokes.LerayHopf.TrilinearForm

open MeasureTheory Measure TopologicalSpace
open scoped ENNReal

noncomputable section

namespace NavierStokes

/-- A **Leray-Hopf weak solution** is a weak NS solution that additionally
    satisfies the energy inequality and has strong L^2 continuity at t=0. -/
structure IsLerayHopfSolution
    (nu : ℝ) (hnu : 0 < nu)
    (u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (u0 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) : Prop where
  weakSol : IsWeakNSSolution nu hnu u u0
  energyIneq : SatisfiesEnergyInequality nu hnu u u0
  /-- Strong L^2 continuity at the initial time: ||u(t) - u_0||_L2 -> 0 as t -> 0+. -/
  initialContinuity : True  -- Placeholder

/-- **Leray-Hopf existence theorem** (Theorem 2.4).

    For every divergence-free initial datum u_0 in L^2(R^3) and every
    viscosity nu > 0, there exists a Leray-Hopf weak solution.

    The proof uses Galerkin approximation on R^3 (Section 2.3 of the text). -/
theorem lerayHopf_existence
    (nu : ℝ) (hnu : 0 < nu)
    (u0 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (_hu0 : u0 ∈ L2sigma (Set.univ : Set (EuclideanSpace ℝ (Fin 3))) isOpen_univ) :
    ∃ u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsLerayHopfSolution nu hnu u u0 := by
  sorry

/-- **Serrin regularity criterion** (Theorem 2.5).

    If a Leray-Hopf solution u additionally belongs to L^q_t L^r_x
    with 2/q + 3/r = 1 and r > 3, then u is smooth.

    This is the bridge from weak to strong solutions: an extra
    integrability condition beyond the energy class suffices. -/
theorem serrin_regularity
    {nu : ℝ} {hnu : 0 < nu}
    {u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {u0 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (_h : IsLerayHopfSolution nu hnu u u0)
    (_hSerrin : True) :  -- Placeholder for L^q L^r condition with 2/q + 3/r = 1
    True := by  -- Placeholder for smoothness conclusion
  trivial

end NavierStokes
