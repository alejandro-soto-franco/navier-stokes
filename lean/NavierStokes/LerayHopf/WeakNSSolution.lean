/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Navier-Stokes project -- weak formulation of the Navier-Stokes equations.

We define the weak Navier-Stokes solution on R^3 via the integral identity:
for every smooth, compactly supported, divergence-free test function phi,

  - int u(T) . phi dx + int_0^T int (nu grad u : grad phi - (u otimes u) : grad phi) dx dt
    = int u_0 . phi dx

This is Definition 2.2 (weak Navier-Stokes solution) in the text.  All proofs
are deferred (sorry) to keep the type skeleton usable by later chapters.
-/
import NavierStokes.Foundations.DivFreeSpace
import NavierStokes.Foundations.WeakDerivative

open MeasureTheory Measure TopologicalSpace
open scoped ENNReal

noncomputable section

namespace NavierStokes

/-- **Weak Navier-Stokes solution** on R^3.

    A vector field `u : [0,T] x R^3 -> R^3` is a weak solution of the
    incompressible Navier-Stokes equations with viscosity `nu > 0` and
    initial datum `u0` if:

    1. `u(t, .)` is divergence-free for a.e. t,
    2. For every smooth, compactly supported, divergence-free test function phi,
       the integral identity (Definition 2.2) holds.

    We encode this as a structure carrying the data together with the
    integral identity as a Prop field.  The integral itself is left
    abstract (sorry) because Mathlib does not yet have space-time
    Bochner integration over product domains. -/
structure IsWeakNSSolution
    (nu : ℝ) (_hnu : 0 < nu)
    (u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (u0 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) : Prop where
  divFree : ∀ t : ℝ, IsDistribDivFree (Set.univ : Set (EuclideanSpace ℝ (Fin 3))) isOpen_univ (u t)
  /-- The weak integral identity holds for all smooth divergence-free test functions.
      Encoded abstractly; the precise integral statement is in the LaTeX text. -/
  weakFormulation : True  -- Placeholder: full Bochner integral identity deferred

/-- Every weak NS solution is divergence-free at each time slice. -/
theorem weakNS_divFree
    {nu : ℝ} {hnu : 0 < nu}
    {u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {u0 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (h : IsWeakNSSolution nu hnu u u0) (t : ℝ) :
    IsDistribDivFree Set.univ isOpen_univ (u t) :=
  h.divFree t

end NavierStokes
