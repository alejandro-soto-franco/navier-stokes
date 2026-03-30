/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Navier-Stokes project -- trilinear form and its antisymmetry.

The trilinear form b(u, v, w) = int sum_{i,j} u_j (d_j v_i) w_i dx
plays a central role in the energy theory of Navier-Stokes.  The key
identity (Lemma 2.1 in the text) is:

  b(u, v, v) = 0   for all divergence-free u in H^1.

This follows from integration by parts:
  b(u, v, v) = (1/2) int u . grad(|v|^2) dx = -(1/2) int (div u)|v|^2 dx = 0.

All proofs are deferred (sorry).
-/
import NavierStokes.Foundations.DivFreeSpace

open MeasureTheory Measure TopologicalSpace
open scoped ENNReal

noncomputable section

namespace NavierStokes

/-- The trilinear form b(u, v, w) arising from the nonlinear term in
    the Navier-Stokes weak formulation.

    b(u, v, w) = sum_{i,j} int u_j (partial_j v_i) w_i dx.

    This is defined abstractly as a real number depending on three
    vector fields.  The precise integral definition requires Bochner
    integration over R^3 with product derivatives; we leave the body
    as sorry and state the key property below. -/
def trilinearForm
    (u v w : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) : ℝ :=
  sorry

/-- **Antisymmetry of the trilinear form** (Lemma 2.1).

    For divergence-free u with sufficient regularity,
      b(u, v, v) = 0.

    Proof sketch: b(u,v,v) = (1/2) int u . grad(|v|^2)
    = -(1/2) int (div u) |v|^2 = 0. -/
theorem trilinearForm_antisymmetric
    (u v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (_hu : IsDistribDivFree (Set.univ : Set (EuclideanSpace ℝ (Fin 3))) isOpen_univ u) :
    trilinearForm u v v = 0 := by
  sorry

end NavierStokes
