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

open MeasureTheory Measure TopologicalSpace Function
open scoped ENNReal ContDiff

noncomputable section

namespace NavierStokes

/-- The trilinear form b(u, v, w) arising from the nonlinear term in
    the Navier-Stokes weak formulation.

    b(u, v, w) = sum_{i,j} int_{R^3} u_j(x) * (partial_j v_i)(x) * w_i(x) dx.

    The partial derivative partial_j v_i is computed as the j-th directional
    derivative of the i-th component of v, using `fderiv`. The integral is
    Bochner integration over all of R^3.

    When u, v, w are sufficiently regular (e.g. v in H^1, u and w in L^2 with
    the product in L^1), this is well-defined. The integrability is not enforced
    in the definition; non-integrable terms produce 0 by Mathlib convention. -/
def trilinearForm
    (u v w : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    ∫ x, (u x) j * (fderiv ℝ (fun y => (v y) i) x (EuclideanSpace.single j 1)) * (w x) i

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
