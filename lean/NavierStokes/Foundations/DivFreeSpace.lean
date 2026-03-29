/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Navier-Stokes project -- divergence-free L^2 vector fields.

We define the Hilbert space L^2_sigma(Omega) of square-integrable divergence-free
vector fields, state the Helmholtz orthogonal decomposition
  L^2(Omega; R^n) = L^2_sigma(Omega) oplus { grad p : p in H^1(Omega) },
and introduce the Leray projector P : L^2 -> L^2_sigma together with its
key properties (idempotence and self-adjointness).

All proofs are deferred (sorry) to keep the type-level skeleton usable by
subsequent chapters of the formalisation.
-/
import NavierStokes.Foundations.WeakDerivative
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic

open MeasureTheory Measure TopologicalSpace
open scoped ENNReal

noncomputable section

namespace NavierStokes

/-! ## Distributional divergence-free condition -/

/-- A vector field `u : ℝⁿ → ℝⁿ` is *distributionally divergence-free* on the open
    set `Ω ⊆ ℝⁿ` if for every smooth compactly supported scalar test function `φ`
    with support in `Ω`,

      ∑ᵢ ∫_Ω uᵢ(x) · ∂ᵢφ(x) dx = 0.

    This is the weak formulation of `div u = 0`: integration by parts turns the
    distributional divergence into minus the above sum, so vanishing for all test
    functions is equivalent to div u = 0 in the sense of distributions.

    We index components of EuclideanSpace via `i : Fin n` and access them via
    `(u x) i`. This mirrors the API of `IsWeakPartialDeriv` in WeakDerivative.lean,
    which tests against `fderiv ℝ φ x (EuclideanSpace.single i 1)` per coordinate. -/
def IsDistribDivFree
    {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (_hΩ : IsOpen Ω)
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
    ContDiff ℝ ⊤ φ →
    HasCompactSupport φ →
    tsupport φ ⊆ Ω →
    ∑ i : Fin n,
      ∫ x in Ω, (u x) i * (fderiv ℝ φ x (EuclideanSpace.single i 1)) = 0

/-! ## The space L^2_sigma -/

/-- `L2sigma Ω hΩ` is the set of vector fields that are simultaneously
    square-integrable on `Ω` and distributionally divergence-free:

      L^2_sigma(Ω) := { u : ℝⁿ → ℝⁿ | MemLp u 2 (volume.restrict Ω)
                                         ∧ IsDistribDivFree Ω hΩ u }.

    This is the natural phase space for the velocity field in the incompressible
    Navier-Stokes equations. -/
def L2sigma
    {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω) :
    Set (EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :=
  { u | MemLp u 2 (volume.restrict Ω) ∧ IsDistribDivFree Ω hΩ u }

/-! ### Closure of L^2_sigma -/

/-- `L2sigma Ω hΩ` is closed in the L^2 topology.

    *Proof sketch (sorry):* The divergence-free condition is linear in `u` and is
    tested against fixed smooth functions; an L^2-convergent sequence passes the
    condition to its limit by dominated convergence. -/
theorem l2sigma_isClosed
    {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω) :
    IsClosed (L2sigma Ω hΩ) := by
  sorry

/-! ## Gradient fields and Helmholtz decomposition -/

/-- The space of *gradient fields* on `Ω`:
      G(Ω) := { v | ∃ p ∈ H^1(Ω), ∀ x i, v(x)_i = ∂_i p(x) }.
    These are L^2 vector fields arising as gradients of scalar potentials.
    Together with `L2sigma` they give the two summands in the Helmholtz splitting. -/
def GradientFields
    {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (_hΩ : IsOpen Ω) :
    Set (EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :=
  { v | ∃ p : EuclideanSpace ℝ (Fin n) → ℝ,
          ContDiff ℝ 1 p ∧
          MemLp p 2 (volume.restrict Ω) ∧
          ∀ (x : EuclideanSpace ℝ (Fin n)) (i : Fin n),
            (v x) i = fderiv ℝ p x (EuclideanSpace.single i 1) }

/-- **Helmholtz decomposition** (sorry):
    Every `u ∈ L^2(Ω; ℝⁿ)` decomposes uniquely as  u = w + g,
    where `w ∈ L^2_sigma` and `g ∈ GradientFields`, and the two components are
    L^2-orthogonal:  ∫_Ω ⟨w(x), g(x)⟩ dx = 0.

    *Proof sketch (sorry):* Standard Hilbert-space projection onto the closed
    subspace `L^2_sigma`; the orthogonal complement is `GradientFields`
    by integration by parts (de Rham). -/
theorem helmholtz_decomposition
    {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω)
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (_hu : MemLp u 2 (volume.restrict Ω)) :
    ∃ (w : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      w ∈ L2sigma Ω hΩ ∧
      g ∈ GradientFields Ω hΩ ∧
      (∀ x, u x = w x + g x) ∧
      (∫ x in Ω, @inner ℝ _ _ (w x) (g x) = (0 : ℝ)) := by
  sorry

/-! ## Leray projector -/

/-- The **Leray projector** maps each L^2 vector field to the `L^2_sigma`-component
    of its Helmholtz decomposition.

    Given `u ∈ L^2(Ω; ℝⁿ)`, write `u = w + ∇p` (Helmholtz); then
      `lerayProjector Ω hΩ u := w`.

    The body is a sorry-stub extracting the first witness from
    `helmholtz_decomposition`. Subsequent lemmas depend only on the stated types
    and properties, not the computational content of this definition. -/
def lerayProjector
    {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω)
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  (helmholtz_decomposition Ω hΩ u (by sorry)).choose

/-! ### Properties of the Leray projector -/

/-- The Leray projector is **idempotent**: `P(Pu) = Pu`.
    Projecting an element of `L^2_sigma` onto `L^2_sigma` returns it unchanged. -/
theorem lerayProjector_idempotent
    {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω)
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (_hu : MemLp u 2 (volume.restrict Ω)) :
    lerayProjector Ω hΩ (lerayProjector Ω hΩ u) = lerayProjector Ω hΩ u := by
  sorry

/-- The Leray projector is **self-adjoint** w.r.t. the L^2 inner product:
      ∫_Ω ⟨Pu, v⟩ dx = ∫_Ω ⟨u, Pv⟩ dx
    for all `u, v ∈ L^2(Ω; ℝⁿ)`.
    Orthogonal projections on a Hilbert space are always self-adjoint. -/
theorem lerayProjector_selfAdjoint
    {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω)
    (u v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (_hu : MemLp u 2 (volume.restrict Ω))
    (_hv : MemLp v 2 (volume.restrict Ω)) :
    ∫ x in Ω, @inner ℝ _ _ (lerayProjector Ω hΩ u x) (v x) =
    ∫ x in Ω, @inner ℝ _ _ (u x) (lerayProjector Ω hΩ v x) := by
  sorry

end NavierStokes
