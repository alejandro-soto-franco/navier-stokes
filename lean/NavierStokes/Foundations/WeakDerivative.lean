/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Navier-Stokes project -- weak derivatives of Lp functions.

We define the weak partial derivative of a locally integrable function
on an open subset Omega subseteq R^n and prove basic properties.
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open MeasureTheory Measure TopologicalSpace
open scoped ENNReal

noncomputable section

namespace NavierStokes

variable {n : ℕ}

/-- A function `g` is a weak partial derivative of `f` with respect to the `i`-th coordinate
    on the open set `Ω ⊆ ℝⁿ` if for every smooth compactly supported test function `φ`
    supported in `Ω`,
      ∫ f * (∂φ/∂xᵢ) dx = - ∫ g * φ dx.
    This is the distributional definition restricted to locally integrable functions.
    The integration-by-parts identity encodes that g is the distributional i-th partial
    derivative of f in the sense of Schwartz. -/
def IsWeakPartialDeriv
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (_hΩ : IsOpen Ω)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (i : Fin n)
    (_hf : LocallyIntegrableOn f Ω)
    (_hg : LocallyIntegrableOn g Ω) : Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
    ContDiff ℝ ⊤ φ →
    HasCompactSupport φ →
    tsupport φ ⊆ Ω →
    ∫ x in Ω, f x * (fderiv ℝ φ x (EuclideanSpace.single i 1)) =
    - ∫ x in Ω, g x * φ x

/-- Weak partial derivatives are unique a.e. when they exist.
    If `g₁` and `g₂` are both weak i-th partial derivatives of `f` on `Ω`, then
    `g₁ = g₂` a.e. on `Ω` with respect to the Lebesgue measure restricted to `Ω`.
    This follows from the fundamental lemma of the calculus of variations: any locally
    integrable function whose integral against every test function vanishes must be zero
    a.e. -/
theorem weakPartialDeriv_unique
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω)
    {f g₁ g₂ : EuclideanSpace ℝ (Fin n) → ℝ}
    {i : Fin n}
    {hf : LocallyIntegrableOn f Ω}
    {hg₁ : LocallyIntegrableOn g₁ Ω}
    {hg₂ : LocallyIntegrableOn g₂ Ω}
    (h₁ : IsWeakPartialDeriv Ω hΩ f g₁ i hf hg₁)
    (h₂ : IsWeakPartialDeriv Ω hΩ f g₂ i hf hg₂) :
    g₁ =ᵐ[volume.restrict Ω] g₂ := by
  sorry -- Uses fundamental lemma: AEEqOfIntegralContDiff

end NavierStokes
