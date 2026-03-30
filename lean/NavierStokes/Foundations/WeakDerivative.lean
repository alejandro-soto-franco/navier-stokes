/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Navier-Stokes project -- weak derivatives of Lp functions.

We define the weak partial derivative of a locally integrable function
on an open subset Omega subseteq R^n and prove basic properties.
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open MeasureTheory Measure TopologicalSpace Function
open scoped ENNReal ContDiff

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
    ContDiff ℝ ∞ φ →
    HasCompactSupport φ →
    tsupport φ ⊆ Ω →
    ∫ x in Ω, f x * (fderiv ℝ φ x (EuclideanSpace.single i 1)) =
    - ∫ x in Ω, g x * φ x

/-- Weak partial derivatives are unique a.e. when they exist.
    If `g₁` and `g₂` are both weak i-th partial derivatives of `f` on `Ω`, then
    `g₁ = g₂` a.e. on `Ω` with respect to the Lebesgue measure restricted to `Ω`.
    This follows from the fundamental lemma of the calculus of variations: any locally
    integrable function whose integral against every test function vanishes must be zero
    a.e. Applied to `g₁ - g₂` via `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`. -/
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
  -- Step 1: From h₁ and h₂ (same LHS), derive ∫ g₁ * φ = ∫ g₂ * φ for all test φ.
  have h_eq : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      ∫ x in Ω, g₁ x * φ x = ∫ x in Ω, g₂ x * φ x := by
    intro φ hφ hφ_supp hφ_Ω
    have eq₁ := h₁ φ hφ hφ_supp hφ_Ω
    have eq₂ := h₂ φ hφ hφ_supp hφ_Ω
    linarith
  -- Step 2: Apply the fundamental lemma to g₁ - g₂ on the open set Ω.
  rw [Filter.EventuallyEq, ae_restrict_iff' hΩ.measurableSet]
  have h_fund : ∀ᵐ x ∂volume, x ∈ Ω → (g₁ - g₂) x = 0 := by
    apply IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hΩ (hg₁.sub hg₂)
    intro φ hφ hφ_supp hφ_Ω
    -- φ vanishes outside Ω (since tsupport φ ⊆ Ω), so the full integral equals
    -- the set integral over Ω.
    have h_vanish : ∀ x, x ∉ Ω → (fun x => φ x • (g₁ - g₂) x) x = 0 := by
      intro x hx
      have : x ∉ support φ := fun hmem => hx (hφ_Ω (subset_tsupport φ hmem))
      simp [notMem_support.mp this]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω)
        (fun x hx => h_vanish x hx)]
    simp only [smul_eq_mul, Pi.sub_apply]
    rw [show (fun x => φ x * (g₁ x - g₂ x)) =
        (fun x => g₁ x * φ x - g₂ x * φ x) from by ext x; ring]
    -- Integrability of g_i * φ on Ω: integrable on tsupport φ (compact), extend to Ω
    -- since φ vanishes on Ω \ tsupport φ.
    have h_int₁ : IntegrableOn (fun x => g₁ x * φ x) Ω volume :=
      ((hg₁.integrableOn_compact_subset hφ_Ω hφ_supp.isCompact).mul_continuousOn
        hφ.continuous.continuousOn hφ_supp.isCompact).of_forall_diff_eq_zero
        hΩ.measurableSet (fun x hx => by
          have : x ∉ tsupport φ := fun h => hx.2 h
          have : φ x = 0 := image_eq_zero_of_notMem_tsupport this
          simp [this])
    have h_int₂ : IntegrableOn (fun x => g₂ x * φ x) Ω volume :=
      ((hg₂.integrableOn_compact_subset hφ_Ω hφ_supp.isCompact).mul_continuousOn
        hφ.continuous.continuousOn hφ_supp.isCompact).of_forall_diff_eq_zero
        hΩ.measurableSet (fun x hx => by
          have : x ∉ tsupport φ := fun h => hx.2 h
          have : φ x = 0 := image_eq_zero_of_notMem_tsupport this
          simp [this])
    rw [integral_sub h_int₁ h_int₂]
    linarith [h_eq φ hφ hφ_supp hφ_Ω]
  -- Step 3: Convert from ∀ᵐ (g₁ - g₂) = 0 to g₁ = g₂.
  filter_upwards [h_fund] with x hx hxΩ
  have := hx hxΩ
  simp [Pi.sub_apply] at this
  linarith

end NavierStokes
