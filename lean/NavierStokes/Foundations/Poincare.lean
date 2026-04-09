/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Navier-Stokes project — Poincare inequality.

The Poincare inequality states that on a bounded domain Omega in R^n, for functions
u in H^1_0(Omega) (i.e., zero trace on the boundary), the L^2 norm of u is controlled
by the L^2 norm of the gradient:

  ||u||_{L^2(Omega)} <= C_P * ||grad u||_{L^2(Omega)}

where C_P > 0 depends only on Omega.  For convex domains, the optimal constant satisfies
C_P <= diam(Omega) / sqrt(n) (Payne-Weinberger 1960).

The proof is structured as:
  1. `poincare_slice`: per-direction bound via Fubini + `poincare_1d` (sorry: Fubini step)
  2. `poincare_smooth`: average over n directions (proved, uses `poincare_slice`)
  3. `poincare_inequality_convex`: H^1_0 limit passage (sorry: approximation argument)
-/
import NavierStokes.Foundations.SobolevSpace
import Mathlib.Analysis.FunctionalSpaces.PoincareInequality

open MeasureTheory Measure TopologicalSpace Metric Set
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace NavierStokes

variable {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)

/-- The L^2 norm squared of a function on Omega: integral_Omega |u|^2 dx. -/
def l2NormSq (f : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  ∫ x in Ω, f x ^ 2

/-- The squared L^2 norm of the gradient of u in H^1, defined as the sum of squared
    L^2 norms of all weak partial derivatives:
    ||grad u||^2_{L^2} = sum_{i=1}^{n} integral_Omega |partial_i u|^2 dx. -/
def gradientL2NormSq (u : SobolevH1 Ω hΩ) : ℝ :=
  ∑ i : Fin n, ∫ x in Ω, u.weakDeriv i x ^ 2

/-! ## Poincare inequality for smooth compactly supported functions

The 1D Poincare inequality (`MeasureTheory.poincare_1d`) gives, for each coordinate
slice through a convex bounded domain:

  integral |phi|^2 dx_i <= L_i^2 * integral |d_i phi|^2 dx_i

where L_i is the width of Omega in direction i (at most diam Omega).

Fubini over the remaining coordinates and averaging over n directions yields:

  integral_Omega |phi|^2 <= (diam Omega)^2 / n * sum_i integral_Omega |d_i phi|^2
-/

/-- For each coordinate direction i, the 1D Poincare inequality gives:
    ∫_Ω |φ|² ≤ diam(Ω)² * ∫_Ω |∂_i φ|²
    This uses Fubini to decompose the n-dimensional integral into 1D slices,
    applying `MeasureTheory.poincare_1d` to each slice.

    The decomposition uses `MeasurableEquiv.piFinSuccAbove` to split
    `(Fin n → ℝ) ≃ᵐ ℝ × (Fin (n-1) → ℝ)` (isolating coordinate i),
    then `setIntegral_prod` (Fubini) to integrate the inner 1D slice.
    On each slice, φ has compact support inside a 1D interval of length ≤ diam(Ω),
    so `poincare_1d` applies with constant diam(Ω)². -/
private theorem poincare_slice
    (hBdd : Bornology.IsBounded Ω)
    (hConvex : Convex ℝ Ω)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : ContDiff ℝ ∞ φ)
    (hsupp : tsupport φ ⊆ Ω)
    (i : Fin n) :
    l2NormSq Ω φ ≤ (diam Ω) ^ 2 *
      ∫ x in Ω, (fderiv ℝ φ x (EuclideanSpace.single i 1)) ^ 2 := by
  -- Fubini decomposition:
  -- 1. Use MeasurableEquiv.piFinSuccAbove to write ℝ^n = ℝ × ℝ^{n-1}
  -- 2. The set Ω decomposes into fibers Ω_{x_{-i}} = {t : (x_1,...,t,...,x_n) ∈ Ω}
  -- 3. By Fubini: ∫_Ω |φ|² = ∫_{ℝ^{n-1}} (∫_{Ω_{x_{-i}}} |φ(x_i, x_{-i})|² dx_i) dx_{-i}
  -- 4. On each fiber: φ has compact support, fiber is convex (width ≤ diam Ω)
  -- 5. Apply poincare_1d: ∫_{fiber} |φ|² ≤ diam(Ω)² * ∫_{fiber} |∂_i φ|²
  -- 6. Integrate back over x_{-i}: ∫_Ω |φ|² ≤ diam(Ω)² * ∫_Ω |∂_i φ|²
  sorry

/-- Poincare inequality for smooth compactly supported functions on a bounded convex
    domain. Averages the per-direction bound from `poincare_slice` over n directions. -/
private theorem poincare_smooth
    (hn : 0 < n)
    (hBdd : Bornology.IsBounded Ω)
    (hConvex : Convex ℝ Ω)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : ContDiff ℝ ∞ φ)
    (hsupp : tsupport φ ⊆ Ω) :
    l2NormSq Ω φ ≤ (diam Ω) ^ 2 / ↑n * ∑ i : Fin n,
      ∫ x in Ω, (fderiv ℝ φ x (EuclideanSpace.single i 1)) ^ 2 := by
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  -- Sum the per-direction bounds
  have hsum : ↑n * l2NormSq Ω φ ≤ (diam Ω) ^ 2 * ∑ i : Fin n,
      ∫ x in Ω, (fderiv ℝ φ x (EuclideanSpace.single i 1)) ^ 2 := by
    calc ↑n * l2NormSq Ω φ
        = ∑ _ : Fin n, l2NormSq Ω φ := by simp [Finset.sum_const, Finset.card_fin]
      _ ≤ ∑ i : Fin n, (diam Ω) ^ 2 *
            ∫ x in Ω, (fderiv ℝ φ x (EuclideanSpace.single i 1)) ^ 2 :=
          Finset.sum_le_sum fun i _ => poincare_slice Ω hBdd hConvex φ hφ hsupp i
      _ = (diam Ω) ^ 2 * ∑ i : Fin n,
            ∫ x in Ω, (fderiv ℝ φ x (EuclideanSpace.single i 1)) ^ 2 :=
          by rw [← Finset.mul_sum]
  -- Divide both sides by n
  rwa [div_mul_eq_mul_div, le_div_iff₀ hn_pos, mul_comm]

/-! ## Poincare inequality for H^1_0 via limit passage -/

/-- **Poincare inequality for convex bounded domains (Payne-Weinberger 1960).**

For any convex bounded open set Omega in R^n, every u in H^1_0(Omega) satisfies:

  integral_Omega |u|^2 dx <= (diam Omega)^2 / n * sum_i integral_Omega |d_i u|^2 dx

Equivalently, ||u||_{L^2} <= (diam Omega / sqrt n) * ||grad u||_{L^2}.

The proof applies `poincare_smooth` to the smooth approximants from `IsH1Zero` and
passes to the limit. -/
theorem poincare_inequality_convex
    (hBdd : Bornology.IsBounded Ω)
    (hConvex : Convex ℝ Ω) :
    ∀ (u : SobolevH1Zero Ω hΩ),
      l2NormSq Ω u.val.f ≤ (diam Ω) ^ 2 / ↑n * gradientL2NormSq Ω hΩ u.val := by
  intro ⟨u, hu⟩
  -- Approximate u by smooth φ_k via IsH1Zero, apply poincare_smooth to each φ_k,
  -- pass to the limit using L^2 norm continuity.
  sorry

end NavierStokes
