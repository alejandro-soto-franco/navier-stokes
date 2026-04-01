/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Navier-Stokes project — Poincare inequality.

The Poincare inequality states that on a bounded domain Omega in R^n, for functions
u in H^1_0(Omega) (i.e., zero trace on the boundary), the L^2 norm of u is controlled
by the L^2 norm of the gradient:

  ||u||_{L^2(Omega)} <= C_P * ||grad u||_{L^2(Omega)}

where C_P > 0 depends only on Omega.  For convex domains, the optimal constant satisfies
C_P <= diam(Omega) / sqrt(n) (Payne-Weinberger 1960).

We state a single combined theorem for convex bounded domains, subsuming both the
general Poincare inequality (for the convex case) and the Payne-Weinberger constant
bound. The proof uses the fundamental theorem of calculus along line segments in the
convex domain combined with Cauchy-Schwarz, avoiding Rellich-Kondrachov compactness.
-/
import NavierStokes.Foundations.SobolevSpace

open MeasureTheory Measure TopologicalSpace Metric
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

/-! ## Poincare inequality for convex bounded domains

The proof strategy for convex Omega bypasses Rellich-Kondrachov entirely:

1. **Smooth functions (1D FTC + Cauchy-Schwarz):** For phi in C^inf_c(Omega) and x in
   Omega, since Omega is convex and phi vanishes outside Omega, integrate along a line
   segment from the boundary to x:

     |phi(x)|^2 <= diam(Omega) * integral_0^{diam} |grad phi(gamma(s))|^2 ds

   Integrate over x, average over n coordinate directions, apply Fubini:

     integral_Omega |phi|^2 dx <= (diam Omega)^2 / n * sum_i integral_Omega |d_i phi|^2 dx

2. **H^1_0 passage to limit:** For u in H^1_0(Omega), the `IsH1Zero` property provides
   phi_k in C^inf_c(Omega) with phi_k -> u in H^1. Apply step 1 to each phi_k, then
   pass to the limit using L^2 continuity.

The proof requires Fubini + line integrals (Category C).
-/

/-- **Poincare inequality for convex bounded domains (Payne-Weinberger 1960).**

For any convex bounded open set Omega in R^n, every u in H^1_0(Omega) satisfies:

  integral_Omega |u|^2 dx <= (diam Omega)^2 / n * sum_i integral_Omega |d_i u|^2 dx

Equivalently, ||u||_{L^2} <= (diam Omega / sqrt n) * ||grad u||_{L^2}.

This subsumes both the general Poincare inequality (for convex domains, where convexity
implies connectedness) and the Payne-Weinberger bound on the optimal constant.

*Proof sketch:* For phi in C^inf_c(Omega) on convex Omega, the 1D FTC along line segments
combined with Cauchy-Schwarz and Fubini gives the estimate with explicit constant
(diam Omega)^2 / n. For u in H^1_0(Omega), use the IsH1Zero approximation property and
pass to the limit.

Category C: the 1D FTC + Cauchy-Schwarz + Fubini chain requires line integration
infrastructure not yet available in Mathlib. -/
theorem poincare_inequality_convex
    (hBdd : Bornology.IsBounded Ω)
    (hConvex : Convex ℝ Ω) :
    ∀ (u : SobolevH1Zero Ω hΩ),
      l2NormSq Ω u.val.f ≤ (diam Ω) ^ 2 / ↑n * gradientL2NormSq Ω hΩ u.val := by
  sorry

end NavierStokes
