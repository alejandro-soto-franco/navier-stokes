/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Navier-Stokes project — Sobolev embedding theorems.

The classical Sobolev embedding theorems assert:
  - (Subcritical) W^{1,p}(Omega) embeds continuously into L^{p*}(Omega) for 1 ≤ p < n,
    where p* = np/(n-p) is the Sobolev conjugate exponent.
  - (Supercritical) W^{1,p}(Omega) embeds continuously into C^{0,alpha}(Omega) for p > n,
    where alpha = 1 - n/p is the Hölder exponent.
These are stated here with sorry proofs; the Gagliardo-Nirenberg-Sobolev inequality in
Mathlib.Analysis.FunctionalSpaces.SobolevInequality provides the analytical core of the
subcritical case for compactly supported smooth functions.
-/
import NavierStokes.Foundations.SobolevSpace
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

open MeasureTheory Measure TopologicalSpace
open scoped ENNReal NNReal

noncomputable section

namespace NavierStokes

variable {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)

/-- The Sobolev conjugate exponent p* = np/(n-p) for 1 ≤ p < n.
    This is the unique exponent for which the Sobolev embedding W^{1,p} ↪ L^{p*} is
    scale-invariant under the dilation x ↦ λx on ℝ^n. -/
noncomputable def sobolevConjugate (p : ℝ) (hn : 0 < n) (hp : 1 ≤ p) (hpn : p < (n : ℝ)) : ℝ :=
  (n : ℝ) * p / ((n : ℝ) - p)

/-- The Sobolev conjugate exponent satisfies p* > p when 1 ≤ p < n. -/
theorem sobolevConjugate_gt (p : ℝ) (hn : 0 < n) (hp : 1 ≤ p) (hpn : p < (n : ℝ)) :
    p < sobolevConjugate p hn hp hpn := by
  -- p < np/(n-p) because n*p - p*(n-p) = p^2 > 0 for p > 0.
  sorry

/-- The Sobolev conjugate exponent satisfies 1/p* = 1/p - 1/n (the dimensional relation). -/
theorem sobolevConjugate_inv (p : ℝ) (hn : 0 < n) (hp : 1 < p) (hpn : p < (n : ℝ)) :
    1 / sobolevConjugate p hn (le_of_lt hp) hpn = 1 / p - 1 / n := by
  -- Algebraic identity: 1/(np/(n-p)) = (n-p)/(np) = 1/p - 1/n.
  sorry

/-- **Sobolev Embedding (Subcritical case)**: W^{1,p}(Omega) embeds continuously into
    L^{p*}(Omega) when 1 ≤ p < n.  Every u in W^{1,p} has its L^{p*} norm controlled
    by a constant times the W^{1,p} seminorm (the L^p norm of the gradient).
    This is a consequence of the Gagliardo-Nirenberg-Sobolev inequality. -/
theorem sobolev_embedding_subcritical
    (p : ℝ) (hp : 1 ≤ p) (hpn : p < (n : ℝ)) (hn : 0 < n)
    (u : SobolevW1p Ω hΩ (ENNReal.ofReal p)) :
    MemLp u.f (ENNReal.ofReal (sobolevConjugate p hn hp hpn)) (volume.restrict Ω) := by
  sorry

/-- **Sobolev Embedding (Supercritical case)**: W^{1,p}(Omega) embeds continuously into
    the Hölder space C^{0,alpha}(Omega) when p > n, with alpha = 1 - n/p.
    Functions in W^{1,p} for p > n are not just measurable but actually continuous and
    Hölder continuous with the indicated exponent. -/
theorem sobolev_embedding_supercritical
    (p : ℝ) (hp : (n : ℝ) < p)
    (u : SobolevW1p Ω hΩ (ENNReal.ofReal p)) :
    -- u.f extends to a continuous function on Omega (up to a.e. modification)
    -- with Hölder exponent alpha = 1 - n/p.
    -- We state the conclusion as: u.f is continuous on Omega (the full Hölder regularity
    -- requires the HolderWith predicate; here we state continuity as the weaker form).
    ContinuousOn u.f Ω := by
  sorry

end NavierStokes
