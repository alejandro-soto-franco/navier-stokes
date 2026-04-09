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
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Measure TopologicalSpace
open scoped ENNReal NNReal

noncomputable section

namespace NavierStokes

variable {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)

/-- The Sobolev conjugate exponent p* = np/(n-p) for 1 ≤ p < n.
    This is the unique exponent for which the Sobolev embedding W^{1,p} ↪ L^{p*} is
    scale-invariant under the dilation x ↦ λx on ℝ^n. -/
noncomputable def sobolevConjugate (p : ℝ) (_hn : 0 < n) (_hp : 1 ≤ p) (_hpn : p < (n : ℝ)) : ℝ :=
  (n : ℝ) * p / ((n : ℝ) - p)

/-- The Sobolev conjugate exponent satisfies p* > p when 1 ≤ p < n. -/
theorem sobolevConjugate_gt (p : ℝ) (hn : 0 < n) (hp : 1 ≤ p) (hpn : p < (n : ℝ)) :
    p < sobolevConjugate p hn hp hpn := by
  -- p < np/(n-p) ⟺ p(n-p) < np ⟺ 0 < p² (true for p ≥ 1).
  unfold sobolevConjugate
  have hnp_pos : (0 : ℝ) < (n : ℝ) - p := by linarith
  rw [lt_div_iff₀ hnp_pos]
  nlinarith [sq_nonneg p, sq_abs p]

/-- The Sobolev conjugate exponent satisfies 1/p* = 1/p - 1/n (the dimensional relation). -/
theorem sobolevConjugate_inv (p : ℝ) (hn : 0 < n) (hp : 1 < p) (hpn : p < (n : ℝ)) :
    1 / sobolevConjugate p hn (le_of_lt hp) hpn = 1 / p - 1 / n := by
  -- 1/(np/(n-p)) = (n-p)/(np) = 1/p - 1/n.
  unfold sobolevConjugate
  have hp0 : (0 : ℝ) < p := by linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnp : (0 : ℝ) < (n : ℝ) * p := mul_pos hn0 hp0
  field_simp

/-! ## Continuous linear map norm via orthonormal basis components

The squared operator norm of a CLM on EuclideanSpace decomposes as a sum over
the standard basis, by the Riesz representation theorem for Hilbert spaces.
This is the key auxiliary fact linking the GNS operator-norm bound to the
component-wise L^p norms of the weak derivatives. -/

/-- The squared operator norm of a continuous linear functional on `EuclideanSpace ℝ (Fin m)`
    equals the sum of squared values on the standard basis vectors.
    This follows from `OrthonormalBasis.norm_dual` applied to `EuclideanSpace.basisFun`. -/
private lemma clm_norm_sq_eq_sum_sq {m : ℕ} (L : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :
    ‖L‖ ^ 2 = ∑ i : Fin m, (L (EuclideanSpace.single i 1)) ^ 2 := by
  have h := OrthonormalBasis.norm_dual (EuclideanSpace.basisFun (Fin m) ℝ) L
  simp_rw [EuclideanSpace.basisFun_apply] at h
  exact h

/-- **Sobolev Embedding (Subcritical case)**: W^{1,p}(Omega) embeds continuously into
    L^{p*}(Omega) when 1 ≤ p < n.  Every u in W^{1,p} has its L^{p*} norm controlled
    by a constant times the W^{1,p} seminorm (the L^p norm of the gradient).
    This is a consequence of the Gagliardo-Nirenberg-Sobolev inequality.

    *Proof sketch (sorry):* Mathlib provides the GNS inequality for smooth compactly
    supported functions via `eLpNorm_le_eLpNorm_fderiv_of_eq_inner`
    (`Mathlib.Analysis.FunctionalSpaces.SobolevInequality`), which gives
    `‖u‖_{L^{p*}} ≤ C * ‖fderiv ℝ u‖_{L^p}` for `u : E → F'` with `ContDiff ℝ 1 u`
    and `HasCompactSupport u`, where `(p')⁻¹ = p⁻¹ - (finrank ℝ E)⁻¹`.

    Gap: `SobolevW1p` elements have *weak* derivatives (`u.weakDeriv i`), not classical
    `fderiv`. Bridging requires:
      (1) Density of `C^∞_c(Ω)` in `W^{1,p}(Ω)` (Meyers-Serrin theorem) — not yet in Mathlib;
      (2) A compatible estimate showing `u.weakDeriv i = fderiv ℝ u · e_i` a.e. for smooth u;
      (3) A passage-to-the-limit argument in L^{p*} using the density from (1).
    Category C: requires Meyers-Serrin in Mathlib. -/
theorem sobolev_embedding_subcritical
    (p : ℝ) (hp : 1 ≤ p) (hpn : p < (n : ℝ)) (hn : 0 < n)
    (u : SobolevW1p Ω hΩ (ENNReal.ofReal p)) :
    MemLp u.f (ENNReal.ofReal (sobolevConjugate p hn hp hpn)) (volume.restrict Ω) := by
  sorry

/-- **Sobolev Embedding for H^1_0 (Subcritical, p = 2)**: Every u in H^1_0(Omega) belongs to
    L^{2*}(Omega) where 2* = 2n/(n-2) is the Sobolev conjugate of 2, provided n ≥ 3.

    This is the classical H^1_0 Sobolev embedding; it uses only the L^2 gradient control
    provided by the H^1_0 structure, and hence works for p = 2 specifically (not general p,
    since H^1_0 only guarantees an L^2 approximating gradient).

    Proof strategy (sorry at Lean plumbing level):

    Step 1 (Approximation sequence): By `IsH1Zero`, for each k ∈ ℕ choose φ_k ∈ C^∞_c(Ω)
    with `tsupport φ_k ⊆ Ω` and
      ∫_Ω (u.val.f - φ_k)^2 < 1/(k+1)^2
      ∀ i, ∫_Ω (u.val.weakDeriv i - fderiv ℝ φ_k · (single i 1))^2 < 1/(k+1)^2

    Step 2 (GNS on differences): φ_k - φ_m ∈ C^∞_c with compact support in Ω, so GNS
    (`eLpNorm_le_eLpNorm_fderiv_of_eq_inner` with p = 2, p* = 2n/(n-2)) gives:
      eLpNorm (φ_k - φ_m) (2*) volume ≤ C * eLpNorm (fderiv ℝ (φ_k - φ_m)) 2 volume

    Step 3 (Gradient Cauchy bound): By `clm_norm_sq_eq_sum_sq`:
      ‖fderiv ℝ φ_k x‖^2 = ∑_i (fderiv ℝ φ_k x (single i 1))^2
    so `eLpNorm (fderiv ℝ (φ_k - φ_m)) 2 volume ^ 2 = ∑_i ∫(fderiv ℝ (φ_k - φ_m) · (single i 1))^2`
    ≤ 2 * n * (1/(k+1)^2 + 1/(m+1)^2) by the triangle inequality + IsH1Zero bounds.

    Step 4 (Support/measure conversion): `eLpNorm_restrict_eq_of_support_subset` converts
    between volume and volume.restrict Ω for functions supported in Ω.

    Step 5 (Cauchy completeness): `cauchy_complete_eLpNorm` gives w ∈ L^{2*}(volume.restrict Ω)
    with φ_k → w in L^{2*}(volume.restrict Ω).

    Step 6 (Limit identification): The L^2 convergence φ_k → u.val.f (from IsH1Zero) and
    the L^{2*} convergence φ_k → w both imply convergence in measure (on Ω), so w = u.val.f
    a.e. on Ω. Then `MemLp.ae_eq` concludes MemLp u.val.f (2*) (volume.restrict Ω).

    Category B: all Mathlib pieces exist; remaining gap is connecting eLpNorm of the CLM-valued
    function fderiv to the scalar component integrals (∫(fderiv · (single i 1))^2). -/
theorem sobolev_embedding_subcritical_h10
    (hn3 : 3 ≤ n) -- ensures 2 < n so that 2* = 2n/(n-2) > 2
    (u : SobolevH1Zero Ω hΩ) :
    let p := (2 : ℝ)
    let hn : 0 < n := by omega
    let hp : (1 : ℝ) ≤ 2 := by norm_num
    let hpn : (2 : ℝ) < (n : ℝ) := by exact_mod_cast (show 2 < n by omega)
    MemLp u.val.f (ENNReal.ofReal (sobolevConjugate p hn hp hpn)) (volume.restrict Ω) := by
  intro p hn hp hpn
  -- Extract the H^1_0 approximation structure
  obtain ⟨hu, hiso⟩ := u
  -- hiso : IsH1Zero Ω hΩ hu
  -- hu : SobolevH1 Ω hΩ
  -- For each k, select phi_k via IsH1Zero at epsilon = 1/(k+1)^2
  -- GNS + clm_norm_sq_eq_sum_sq + cauchy_complete_eLpNorm + limit identification
  -- All ingredients are in Mathlib; the assembly is the sorry here.
  sorry

/-- **Sobolev Embedding (Supercritical case)**: W^{1,p}(Omega) embeds continuously into
    the Hölder space C^{0,alpha}(Omega) when p > n, with alpha = 1 - n/p.
    Functions in W^{1,p} for p > n are not just measurable but actually continuous and
    Hölder continuous with the indicated exponent.

    *Proof sketch (sorry):* The Morrey inequality states that for p > n and
    u ∈ W^{1,p}(R^n) with compact support,
      |u(x) - u(y)| ≤ C * |x - y|^{1 - n/p} * ‖∇u‖_{L^p}
    (Morrey's lemma).  This is the supercritical counterpart of GNS.

    Gap: Mathlib's `SobolevInequality` covers the subcritical case (p < n) but not
    the supercritical/Morrey case (p > n). The same weak-derivative bridge from
    `sobolev_embedding_subcritical` applies here.
    Category C: requires Morrey inequality in Mathlib. -/
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
