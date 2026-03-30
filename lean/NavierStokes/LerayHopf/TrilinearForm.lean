/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Navier-Stokes project -- trilinear form and its antisymmetry.

The trilinear form b(u, v, w) = int sum_{i,j} u_j (d_j v_i) w_i dx
plays a central role in the energy theory of Navier-Stokes.  The key
identity (Lemma 2.1 in the text) is:

  b(u, v, v) = 0   for all divergence-free u in H^1.

This follows from integration by parts:
  b(u, v, v) = (1/2) int u . grad(|v|^2) dx = -(1/2) int (div u)|v|^2 dx = 0.
-/
import NavierStokes.Foundations.DivFreeSpace
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Pow

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

    For divergence-free u and smooth, compactly-supported v,
      b(u, v, v) = 0.

    Proof: for each component k, define φ_k(x) = (v_k(x))². Then φ_k is C^∞_c,
    and fderiv φ_k x (eⱼ) = 2 v_k ∂ⱼv_k by the chain rule for squares.
    Applying the divergence-free condition to each φ_k:
      ∑ⱼ ∫ uⱼ ∂ⱼφ_k = 0, i.e. 2 ∑ⱼ ∫ uⱼ (∂ⱼv_k) v_k = 0.
    Summing over k gives b(u,v,v) = ∑_k 0 = 0.

    The regularity hypotheses (`ContDiff ℝ ∞ v`, `HasCompactSupport v`) ensure that
    φ is a valid C^∞_c test function. The general H^1 case follows by a density
    argument (not formalised here). -/
theorem trilinearForm_antisymmetric
    (u v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hu : IsDistribDivFree (Set.univ : Set (EuclideanSpace ℝ (Fin 3))) isOpen_univ u)
    (hv : ContDiff ℝ ∞ v)
    (hv_supp : HasCompactSupport v) :
    trilinearForm u v v = 0 := by
  -- Abbreviation for the i-th component of v
  set vi : Fin 3 → (EuclideanSpace ℝ (Fin 3) → ℝ) := fun i x => (v x) i with hvi_def
  -- Each component is smooth (v is smooth, projection is a CLM)
  have hvi_smooth : ∀ i, ContDiff ℝ ∞ (vi i) := by
    intro i
    exact ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff).comp hv
  -- Each component has compact support
  have hvi_supp : ∀ i, HasCompactSupport (vi i) := by
    intro i
    apply HasCompactSupport.mono hv_supp
    intro x hx
    simp only [hvi_def, mem_support, ne_eq] at hx ⊢
    exact fun h => hx (by simp [h])
  -- Each component is differentiable
  have hvi_diff : ∀ i, Differentiable ℝ (vi i) := fun i => (hvi_smooth i).differentiable (by simp)
  -- For each component k, define φ_k(x) = (v_k(x))² as a test function
  -- Apply div-free condition to each φ_k separately (avoids ∑/∫ swap)
  have h_inner_zero : ∀ k : Fin 3,
      ∑ j : Fin 3, ∫ x, (u x) j *
        fderiv ℝ (vi k) x (EuclideanSpace.single j 1) * vi k x = 0 := by
    intro k
    -- φ_k(x) = (v_k(x))²
    set φ_k : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => (vi k x) ^ 2 with hφk_def
    -- φ_k is smooth
    have hφk_smooth : ContDiff ℝ ∞ φ_k := (hvi_smooth k).pow 2
    -- φ_k has compact support
    have hφk_supp : HasCompactSupport φ_k := by
      apply HasCompactSupport.mono (hvi_supp k)
      intro x hx
      simp only [hφk_def, mem_support, ne_eq] at hx ⊢
      intro h; apply hx; simp [h]
    -- Div-free condition applied to φ_k
    have h_div := hu φ_k hφk_smooth hφk_supp (Set.subset_univ _)
    simp only [setIntegral_univ] at h_div
    -- Compute fderiv of φ_k = v_k²: fderiv(v_k²) = (2 * v_k) • fderiv(v_k)
    have h_fderiv_k : ∀ (x : EuclideanSpace ℝ (Fin 3)) (j : Fin 3),
        fderiv ℝ φ_k x (EuclideanSpace.single j 1) =
        2 * vi k x * fderiv ℝ (vi k) x (EuclideanSpace.single j 1) := by
      intro x j
      rw [fderiv_fun_pow 2 (hvi_diff k x), ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    -- Substitute into h_div
    simp_rw [h_fderiv_k] at h_div
    -- h_div: ∑ j, ∫ x, (u x) j * (2 * v_k(x) * ∂_j(v_k)(x)) = 0
    -- Rewrite integrand: u_j * (2 * v_k * ∂_j(v_k)) = 2 * (u_j * ∂_j(v_k) * v_k)
    have h_rw : ∀ j : Fin 3, ∀ x : EuclideanSpace ℝ (Fin 3),
        (u x) j * (2 * vi k x * fderiv ℝ (vi k) x (EuclideanSpace.single j 1)) =
        2 * ((u x) j * fderiv ℝ (vi k) x (EuclideanSpace.single j 1) * vi k x) := by
      intros; ring
    simp_rw [h_rw, integral_const_mul, ← Finset.mul_sum] at h_div
    -- h_div: 2 * ∑ j, ∫ x, u_j * ∂_j(v_k) * v_k = 0
    linarith
  -- trilinearForm u v v = ∑ k, (∑ j, ∫ u_j * ∂_j(v_k) * v_k) = ∑ k, 0 = 0
  unfold trilinearForm
  convert Finset.sum_eq_zero (fun k _ => h_inner_zero k) using 1

end NavierStokes
