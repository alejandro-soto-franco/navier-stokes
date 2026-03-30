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
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Data.Real.ConjExponents

open MeasureTheory Measure TopologicalSpace
open scoped ENNReal ContDiff

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
    ContDiff ℝ ∞ φ →
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

/-- `L2sigma Ω hΩ` is closed under L^2 convergence: if a sequence `(u_k)` in L^2_sigma
    converges to `u` in L^2 (i.e., `∫ ‖u_k - u‖^2 → 0`), then `u ∈ L^2_sigma`.

    The pointwise `IsClosed` predicate on function types uses the product topology
    (pointwise convergence), which is the wrong topology for L^2 spaces.
    Instead, we state closedness as: every L^2-convergent sequence of divergence-free
    fields has a divergence-free limit.

    *Proof sketch (sorry):* The divergence-free condition
      `∑ᵢ ∫ uᵢ * ∂ᵢφ dx = 0` for all test φ
    is linear in u. For fixed smooth φ, Holder's inequality gives
      |∑ᵢ ∫ (u_k - u)ᵢ ∂ᵢφ dx| ≤ C_φ ‖u_k - u‖_{L^2} → 0,
    so the condition passes to the L^2 limit. -/
theorem l2sigma_closed_under_l2_convergence
    {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω)
    (u : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hu : ∀ k, u k ∈ L2sigma Ω hΩ)
    (hv_lp : MemLp v 2 (volume.restrict Ω))
    (_hconv : Filter.Tendsto
      (fun k => ∫ x in Ω, ‖u k x - v x‖ ^ (2 : ℝ))
      Filter.atTop (nhds 0)) :
    v ∈ L2sigma Ω hΩ := by
  refine ⟨hv_lp, ?_⟩
  -- Goal: IsDistribDivFree Ω hΩ v
  intro φ hφ hφ_supp hφ_Ω
  -- Each u_k satisfies the divergence-free condition:
  have huk_div : ∀ k, ∑ i : Fin n,
      ∫ x in Ω, (u k x) i * (fderiv ℝ φ x (EuclideanSpace.single i 1)) = 0 :=
    fun k => (hu k).2 φ hφ hφ_supp hφ_Ω
  -- The constant-zero sequence converges to both 0 and to the target value.
  -- By uniqueness of limits in ℝ (T2Space), the target is 0.
  have h_seq_eq : (fun k => ∑ i : Fin n,
      ∫ x in Ω, (u k x) i * (fderiv ℝ φ x (EuclideanSpace.single i 1))) =
      fun _ => (0 : ℝ) := funext huk_div
  -- Key step: the integrals converge by Holder's inequality.
  -- For each i, |∫ (u_k - v)_i * ∂_i φ| ≤ ‖(u_k - v)_i‖_{L²} * ‖∂_i φ‖_{L²} → 0.
  have h_tendsto : Filter.Tendsto (fun k => ∑ i : Fin n,
      ∫ x in Ω, (u k x) i * (fderiv ℝ φ x (EuclideanSpace.single i 1)))
      Filter.atTop (nhds (∑ i : Fin n,
        ∫ x in Ω, (v x) i * (fderiv ℝ φ x (EuclideanSpace.single i 1)))) := by
    -- Reduce to per-component convergence
    apply tendsto_finset_sum
    intro i _hi
    -- For fixed i, abbreviate g_i(x) := fderiv ℝ φ x (e_i)
    -- g_i is continuous with compact support (from φ ∈ C^∞_c)
    have hg_supp : HasCompactSupport (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
      hφ_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
    have hg_cont : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    -- g_i ∈ L^2 (continuous + compact support → MemLp for all p)
    have hg_memLp : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))
        2 (volume.restrict Ω) :=
      hg_cont.memLp_of_hasCompactSupport hg_supp
    -- Step 1: Reduce to showing the difference integral → 0
    suffices h_diff_zero : Filter.Tendsto (fun k =>
        ∫ x in Ω, ((u k x) i - (v x) i) *
          (fderiv ℝ φ x (EuclideanSpace.single i 1)))
        Filter.atTop (nhds 0) by
      -- Algebra: original = target + diff, so diff → 0 implies original → target
      have h_eq : ∀ k,
          ∫ x in Ω, (u k x) i * (fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          (∫ x in Ω, (v x) i * (fderiv ℝ φ x (EuclideanSpace.single i 1))) +
          ∫ x in Ω, ((u k x) i - (v x) i) *
            (fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
        intro k
        -- Integrability: L² component × L² test function is L¹ (Holder with p=q=2)
        have hvi : MemLp (fun x => (v x) i) 2 (volume.restrict Ω) :=
          hv_lp.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) i)
        have huki : MemLp (fun x => (u k x) i) 2 (volume.restrict Ω) :=
          (hu k).1.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) i)
        have hdiff_i : MemLp (fun x => (u k x) i - (v x) i) 2 (volume.restrict Ω) :=
          huki.sub hvi
        have h_int_v := hvi.integrable_mul hg_memLp
        have h_int_diff := hdiff_i.integrable_mul hg_memLp
        -- Split: ∫ (u_k)_i * g_i = ∫ v_i * g_i + ∫ (u_k - v)_i * g_i
        calc ∫ x in Ω, (u k x) i * (fderiv ℝ φ x (EuclideanSpace.single i 1))
            = ∫ x in Ω, ((v x) i * (fderiv ℝ φ x (EuclideanSpace.single i 1)) +
                ((u k x) i - (v x) i) *
                  (fderiv ℝ φ x (EuclideanSpace.single i 1))) := by
              congr 1; funext x; ring
          _ = (∫ x in Ω, (v x) i * (fderiv ℝ φ x (EuclideanSpace.single i 1))) +
              ∫ x in Ω, ((u k x) i - (v x) i) *
                (fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
              integral_add h_int_v h_int_diff
      simp_rw [h_eq]
      have := h_diff_zero.const_add
        (∫ x in Ω, (v x) i * (fderiv ℝ φ x (EuclideanSpace.single i 1)))
      rwa [add_zero] at this
    -- Step 2: Show ∫_Ω ((u_k - v)_i * g_i) → 0 via Cauchy-Schwarz bound
    -- Bound: |∫ (u_k - v)_i * g_i| ≤ C_i * (∫ ‖u_k - v‖²)^{1/2} → 0
    -- where C_i = (∫_Ω ‖g_i‖²)^{1/2} is a constant (g_i ∈ L² by hg_memLp).
    set C_i := (∫ x in Ω, ‖fderiv ℝ φ x (EuclideanSpace.single i 1)‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
    apply squeeze_zero_norm (a := fun k => C_i *
        (∫ x in Ω, ‖u k x - v x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2))
    · -- Cauchy-Schwarz bound: ‖∫ (u_k - v)_i * g_i‖ ≤ C_i * (∫ ‖u_k - v‖²)^{1/2}
      intro k
      have hdiff_memLp := (hu k).1.sub hv_lp
      -- MemLp of component at ENNReal.ofReal 2 (needed for Hölder)
      have hf_memLp : MemLp (fun x => (u k x) i - (v x) i)
          (ENNReal.ofReal 2) (volume.restrict Ω) := by
        rw [show ENNReal.ofReal 2 = 2 from by simp]
        exact hdiff_memLp.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) i)
      have hg_memLp' : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))
          (ENNReal.ofReal 2) (volume.restrict Ω) := by
        rw [show ENNReal.ofReal 2 = 2 from by simp]; exact hg_memLp
      -- Component norm ≤ total norm (PiLp.norm_apply_le)
      have h_comp : ∀ x, ‖(u k x) i - (v x) i‖ ≤ ‖u k x - v x‖ := fun x => by
        rw [show (u k x) i - (v x) i = (u k x - v x) i from (Pi.sub_apply _ _ _).symm]
        exact PiLp.norm_apply_le _ _
      -- Integrability of ‖u_k - v‖^2 (from MemLp 2 via norm_rpow)
      have h_int : Integrable (fun x => ‖u k x - v x‖ ^ (2 : ℝ)) (volume.restrict Ω) :=
        hdiff_memLp.integrable_norm_rpow (by simp) (by simp)
      -- ∫ ‖f_i‖² ≤ ∫ ‖u_k - v‖² (from pointwise component bound)
      have h_int_le : (∫ x in Ω, ‖(u k x) i - (v x) i‖ ^ (2 : ℝ)) ≤
          (∫ x in Ω, ‖u k x - v x‖ ^ (2 : ℝ)) :=
        integral_mono_of_nonneg (ae_of_all _ (fun x => by positivity)) h_int
          (ae_of_all _ (fun x =>
            Real.rpow_le_rpow (norm_nonneg _) (h_comp x) (by norm_num : (0 : ℝ) ≤ 2)))
      calc ‖∫ x in Ω, ((u k x) i - (v x) i) *
              (fderiv ℝ φ x (EuclideanSpace.single i 1))‖
          ≤ ∫ x in Ω, ‖((u k x) i - (v x) i) *
              (fderiv ℝ φ x (EuclideanSpace.single i 1))‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ x in Ω, ‖(u k x) i - (v x) i‖ *
              ‖fderiv ℝ φ x (EuclideanSpace.single i 1)‖ := by
            congr 1; ext x; exact norm_mul _ _
        _ ≤ (∫ x in Ω, ‖(u k x) i - (v x) i‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
            (∫ x in Ω, ‖fderiv ℝ φ x (EuclideanSpace.single i 1)‖ ^ (2 : ℝ)) ^
              ((1 : ℝ) / 2) :=
            integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hf_memLp hg_memLp'
        _ ≤ (∫ x in Ω, ‖u k x - v x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) * C_i := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact Real.rpow_le_rpow (by positivity) h_int_le (by norm_num)
        _ = C_i * (∫ x in Ω, ‖u k x - v x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
            mul_comm _ _
    · -- Convergence: C_i * (∫ ‖u_k - v‖²)^{1/2} → 0
      -- From _hconv (∫ ‖u_k - v‖² → 0) composed with x^{1/2} and × C_i.
      have h_rpow : Filter.Tendsto
          (fun k => (∫ x in Ω, ‖u k x - v x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2))
          Filter.atTop (nhds ((0 : ℝ) ^ ((1 : ℝ) / 2))) :=
        _hconv.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 2))
      rw [Real.zero_rpow (by norm_num : (1 : ℝ) / 2 ≠ 0)] at h_rpow
      have := h_rpow.const_mul C_i
      rw [mul_zero] at this
      exact this
  rw [h_seq_eq] at h_tendsto
  exact tendsto_nhds_unique h_tendsto tendsto_const_nhds

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
