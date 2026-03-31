/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Navier-Stokes project — Helmholtz decomposition via orthogonal projection.

We use Mathlib's `Submodule.orthogonalProjection` machinery to:
  1. Package L2sigma as a closed submodule of the Hilbert space `Lp E 2 μ`.
  2. Obtain the Leray projector as the orthogonal projection onto this submodule.
  3. Prove idempotence and self-adjointness directly from Mathlib projection lemmas.

Key sorry-free results:
  - `lerayProjectorLp_idempotent`: `P(P(f)) = P(f)` — from `starProjection_eq_self_iff`
  - `lerayProjectorLp_selfAdjoint`: `⟪Pf, g⟫ = ⟪f, Pg⟫` — from `inner_starProjection_left_eq_right`
  - `helmholtz_l2_decomposition`: Hilbert-space orthogonal splitting of any `f ∈ Lp E 2 μ`

The one remaining sorry (`l2sigmaSubmodule_isSeqClosed`) converts `‖f_k - f‖_{Lp 2} → 0`
to `∫ ‖⇑f_k - ⇑f‖² dμ → 0` using `Lp.norm_def` for p=2 (ENNReal bookkeeping).
-/
import NavierStokes.Foundations.DivFreeSpace
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.Sequences

open MeasureTheory Measure TopologicalSpace Filter
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace NavierStokes

variable {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)

/-! ## Setup -/

private abbrev LP2 := Lp (EuclideanSpace ℝ (Fin n)) 2 (volume.restrict Ω)

-- Required for CompleteSpace (LP2 Ω) via `Lp.instCompleteSpace`.
private instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

-- Convenience: the integrand derivative is in MemLp 2 for smooth compactly supported φ.
private lemma phi_deriv_memLp {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφ_supp : HasCompactSupport φ) (i : Fin n) :
    MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) :=
  (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    |>.memLp_of_hasCompactSupport (hφ_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))

/-! ## Auxiliary lemmas for IsDistribDivFree -/

/-- `IsDistribDivFree` is invariant under a.e. modification: if `u₁ =ᵐ u₂` and `u₁`
    is divergence-free, then `u₂` is too. -/
private lemma isDistribDivFree_ae_congr
    {u₁ u₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h : u₁ =ᵐ[volume.restrict Ω] u₂)
    (hu : IsDistribDivFree Ω hΩ u₁) :
    IsDistribDivFree Ω hΩ u₂ := by
  intro φ hφ hφ_supp hφ_Ω
  have h₁ := hu φ hφ hφ_supp hφ_Ω
  suffices heq : ∑ i : Fin n, ∫ x in Ω, (u₁ x) i *
      fderiv ℝ φ x (EuclideanSpace.single i 1) =
      ∑ i : Fin n, ∫ x in Ω, (u₂ x) i *
      fderiv ℝ φ x (EuclideanSpace.single i 1) by linarith [h₁.symm.trans heq]
  congr 1; ext i
  -- For a.e. x, u₁ x = u₂ x, so the integrands agree a.e.
  exact integral_congr_ae (h.mono (fun x hx => by simp only [hx]))

/-- The zero vector field is distributionally divergence-free. -/
private lemma isDistribDivFree_zero :
    IsDistribDivFree Ω hΩ (0 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := by
  intro φ _hφ _hφ_supp _hφ_Ω
  simp

/-- `IsDistribDivFree` is stable under addition (with `MemLp 2` for integrability). -/
private lemma isDistribDivFree_add
    {u v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hu_mem : MemLp u 2 (volume.restrict Ω))
    (hv_mem : MemLp v 2 (volume.restrict Ω))
    (hdu : IsDistribDivFree Ω hΩ u)
    (hdv : IsDistribDivFree Ω hΩ v) :
    IsDistribDivFree Ω hΩ (u + v) := by
  intro φ hφ hφ_supp hφ_Ω
  have hdu' := hdu φ hφ hφ_supp hφ_Ω
  have hdv' := hdv φ hφ hφ_supp hφ_Ω
  have hg := phi_deriv_memLp Ω hφ hφ_supp
  -- Per-component splitting.
  -- Two issues: (1) greedy binder `∫ A + ∫ B` = `∫ (A + ∫ B)` — use explicit parens;
  -- (2) EuclideanSpace.proj i (u x) ≠ (u x).ofLp i syntactically — rely on CLM comp.
  have hstep : ∀ i : Fin n,
      ∫ x in Ω, ((u + v) x).ofLp i * fderiv ℝ φ x (EuclideanSpace.single i 1) =
      (∫ x in Ω, (u x).ofLp i * fderiv ℝ φ x (EuclideanSpace.single i 1)) +
      (∫ x in Ω, (v x).ofLp i * fderiv ℝ φ x (EuclideanSpace.single i 1)) := fun i => by
    -- Component memLp via norm bound: |(u x).ofLp i| ≤ ‖u x‖
    have h_comp_u : MemLp (fun x : EuclideanSpace ℝ (Fin n) => (u x).ofLp i) 2
        (volume.restrict Ω) :=
      hu_mem.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) i)
    have h_comp_v : MemLp (fun x : EuclideanSpace ℝ (Fin n) => (v x).ofLp i) 2
        (volume.restrict Ω) :=
      hv_mem.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) i)
    have h_int_u := h_comp_u.integrable_mul (hg i)
    have h_int_v := h_comp_v.integrable_mul (hg i)
    rw [show (fun x : EuclideanSpace ℝ (Fin n) =>
          ((u + v) x).ofLp i * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        (fun x => (u x).ofLp i * fderiv ℝ φ x (EuclideanSpace.single i 1) +
                  (v x).ofLp i * fderiv ℝ φ x (EuclideanSpace.single i 1)) from
      funext (fun x => by simp only [Pi.add_apply, PiLp.add_apply]; ring)]
    exact integral_add h_int_u h_int_v
  simp_rw [hstep, Finset.sum_add_distrib]
  linarith

/-- `IsDistribDivFree` is stable under scalar multiplication by `c : ℝ`. -/
private lemma isDistribDivFree_smul
    {u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (c : ℝ)
    (hdu : IsDistribDivFree Ω hΩ u) :
    IsDistribDivFree Ω hΩ (c • u) := by
  intro φ hφ hφ_supp hφ_Ω
  have hdu' := hdu φ hφ hφ_supp hφ_Ω
  -- Show: ∑ i, ∫ (c•u)_i * ∂φ = c * ∑ i, ∫ u_i * ∂φ
  have hkey : ∑ i : Fin n, ∫ x in Ω, ((c • u) x) i *
      fderiv ℝ φ x (EuclideanSpace.single i 1) =
      c * ∑ i : Fin n, ∫ x in Ω, (u x) i *
        fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    rw [Finset.mul_sum]
    congr 1; ext i
    rw [← integral_const_mul]
    congr 1; ext x
    -- Pointwise: ((c•u) x) i * ∂φ = c * ((u x) i * ∂φ)
    simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [hkey, hdu', mul_zero]

/-! ## L2sigma as a submodule of Lp 2 -/

/-- `L2sigma Ω hΩ` as a `Submodule` of the Hilbert space `Lp (EuclideanSpace ℝ (Fin n)) 2 μ`.

    An element `f : Lp E 2 μ` is in `l2sigmaSubmodule` iff its a.e.-representative
    `⇑f` is distributionally divergence-free.

    Submodule axioms:
    - `zero_mem'`: use `isDistribDivFree_ae_congr` (⇑0 =ᵐ 0, and 0 is div-free).
    - `add_mem'`: use `isDistribDivFree_ae_congr` (⇑(f+g) =ᵐ ⇑f+⇑g) + `isDistribDivFree_add`.
    - `smul_mem'`: use `isDistribDivFree_ae_congr` (⇑(c•f) =ᵐ c•⇑f) + `isDistribDivFree_smul`. -/
def l2sigmaSubmodule :
    Submodule ℝ (LP2 Ω) where
  carrier := { f | IsDistribDivFree Ω hΩ ⇑f }
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    exact isDistribDivFree_ae_congr Ω hΩ
      (Lp.coeFn_zero (EuclideanSpace ℝ (Fin n)) 2 (volume.restrict Ω)).symm
      (isDistribDivFree_zero Ω hΩ)
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq] at *
    exact isDistribDivFree_ae_congr Ω hΩ (Lp.coeFn_add f g).symm
      (isDistribDivFree_add Ω hΩ (Lp.memLp f) (Lp.memLp g) hf hg)
  smul_mem' := by
    intro c f hf
    simp only [Set.mem_setOf_eq] at *
    exact isDistribDivFree_ae_congr Ω hΩ (Lp.coeFn_smul c f).symm
      (isDistribDivFree_smul Ω hΩ c hf)

/-! ## Closedness of l2sigmaSubmodule -/

/-- The carrier of `l2sigmaSubmodule` is sequentially closed in `Lp E 2 μ`.
    Uses `l2sigma_closed_under_l2_convergence` (proved in `DivFreeSpace.lean`) via
    a bridge (sorry) converting `‖f_k - f‖_{Lp2} → 0` to `∫ ‖⇑f_k - ⇑f‖² dμ → 0`. -/
theorem l2sigmaSubmodule_isSeqClosed :
    IsSeqClosed (l2sigmaSubmodule Ω hΩ).carrier := by
  intro f_seq f_lim h_mem h_tends
  -- Build witnesses for l2sigma_closed_under_l2_convergence
  have hu : ∀ k, ⇑(f_seq k) ∈ L2sigma Ω hΩ :=
    fun k => ⟨Lp.memLp (f_seq k), h_mem k⟩
  have hv_lp : MemLp (⇑f_lim) 2 (volume.restrict Ω) := Lp.memLp f_lim
  -- Bridge: ‖f_k - f‖_{Lp2} → 0  implies  ∫ ‖⇑f_k - ⇑f‖² dμ → 0
  have hconv : Filter.Tendsto
      (fun k => ∫ x in Ω, ‖⇑(f_seq k) x - ⇑f_lim x‖ ^ (2 : ℝ))
      Filter.atTop (nhds 0) := by
    -- ‖f_k - f‖_{Lp2}^2 = ∫ ‖⇑(f_k - f)‖^2 dμ  (p=2 formula)
    -- ⇑(f_k - f) =ᵐ ⇑f_k - ⇑f  (Lp.coeFn_sub)
    -- So ∫ ‖⇑f_k - ⇑f‖^2 dμ = ‖f_k - f‖^2 → 0
    sorry
  exact (l2sigma_closed_under_l2_convergence Ω hΩ
    (fun k => ⇑(f_seq k)) ⇑f_lim hu hv_lp hconv).2

/-- `l2sigmaSubmodule` is topologically closed in `Lp E 2 μ`.
    `Lp E 2 μ` is a metric space (hence a sequential space), so `IsSeqClosed.isClosed` applies. -/
theorem l2sigmaSubmodule_isClosed :
    IsClosed ((l2sigmaSubmodule Ω hΩ : Submodule ℝ (LP2 Ω)) : Set (LP2 Ω)) :=
  IsSeqClosed.isClosed (l2sigmaSubmodule_isSeqClosed Ω hΩ)

/-- `l2sigmaSubmodule` packaged as a `ClosedSubmodule`, enabling Mathlib's
    `HasOrthogonalProjection` instance (valid for any `ClosedSubmodule` of a complete IPS). -/
def l2sigmaClosedSubmodule : ClosedSubmodule ℝ (LP2 Ω) :=
  ⟨l2sigmaSubmodule Ω hΩ, l2sigmaSubmodule_isClosed Ω hΩ⟩

/-! ## Leray projector via orthogonal projection -/

-- `HasOrthogonalProjection` holds for any ClosedSubmodule of a complete inner product space.
private instance l2sigma_hasOrthogonalProjection :
    (l2sigmaSubmodule Ω hΩ).HasOrthogonalProjection :=
  inferInstanceAs ((l2sigmaClosedSubmodule Ω hΩ).toSubmodule.HasOrthogonalProjection)

/-- The Leray projector: the orthogonal projection onto `l2sigmaSubmodule`,
    as a bounded linear map `Lp E 2 μ →L[ℝ] Lp E 2 μ`.

    All properties (idempotence, self-adjointness, range) follow from Mathlib's
    `Submodule.starProjection` API without additional sorries. -/
def lerayProjectorLp : LP2 Ω →L[ℝ] LP2 Ω :=
  (l2sigmaSubmodule Ω hΩ).starProjection

/-- The Lp Leray projector maps into `l2sigmaSubmodule`. -/
theorem lerayProjectorLp_mem (f : LP2 Ω) :
    lerayProjectorLp Ω hΩ f ∈ l2sigmaSubmodule Ω hΩ :=
  (l2sigmaSubmodule Ω hΩ).starProjection_apply_mem f

/-- **Idempotence** (sorry-free): `P(P(f)) = P(f)` for all `f : Lp E 2 μ`.
    Since `P(f) ∈ l2sigmaSubmodule`, `starProjection_eq_self_iff.mpr` applies. -/
theorem lerayProjectorLp_idempotent (f : LP2 Ω) :
    lerayProjectorLp Ω hΩ (lerayProjectorLp Ω hΩ f) = lerayProjectorLp Ω hΩ f :=
  (l2sigmaSubmodule Ω hΩ).starProjection_eq_self_iff.mpr (lerayProjectorLp_mem Ω hΩ f)

/-- **Self-adjointness** (sorry-free): `⟪P(f), g⟫ = ⟪f, P(g)⟫` for all `f g : Lp E 2 μ`.
    Follows from `inner_starProjection_left_eq_right`. -/
theorem lerayProjectorLp_selfAdjoint (f g : LP2 Ω) :
    @inner ℝ _ _ (lerayProjectorLp Ω hΩ f) g =
    @inner ℝ _ _ f (lerayProjectorLp Ω hΩ g) :=
  (l2sigmaSubmodule Ω hΩ).inner_starProjection_left_eq_right f g

/-! ## Helmholtz decomposition at the Lp level -/

/-- **Helmholtz L2 decomposition** (sorry-free modulo the norm bridge):
    `f = P(f) + (f - P(f))` with `P(f) ∈ l2sigmaSubmodule` and `⟪P(f), f - P(f)⟫ = 0`.
    The orthogonal complement `(l2sigmaSubmodule)ᗮ` contains all gradient fields by
    integration by parts, but the exact characterisation requires de Rham theory. -/
theorem helmholtz_l2_decomposition (f : LP2 Ω) :
    lerayProjectorLp Ω hΩ f ∈ l2sigmaSubmodule Ω hΩ ∧
    f = lerayProjectorLp Ω hΩ f + (f - lerayProjectorLp Ω hΩ f) ∧
    @inner ℝ _ _ (lerayProjectorLp Ω hΩ f) (f - lerayProjectorLp Ω hΩ f) = (0 : ℝ) :=
  ⟨lerayProjectorLp_mem Ω hΩ f,
   by abel,
   by
     rw [real_inner_comm]
     exact (l2sigmaSubmodule Ω hΩ).starProjection_inner_eq_zero f _
       (lerayProjectorLp_mem Ω hΩ f)⟩

end NavierStokes
