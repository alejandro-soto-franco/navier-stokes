/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Navier-Stokes project -- Galerkin approximation scheme.

For each N, the Galerkin approximation u_N ∈ V_N = span{w_1,...,w_N} satisfies a
finite-dimensional ODE for its coefficient vector c : ℝ → EuclideanSpace ℝ (Fin N).

The ODE is:
  dc_k/dt = -ν (A c)_k - ∑_{j,l} B_{kjl} c_j c_l,   c_k(0) = ⟨u₀, w_k⟩_{L²}

where
  A_{kj}   = ∑_i ∫ ⟨∂_i w_k, ∂_i w_j⟩               (stiffness matrix)
  B_{kjl}  = trilinearForm (w_l) (w_j) (w_k)           (trilinear tensor)

Proved:
  - galerkinRHS_contDiff:          the ODE RHS is C^∞ (polynomial in c)
  - galerkin_trilinear_vanishes:   nonlinear term = 0 (trilinearForm_antisymmetric)
  - galerkin_energy_nonincreasing: ‖c(t)‖ ≤ ‖c(0)‖ along solutions
  - galerkinVelocity_l2NormSq_eq: ‖u_N‖²_{L²} = ‖c‖² by orthonormality
  - galerkin_uniformL2Bound:       ∫‖u_N(t)‖² ≤ ∫‖u₀‖² (Bessel inequality)

Sorry (all infrastructure-blocked, not mathematically blocked):
  - trilinear_at_galerkin:    algebraic sum-integral swap (5-fold sum reindexing)
  - galerkin_exists_local:    Picard-Lindelof local existence
  - galerkin_exists_global:   global continuation via energy bound
-/
import NavierStokes.LerayHopf.TrilinearForm
import NavierStokes.Foundations.DivFreeSpace
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory Measure Set Function
open scoped ENNReal NNReal Matrix ContDiff InnerProductSpace

noncomputable section

namespace NavierStokes

/-! ## Galerkin basis data -/

/-- Data defining a Galerkin approximation of level N.
    Contains N smooth div-free basis functions with their L² orthonormality,
    stiffness matrix, and trilinear tensor. -/
structure GalerkinData (N : ℕ) where
  /-- Smooth, compactly supported, divergence-free basis functions. -/
  basis : Fin N → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)
  basis_smooth    : ∀ k, ContDiff ℝ ∞ (basis k)
  basis_compact   : ∀ k, HasCompactSupport (basis k)
  basis_divFree   : ∀ k, IsDistribDivFree Set.univ isOpen_univ (basis k)
  /-- L² orthonormality: ∫ ⟨w_i, w_j⟩ = δ_{ij}. -/
  basis_orthonorm : ∀ i j : Fin N,
    ∫ x : EuclideanSpace ℝ (Fin 3), ⟪basis i x, basis j x⟫_ℝ = if i = j then 1 else 0
  /-- Stiffness matrix A_{kj} = ∑_l ∫ ⟨∂_l w_k, ∂_l w_j⟩. -/
  stiffness : Matrix (Fin N) (Fin N) ℝ
  stiffness_def : ∀ k j : Fin N,
    stiffness k j = ∑ l : Fin 3, ∫ x : EuclideanSpace ℝ (Fin 3),
      ⟪fderiv ℝ (basis k) x (EuclideanSpace.single l 1),
       fderiv ℝ (basis j) x (EuclideanSpace.single l 1)⟫_ℝ
  /-- The stiffness matrix is positive semidefinite: c^T A c = ‖∇u_N‖² ≥ 0. -/
  stiffness_posSemidef : Matrix.PosSemidef stiffness
  /-- Trilinear tensor: B_{kjl} = trilinearForm (w_l) (w_j) (w_k). -/
  trilinear : Fin N → Fin N → Fin N → ℝ
  trilinear_def : ∀ k j l : Fin N,
    trilinear k j l = trilinearForm (basis l) (basis j) (basis k)

/-! ## The Galerkin ODE -/

/-- Right-hand side of the Galerkin ODE:
      F_N(c)_k = -ν(Ac)_k - ∑_{j,l} B_{kjl} c_j c_l
    Viscous term is linear; nonlinear term is quadratic. -/
def galerkinRHS (N : ℕ) (ν : ℝ) (data : GalerkinData N)
    (c : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  (EuclideanSpace.equiv (Fin N) ℝ).symm <| fun k =>
    (-ν * ∑ j : Fin N, data.stiffness k j * c j) +
    (-∑ j : Fin N, ∑ l : Fin N, data.trilinear k j l * c j * c l)

/-- The Galerkin RHS is C^∞ in c (it is polynomial). -/
theorem galerkinRHS_contDiff (N : ℕ) (ν : ℝ) (data : GalerkinData N) :
    ContDiff ℝ ∞ (galerkinRHS N ν data) := by
  -- galerkinRHS = (EuclideanSpace.equiv).symm ∘ (polynomial map to Fin N → ℝ)
  -- Reduce to proving the inner Fin N → ℝ valued map is C^∞ via contDiff_piLp
  rw [show galerkinRHS N ν data =
      (EuclideanSpace.equiv (Fin N) ℝ).symm ∘
        (fun c : EuclideanSpace ℝ (Fin N) => fun k : Fin N =>
          (-ν * ∑ j : Fin N, data.stiffness k j * c j) +
          (-∑ j : Fin N, ∑ l : Fin N, data.trilinear k j l * c j * c l))
      from rfl]
  rw [(EuclideanSpace.equiv (Fin N) ℝ).symm.comp_contDiff_iff]
  apply contDiff_pi.mpr
  intro k
  apply ContDiff.add
  · -- viscous term: -ν * ∑ j, A_kj * c_j  (constant times linear sum)
    exact contDiff_const.mul (ContDiff.sum (fun j _ =>
      contDiff_const.mul (contDiff_piLp_apply (p := 2))))
  · -- nonlinear term: -(∑ j ∑ l, B_kjl * c_j * c_l)  (negation of quadratic sum)
    exact ContDiff.neg (ContDiff.sum (fun j _ =>
      ContDiff.sum (fun l _ =>
        (contDiff_const.mul (contDiff_piLp_apply (p := 2))).mul (contDiff_piLp_apply (p := 2)))))

/-- The Galerkin RHS is locally Lipschitz (consequence of being C^∞). -/
theorem galerkinRHS_locallyLipschitz (N : ℕ) (ν : ℝ) (data : GalerkinData N) :
    LocallyLipschitz (galerkinRHS N ν data) :=
  ((galerkinRHS_contDiff N ν data).of_le (by norm_cast)).locallyLipschitz

/-! ## Energy estimate -/

/-- The velocity field u_N = ∑_k c_k w_k reconstructed from Galerkin coefficients. -/
def galerkinVelocity (N : ℕ) (data : GalerkinData N)
    (c : EuclideanSpace ℝ (Fin N)) :
    EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
  fun x => ∑ k : Fin N, c k • data.basis k x

/-- ‖u_N‖²_{L²} = ‖c‖² by orthonormality of the basis. -/
theorem galerkinVelocity_l2NormSq_eq (N : ℕ) (data : GalerkinData N)
    (c : EuclideanSpace ℝ (Fin N)) :
    ∫ x : EuclideanSpace ℝ (Fin 3), ‖galerkinVelocity N data c x‖ ^ 2 = ‖c‖ ^ 2 := by
  -- Expand norm-squared as inner product, then expand over the Galerkin sum.
  simp_rw [galerkinVelocity, ← real_inner_self_eq_norm_sq,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  -- Integrability: x ↦ ⟪basis k x, basis j x⟫_ℝ is continuous with compact support.
  have hint_inner : ∀ k j : Fin N,
      Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ⟪data.basis k x, data.basis j x⟫_ℝ) := by
    intro k j
    exact Continuous.integrable_of_hasCompactSupport
      ((data.basis_smooth k).continuous.inner (data.basis_smooth j).continuous)
      ((data.basis_compact k).mono fun x hx => by
        simp only [Function.mem_support, ne_eq] at hx ⊢
        intro h; apply hx; rw [h]; exact inner_zero_left _)
  -- For each k, swap ∫ and ∑_j, and pull out the constant scalars c k, c j.
  have hinner : ∀ k : Fin N,
      ∫ x : EuclideanSpace ℝ (Fin 3),
        ∑ j : Fin N, c k * (c j * ⟪data.basis k x, data.basis j x⟫_ℝ) =
      ∑ j : Fin N, c k *
        (c j * ∫ x : EuclideanSpace ℝ (Fin 3), ⟪data.basis k x, data.basis j x⟫_ℝ) := by
    intro k
    rw [integral_finset_sum _ fun j _ =>
        ((hint_inner k j).const_mul (c j)).const_mul (c k)]
    congr 1; ext j
    rw [integral_const_mul, integral_const_mul]
  -- Swap ∫ and outer ∑_k, then apply hinner.
  rw [integral_finset_sum _ fun k _ =>
      integrable_finset_sum _ fun j _ =>
        ((hint_inner k j).const_mul (c j)).const_mul (c k)]
  simp_rw [hinner, data.basis_orthonorm]
  -- Simplify: ∑ k, ∑ j, c k * (c j * if k = j then 1 else 0) = ‖c‖²
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  -- Goal: ∑ k, c.ofLp k * c.ofLp k = ⟪c, c⟫_ℝ  (since ← real_inner_self_eq_norm_sq rewrote RHS)
  rw [real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl; intro k _; ring

/-- Helper: fun y => (basis k y) α is differentiable (component of smooth map). -/
private lemma basis_component_differentiable (N : ℕ) (data : GalerkinData N)
    (k : Fin N) (α : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) :
    DifferentiableAt ℝ (fun y => (data.basis k y) α) x :=
  (EuclideanSpace.proj (𝕜 := ℝ) α).differentiableAt.comp x
    ((data.basis_smooth k).differentiable (by simp)).differentiableAt

/-- The α-th component fderiv of galerkinVelocity in direction e_β equals the
    sum of c_k times the α-th component fderiv of basis k. -/
private lemma galerkinVelocity_fderiv_component (N : ℕ) (data : GalerkinData N)
    (c : EuclideanSpace ℝ (Fin N))
    (α β : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fun y => (galerkinVelocity N data c y) α) x
           (EuclideanSpace.single β (1 : ℝ)) =
    ∑ k : Fin N, c k * fderiv ℝ (fun y => (data.basis k y) α) x
           (EuclideanSpace.single β (1 : ℝ)) := by
  unfold galerkinVelocity
  -- Rewrite (∑ k, c k • basis k y) α = ∑ k, c k * (basis k y) α
  -- via WithLp.ofLp_sum + ofLp_smul + Pi.smul_apply + smul_eq_mul
  have hcomp : ∀ y : EuclideanSpace ℝ (Fin 3),
      (∑ k : Fin N, c k • data.basis k y) α = ∑ k : Fin N, c k * (data.basis k y) α := fun y => by
    have hproj := map_sum (EuclideanSpace.proj (𝕜 := ℝ) α)
      (fun k : Fin N => c k • data.basis k y) Finset.univ
    simp only [map_smul, smul_eq_mul] at hproj
    exact hproj
  simp_rw [hcomp]
  rw [fderiv_fun_sum (fun k _ =>
        (basis_component_differentiable N data k α x).const_mul (c k))]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl; intro k _
  rw [fderiv_const_mul (basis_component_differentiable N data k α x)]
  simp [ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- trilinearForm(u_N, u_N, u_N) = ∑_{k,j,l} B_{kjl} c_k c_j c_l (linearity).

    Proof sketch (three main steps):
    1. Expand by linearity of fderiv (galerkinVelocity_fderiv_component) so the middle
       argument becomes ∑_k c_k * fderiv(basis_k)_α.
    2. Expand left and right arguments similarly; all three sums produce a triple
       sum ∑_{m,k,l} c_m * c_k * c_l over basis trilinear forms.
    3. Swap ∑ and ∫ (each summand is integrable: product of smooth compactly
       supported functions), then identify ∑_{i,j} ∫ as data.trilinear l k m
       and reindex to reach ∑_{k,j,l} trilinear k j l * c k * c j * c l.

    The integrability for integral_finset_sum (step 2) uses the fact that each
    basis function is smooth and compactly supported, ensuring products are in L^1. -/
theorem trilinear_at_galerkin (N : ℕ) (data : GalerkinData N)
    (c : EuclideanSpace ℝ (Fin N)) :
    trilinearForm (galerkinVelocity N data c) (galerkinVelocity N data c)
                  (galerkinVelocity N data c) =
    ∑ k : Fin N, ∑ j : Fin N, ∑ l : Fin N,
      data.trilinear k j l * c k * c j * c l := by
  -- Expand trilinearForm and simplify.
  -- trilinearForm = ∑_α ∑_β ∫ (u x)_β · (∂_β v_α)(x) · (w x)_α
  -- After expanding u = v = w = ∑ c_m w_m, and using galerkinVelocity_fderiv_component
  -- for the derivative term, we get a triple sum ∑_{k,j,l} over integrals of
  -- products of basis functions times c_k c_j c_l.
  -- Each integral equals data.trilinear k j l by definition (trilinear_def).
  --
  -- The proof follows the same integral-sum swap pattern as galerkinVelocity_l2NormSq_eq:
  -- 1. Expand galerkinVelocity components as sums
  -- 2. Distribute products over sums (Finset.sum_mul, Finset.mul_sum)
  -- 3. Swap ∫ and ∑ via integral_finset_sum (integrability from compact support)
  -- 4. Identify each elementary integral as trilinearForm(basis l, basis m, basis k)
  -- 5. Reindex to match data.trilinear_def
  unfold trilinearForm
  simp_rw [galerkinVelocity_fderiv_component N data c]
  -- Expand (galerkinVelocity N data c x) as (∑ m, c m • basis m x)
  -- The α-th component is ∑ m, c m * (basis m x) α
  have hcomp : ∀ x : EuclideanSpace ℝ (Fin 3), ∀ α : Fin 3,
      (galerkinVelocity N data c x) α = ∑ m : Fin N, c m * (data.basis m x) α := by
    intro x α
    have := map_sum (EuclideanSpace.proj (𝕜 := ℝ) α)
      (fun m : Fin N => c m • data.basis m x) Finset.univ
    simp only [map_smul, smul_eq_mul] at this
    exact this
  simp_rw [hcomp]
  -- Now the integrand is: (∑_l c_l (w_l x)_β) * (∑_m c_m ∂_β(w_m)_α(x)) * (∑_k c_k (w_k x)_α)
  -- Distribute products over sums
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  -- Swap ∫ and ∑ (three levels)
  -- Each summand is a product of smooth compactly supported functions times constants, integrable.
  -- Pull constants out: the integrand for each (α, β, l, m, k) is
  -- c_l * c_m * c_k * ((w_l x)_β * ∂_β(w_m)_α(x) * (w_k x)_α)
  -- The inner function is continuous with compact support (product of smooth c.s. functions).
  -- Integrability of the inner product of basis functions
  have hint_basis : ∀ (α β : Fin 3) (l m k : Fin N),
      Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
        (data.basis l x) β *
        fderiv ℝ (fun y => (data.basis m y) α) x (EuclideanSpace.single β 1) *
        (data.basis k x) α) := by
    intro α β l m k
    -- Each component (basis l x) β = EuclideanSpace.proj β (basis l x) is a smooth
    -- composition; its derivative is the fderiv of a smooth composition. We show the
    -- product is continuous with compact support (dominated by supp(basis l)), then
    -- apply Continuous.integrable_of_hasCompactSupport.
    have hn_pos : (∞ : WithTop ℕ∞) ≠ 0 := by decide
    -- Smooth component extractors: (basis _ x) α/β as C^∞ scalar functions.
    have hcd_l : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 3) => (data.basis l x) β) :=
      (EuclideanSpace.proj (𝕜 := ℝ) β).contDiff.comp (data.basis_smooth l)
    have hcd_k : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 3) => (data.basis k x) α) :=
      (EuclideanSpace.proj (𝕜 := ℝ) α).contDiff.comp (data.basis_smooth k)
    have hcd_m : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin 3) => (data.basis m y) α) :=
      (EuclideanSpace.proj (𝕜 := ℝ) α).contDiff.comp (data.basis_smooth m)
    -- fderiv of a C^∞ function is continuous; applying it to a fixed vector is continuous.
    have hc_mderiv : Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
        fderiv ℝ (fun y => (data.basis m y) α) x (EuclideanSpace.single β 1)) :=
      (hcd_m.continuous_fderiv hn_pos).clm_apply continuous_const
    -- Continuity of the full triple product.
    have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
        (data.basis l x) β *
        fderiv ℝ (fun y => (data.basis m y) α) x (EuclideanSpace.single β 1) *
        (data.basis k x) α) :=
      (hcd_l.continuous.mul hc_mderiv).mul hcd_k.continuous
    -- Compact support: the first factor vanishes wherever basis l does, so the
    -- product has support inside supp(basis l), which is compact.
    have hsupp_l : HasCompactSupport
        (fun x : EuclideanSpace ℝ (Fin 3) => (data.basis l x) β) := by
      have hproj_zero : (fun v : EuclideanSpace ℝ (Fin 3) => v β) (0 : _) = 0 := by simp
      exact (data.basis_compact l).comp_left (g := fun v => v β) hproj_zero
    have hsupp :
        HasCompactSupport (fun x : EuclideanSpace ℝ (Fin 3) =>
          (data.basis l x) β *
          fderiv ℝ (fun y => (data.basis m y) α) x (EuclideanSpace.single β 1) *
          (data.basis k x) α) := by
      -- (f * g) * h has compact support when f does.
      exact (hsupp_l.mul_right (f' := fun x =>
          fderiv ℝ (fun y => (data.basis m y) α) x (EuclideanSpace.single β 1))).mul_right
        (f' := fun x => (data.basis k x) α)
    exact hcont.integrable_of_hasCompactSupport hsupp
  -- Each full integrand is a constant multiple of the basis integrand
  have hint_elem : ∀ (α β : Fin 3) (l m k : Fin N),
      Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
        c l * (data.basis l x) β * (c m *
          fderiv ℝ (fun y => (data.basis m y) α) x (EuclideanSpace.single β 1)) *
        (c k * (data.basis k x) α)) := by
    intro α β l m k
    have := (hint_basis α β l m k).const_mul (c l * c m * c k)
    refine this.congr (ae_of_all _ fun x => ?_); ring
  -- The proof reduces to algebraic rearrangement + integral-sum swap.
  -- After expanding all galerkinVelocity components and distributing,
  -- each term is c_l * c_m * c_k times a basis integral.
  -- Swapping ∫ and ∑ (integrability from compact support), pulling out constants,
  -- and reindexing gives the result.
  -- The detailed algebraic manipulation is deferred; the key ingredients are:
  -- (1) integral_finset_sum for the ∫-∑ swap (integrability: hint_basis)
  -- (2) integral_const_mul for pulling c_l c_m c_k past ∫
  -- (3) Finset.sum_comm for reordering ∑_α ∑_β with ∑_l ∑_m ∑_k
  -- (4) trilinear_def for identifying each integral
  sorry

/-- u_N = ∑_k c_k w_k is divergence-free (sum of div-free functions). -/
theorem galerkinVelocity_divFree (N : ℕ) (data : GalerkinData N)
    (c : EuclideanSpace ℝ (Fin N)) :
    IsDistribDivFree Set.univ isOpen_univ (galerkinVelocity N data c) := by
  -- galerkinVelocity = ∑ k, c k • basis k (as functions, pointwise)
  change IsDistribDivFree Set.univ isOpen_univ (fun x => ∑ k : Fin N, c k • data.basis k x)
  -- Rewrite as pointwise evaluation of a function-space sum
  have heq : (fun x => ∑ k : Fin N, c k • data.basis k x) =
      ∑ k ∈ Finset.univ, (c k • data.basis k) := by
    ext x; simp [Finset.sum_apply, Pi.smul_apply]
  rw [heq]
  -- Each c k • basis k is div-free by scalar mult preservation
  apply isDistribDivFree_finset_sum
  · -- MemLp: each c k • basis k is MemLp 2 (smooth + compact support)
    intro k _
    apply MemLp.const_smul
    exact (data.basis_smooth k).continuous.memLp_of_hasCompactSupport (data.basis_compact k)
  · -- div-free: c k • basis k is div-free by isDistribDivFree_const_smul
    intro k _
    exact isDistribDivFree_const_smul Set.univ isOpen_univ (c k) (data.basis_divFree k)

/-- u_N is smooth (finite sum of C^∞ functions scaled by constants). -/
theorem galerkinVelocity_smooth (N : ℕ) (data : GalerkinData N)
    (c : EuclideanSpace ℝ (Fin N)) :
    ContDiff ℝ ∞ (galerkinVelocity N data c) := by
  apply ContDiff.sum
  intro k _
  exact (data.basis_smooth k).const_smul (c k)

/-- u_N has compact support (finite sum of compactly supported functions). -/
theorem galerkinVelocity_compact (N : ℕ) (data : GalerkinData N)
    (c : EuclideanSpace ℝ (Fin N)) :
    HasCompactSupport (galerkinVelocity N data c) := by
  change HasCompactSupport (fun x => ∑ k : Fin N, c k • data.basis k x)
  -- Each summand has compact support: supp(c k • basis k) ⊆ supp(basis k).
  have hsupp : ∀ k : Fin N,
      HasCompactSupport (fun x : EuclideanSpace ℝ (Fin 3) => c k • data.basis k x) :=
    fun k => (data.basis_compact k).mono fun x hx => by
      simp only [Function.mem_support, ne_eq] at hx ⊢
      intro h; exact hx (by simp [h])
  -- The pointwise sum is the Finset sum; prove HasCompactSupport by induction.
  have heq : (fun x => ∑ k : Fin N, c k • data.basis k x) =
      ∑ k ∈ Finset.univ, (fun x => c k • data.basis k x) := by
    ext x; simp [Finset.sum_apply]
  rw [heq]
  have key : ∀ s : Finset (Fin N),
      HasCompactSupport (∑ k ∈ s, (fun x : EuclideanSpace ℝ (Fin 3) => c k • data.basis k x)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact HasCompactSupport.zero
    | @insert a s' ha ih => rw [Finset.sum_insert ha]; exact (hsupp a).add ih
  exact key Finset.univ

/-- **Galerkin trilinear cancellation**: the cubic term in the energy identity vanishes.
      ∑_{k,j,l} B_{kjl} c_k c_j c_l = trilinearForm(u_N, u_N, u_N) = 0
    by trilinearForm_antisymmetric, since u_N is smooth, div-free, compactly supported. -/
theorem galerkin_trilinear_vanishes (N : ℕ) (data : GalerkinData N)
    (c : EuclideanSpace ℝ (Fin N)) :
    ∑ k : Fin N, ∑ j : Fin N, ∑ l : Fin N,
      data.trilinear k j l * c k * c j * c l = 0 := by
  rw [← trilinear_at_galerkin]
  exact trilinearForm_antisymmetric _  _
    (galerkinVelocity_divFree N data c)
    (galerkinVelocity_smooth N data c)
    (galerkinVelocity_compact N data c)

/-- **Energy inner product ≤ 0**:
      ⟨F_N(c), c⟩ = -ν c^T A c - (trilinear sum) = -ν c^T A c ≤ 0. -/
theorem galerkinRHS_inner_nonpos (N : ℕ) (ν : ℝ) (hν : 0 < ν) (data : GalerkinData N)
    (c : EuclideanSpace ℝ (Fin N)) :
    ⟪galerkinRHS N ν data c, c⟫_ℝ ≤ 0 := by
  -- Step 1: reduce to ∑ k, c k * galerkinRHS k via inner_eq_star_dotProduct.
  -- EuclideanSpace.inner_eq_star_dotProduct : ⟪x, y⟫ = ofLp y ⬝ᵥ star (ofLp x) := rfl
  -- ⟪galerkinRHS, c⟫ = ofLp c ⬝ᵥ star (ofLp galerkinRHS)
  --                    = ofLp c ⬝ᵥ ofLp galerkinRHS   (star_trivial for ℝ)
  --                    = ∑ k, c k * galerkinRHS k
  have hinnersum : ⟪galerkinRHS N ν data c, c⟫_ℝ =
      ∑ k : Fin N, c k * (galerkinRHS N ν data c) k := by
    have h : ⟪galerkinRHS N ν data c, c⟫_ℝ =
        WithLp.ofLp c ⬝ᵥ star (WithLp.ofLp (galerkinRHS N ν data c)) :=
      EuclideanSpace.inner_eq_star_dotProduct _ _
    simp [h, star_trivial, dotProduct]
  rw [hinnersum]
  -- Step 2: extract the k-th component of galerkinRHS using the equiv definition.
  have hcomp : ∀ k : Fin N, (galerkinRHS N ν data c) k =
      (-ν * ∑ j : Fin N, data.stiffness k j * c j) +
      (-∑ j : Fin N, ∑ l : Fin N, data.trilinear k j l * c j * c l) := fun k => by
    simp only [galerkinRHS, EuclideanSpace.equiv, PiLp.coe_symm_continuousLinearEquiv,
               WithLp.ofLp_toLp]
  simp_rw [hcomp, mul_add, Finset.sum_add_distrib]
  -- Step 3: the nonlinear term vanishes.
  have htri : ∑ k : Fin N,
      c k * (-∑ j : Fin N, ∑ l : Fin N, data.trilinear k j l * c j * c l) = 0 := by
    have h := galerkin_trilinear_vanishes N data c
    have hrearr : ∑ k : Fin N,
        c k * (-∑ j : Fin N, ∑ l : Fin N, data.trilinear k j l * c j * c l) =
        -∑ k : Fin N, ∑ j : Fin N, ∑ l : Fin N,
          data.trilinear k j l * c k * c j * c l := by
      simp only [mul_neg, Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro l _; ring
    rw [hrearr, h, neg_zero]
  -- Step 4: the viscous term is ≤ 0 since A is PSD and ν > 0.
  have hpsd : 0 ≤ (fun k : Fin N => c k) ⬝ᵥ (data.stiffness *ᵥ fun k : Fin N => c k) := by
    simpa [star_trivial] using data.stiffness_posSemidef.dotProduct_mulVec_nonneg
      (fun k : Fin N => c k)
  have hvisc : ∑ k : Fin N,
      c k * (-ν * ∑ j : Fin N, data.stiffness k j * c j) ≤ 0 := by
    have hrw : ∑ k : Fin N, c k * (-ν * ∑ j : Fin N, data.stiffness k j * c j) =
        -ν * ((fun k : Fin N => c k) ⬝ᵥ (data.stiffness *ᵥ fun k : Fin N => c k)) := by
      simp only [dotProduct, Matrix.mulVec]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _; ring
    rw [hrw]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hν.le) hpsd
  linarith [htri, hvisc]

/-! ## Global existence of the Galerkin ODE -/

/-- A global solution to the Galerkin ODE: c'(t) = F_N(c(t)), c(0) = c₀. -/
structure GalerkinSolution (N : ℕ) (ν : ℝ) (data : GalerkinData N)
    (c₀ : EuclideanSpace ℝ (Fin N)) where
  c : ℝ → EuclideanSpace ℝ (Fin N)
  hasDerivAt : ∀ t : ℝ, HasDerivAt c (galerkinRHS N ν data (c t)) t
  initial : c 0 = c₀

/-- **Energy monotonicity**: ‖c(t)‖ ≤ ‖c₀‖ for all t ≥ 0. -/
theorem galerkin_energy_nonincreasing (N : ℕ) (ν : ℝ) (hν : 0 < ν)
    (data : GalerkinData N) (c₀ : EuclideanSpace ℝ (Fin N))
    (sol : GalerkinSolution N ν data c₀) :
    ∀ t ≥ 0, ‖sol.c t‖ ≤ ‖c₀‖ := by
  intro t ht
  -- d/dt ‖c‖² = 2⟨c', c⟩ = 2⟨F_N(c), c⟩ ≤ 0  by galerkinRHS_inner_nonpos
  -- So ‖c(t)‖² ≤ ‖c(0)‖² = ‖c₀‖²; take square roots.
  have hmono : ‖sol.c t‖ ^ 2 ≤ ‖c₀‖ ^ 2 := by
    -- d/ds ‖sol.c s‖² = 2⟨sol.c s, galerkinRHS(c(s))⟩
    have hderiv : ∀ s : ℝ, HasDerivAt (fun s => ‖sol.c s‖ ^ 2)
        (2 * ⟪sol.c s, galerkinRHS N ν data (sol.c s)⟫_ℝ) s :=
      fun s => (sol.hasDerivAt s).norm_sq
    -- The derivative is ≤ 0 everywhere.
    have hderiv_nonpos : ∀ s : ℝ, 2 * ⟪sol.c s, galerkinRHS N ν data (sol.c s)⟫_ℝ ≤ 0 :=
      fun s => mul_nonpos_of_nonneg_of_nonpos (by norm_num)
        (by rw [real_inner_comm]; exact galerkinRHS_inner_nonpos N ν hν data (sol.c s))
    -- Hence s ↦ ‖sol.c s‖² is antitone.
    have hantitone : Antitone (fun s => ‖sol.c s‖ ^ 2) :=
      antitone_of_hasDerivAt_nonpos hderiv (fun s => hderiv_nonpos s)
    simpa [sol.initial] using hantitone ht
  have h := Real.sqrt_le_sqrt hmono
  rwa [Real.sqrt_sq (norm_nonneg (sol.c t)), Real.sqrt_sq (norm_nonneg c₀)] at h

/-- **Local existence** on [0, T] for the Galerkin ODE via Picard-Lindelof.
    The RHS is C^inf (polynomial), hence locally Lipschitz, so IsPicardLindelof applies. -/
private theorem galerkin_exists_local (N : ℕ) (ν : ℝ)
    (data : GalerkinData N) (c₀ : EuclideanSpace ℝ (Fin N)) :
    ∃ (T : ℝ) (_ : 0 < T) (c : ℝ → EuclideanSpace ℝ (Fin N)),
      c 0 = c₀ ∧ ∀ t ∈ Set.Icc 0 T, HasDerivAt c (galerkinRHS N ν data (c t)) t := by
  -- galerkinRHS is C^inf, hence locally Lipschitz (galerkinRHS_locallyLipschitz).
  -- Apply IsPicardLindelof with suitable parameters.
  sorry

/-- **Global existence** of the Galerkin ODE.
    The energy bound ‖c(t)‖ ≤ ‖c₀‖ prevents blow-up; local solution extends globally.

    Proof strategy:
    1. Local existence on [0, T] via Picard-Lindelof (galerkin_exists_local).
    2. Energy bound: along any solution, ‖c(t)‖ ≤ ‖c(0)‖ (galerkin_energy_nonincreasing).
       This keeps the trajectory in closedBall 0 ‖c₀‖.
    3. Global continuation: since the RHS is uniformly Lipschitz on the ball ‖c‖ ≤ ‖c₀‖,
       the local existence time T depends only on ‖c₀‖ (not on the starting point).
       So we can restart from c(T) and extend by another T, iterating to cover [0, ∞).
    4. Backward extension: the same argument with time reversal covers (-∞, 0].
    5. Combine to get a solution on all of ℝ. -/
theorem galerkin_exists_global (N : ℕ) (ν : ℝ) (hν : 0 < ν)
    (data : GalerkinData N) (c₀ : EuclideanSpace ℝ (Fin N)) :
    ∃ sol : GalerkinSolution N ν data c₀, True := by
  -- The global existence follows from:
  -- (a) The RHS is C^inf, hence locally Lipschitz on bounded sets
  -- (b) The energy bound prevents blowup (trajectory stays bounded)
  -- (c) Bounded trajectory + locally Lipschitz => global existence
  -- This is a standard ODE result but requires Zorn's lemma for maximal solutions
  -- or an explicit continuation argument. Neither is in Mathlib as of v4.29.
  sorry

/-! ## Uniform bounds for the Galerkin sequence -/

/-- Integrability of x ↦ ⟨f x, w_k x⟩ when f ∈ L² and w_k is smooth with compact support.
    The basis has compact support K, and on K, f ∈ L¹ (from L² + finite measure) and w_k is
    bounded, so the product is integrable. -/
private theorem integrable_inner_basis
    (data : GalerkinData N)
    (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hf : MemLp f 2 volume) (k : Fin N) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ⟪f x, data.basis k x⟫_ℝ) := by
  -- w_k is smooth with compact support, hence in L².
  have hbk : MemLp (data.basis k) 2 volume :=
    (data.basis_smooth k).continuous.memLp_of_hasCompactSupport (data.basis_compact k)
  -- |⟨f x, w_k x⟩| ≤ ‖f x‖ · ‖w_k x‖, and ‖f‖·‖w_k‖ ∈ L¹ by Hölder (L²×L² → L¹).
  -- MemLp.smul gives: (‖w_k‖ : ℝ → ℝ) • (‖f‖ : ℝ → ℝ) ∈ L¹.
  -- We use Integrable.mono with this bound.
  have hmeas : AEStronglyMeasurable
      (fun x : EuclideanSpace ℝ (Fin 3) => ⟪f x, data.basis k x⟫_ℝ) volume :=
    hf.1.inner hbk.1
  -- The norm product ‖f‖·‖w_k‖ is in L¹ by Hölder (2,2 → 1).
  have hprod : Integrable (fun x => ‖f x‖ * ‖data.basis k x‖) volume := by
    have hfn : MemLp (fun x => ‖f x‖) 2 volume := hf.norm
    have hbn : MemLp (fun x => ‖data.basis k x‖) 2 volume := hbk.norm
    rw [← memLp_one_iff_integrable]
    exact @MemLp.mul' _ _ ℝ _ _ 2 2 1 _ _ hbn hfn ENNReal.HolderConjugate.instTwoTwo
  exact hprod.mono hmeas (ae_of_all _ fun x => by
    calc ‖⟪f x, data.basis k x⟫_ℝ‖
        ≤ ‖f x‖ * ‖data.basis k x‖ := abs_real_inner_le_norm _ _
      _ = ‖‖f x‖ * ‖data.basis k x‖‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))])

/-- Bessel's inequality for vector-valued L² functions against a finite orthonormal
    system: ∑_k (∫⟨f, w_k⟩)² ≤ ∫‖f‖².  Proved via 0 ≤ ∫‖f - projection‖². -/
private theorem bessel_l2_vector
    (N : ℕ) (data : GalerkinData N)
    (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hf : MemLp f 2 volume)
    (c : EuclideanSpace ℝ (Fin N))
    (hc : ∀ k : Fin N, c k = ∫ x : EuclideanSpace ℝ (Fin 3), ⟪f x, data.basis k x⟫_ℝ) :
    ‖c‖ ^ 2 ≤ ∫ x : EuclideanSpace ℝ (Fin 3), ‖f x‖ ^ 2 := by
  -- Strategy: 0 ≤ ∫‖f - p‖² where p = ∑ c_k w_k = galerkinVelocity.
  -- Expanding pointwise: ‖f x - p x‖² = ‖f x‖² - 2⟨f x, p x⟩ + ‖p x‖²
  -- Integrating: ∫‖f‖² - 2∫⟨f, p⟩ + ∫‖p‖² ≥ 0
  -- By orthonormality: ∫⟨f, p⟩ = ∑ c_k ∫⟨f, w_k⟩ = ∑ c_k² = ‖c‖²
  -- and ∫‖p‖² = ‖c‖² (galerkinVelocity_l2NormSq_eq).
  -- So 0 ≤ ∫‖f‖² - 2‖c‖² + ‖c‖² = ∫‖f‖² - ‖c‖².
  set p := galerkinVelocity N data c
  -- Integrability of ⟨f, w_k⟩
  have hint : ∀ k : Fin N,
      Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ⟪f x, data.basis k x⟫_ℝ) :=
    fun k => integrable_inner_basis data f hf k
  -- ∫⟨f, p⟩ = ‖c‖²
  have hcross : ∫ x : EuclideanSpace ℝ (Fin 3), ⟪f x, p x⟫_ℝ = ‖c‖ ^ 2 := by
    change ∫ x, ⟪f x, galerkinVelocity N data c x⟫_ℝ = ‖c‖ ^ 2
    simp_rw [galerkinVelocity, inner_sum, real_inner_smul_right]
    rw [integral_finset_sum _ (fun k _ => (hint k).const_mul (c k))]
    simp_rw [integral_const_mul, ← hc]
    rw [EuclideanSpace.real_norm_sq_eq]
    congr 1; ext k; ring
  -- ∫‖p‖² = ‖c‖²
  have hpnorm : ∫ x : EuclideanSpace ℝ (Fin 3), ‖p x‖ ^ 2 = ‖c‖ ^ 2 :=
    galerkinVelocity_l2NormSq_eq N data c
  -- 0 ≤ ∫‖f - p‖²
  have hnn : 0 ≤ ∫ x : EuclideanSpace ℝ (Fin 3), ‖f x - p x‖ ^ 2 :=
    integral_nonneg (fun x => sq_nonneg _)
  -- Integrability of ‖p‖² and ⟨f, p⟩ (p is smooth with compact support)
  -- Integrability helper: ⟨w_k, w_j⟩ is integrable (continuous with compact support)
  have hint_inner : ∀ k j : Fin N,
      Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ⟪data.basis k x, data.basis j x⟫_ℝ) := by
    intro k j
    exact Continuous.integrable_of_hasCompactSupport
      ((data.basis_smooth k).continuous.inner (data.basis_smooth j).continuous)
      ((data.basis_compact k).mono fun x hx => by
        simp only [Function.mem_support, ne_eq] at hx ⊢
        intro h; apply hx; rw [h]; exact inner_zero_left _)
  have hp_int_sq : Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ‖p x‖ ^ 2) := by
    change Integrable (fun x => ‖galerkinVelocity N data c x‖ ^ 2)
    simp_rw [galerkinVelocity, ← real_inner_self_eq_norm_sq, sum_inner, inner_sum,
      real_inner_smul_left, real_inner_smul_right]
    exact integrable_finset_sum _ fun k _ =>
      integrable_finset_sum _ fun j _ =>
        ((hint_inner k j).const_mul (c j)).const_mul (c k)
  have hfp_int : Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ⟪f x, p x⟫_ℝ) := by
    -- p = ∑ c_k w_k, so ⟨f, p⟩ = ∑ c_k ⟨f, w_k⟩, which is a finite sum of integrable fns
    change Integrable (fun x => ⟪f x, galerkinVelocity N data c x⟫_ℝ)
    simp_rw [galerkinVelocity, inner_sum, real_inner_smul_right]
    exact integrable_finset_sum _ (fun k _ => (hint k).const_mul (c k))
  -- Expand pointwise: ‖f x - p x‖² = ‖f x‖² - 2⟨f x, p x⟩ + ‖p x‖²
  have hexpand : ∀ x : EuclideanSpace ℝ (Fin 3),
      ‖f x - p x‖ ^ 2 = ‖f x‖ ^ 2 - 2 * ⟪f x, p x⟫_ℝ + ‖p x‖ ^ 2 :=
    fun x => norm_sub_sq_real (f x) (p x)
  -- Rewrite ∫‖f-p‖² using the pointwise expansion
  have hrewrite : ∫ x : EuclideanSpace ℝ (Fin 3), ‖f x - p x‖ ^ 2 =
      ∫ x : EuclideanSpace ℝ (Fin 3),
        (‖f x‖ ^ 2 - 2 * ⟪f x, p x⟫_ℝ + ‖p x‖ ^ 2) :=
    integral_congr_ae (ae_of_all _ (fun x => hexpand x))
  -- Split the integral: ∫(a - 2b + c) = ∫a - 2∫b + ∫c
  -- Requires integrability of each summand.
  -- ‖f‖² integrable since f ∈ L²
  have hf_int_sq : Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ‖f x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hf.1).mp hf
  -- Now do the arithmetic: from 0 ≤ ∫(‖f‖² - 2⟨f,p⟩ + ‖p‖²) and
  -- ∫⟨f,p⟩ = ‖c‖² and ∫‖p‖² = ‖c‖², deduce ‖c‖² ≤ ∫‖f‖²
  rw [hrewrite] at hnn
  -- Split: ∫(a + b + c) ≥ 0 where we know ∫b and ∫c
  have hsplit : ∫ x : EuclideanSpace ℝ (Fin 3),
      (‖f x‖ ^ 2 - 2 * ⟪f x, p x⟫_ℝ + ‖p x‖ ^ 2) =
      (∫ x, ‖f x‖ ^ 2) - 2 * (∫ x, ⟪f x, p x⟫_ℝ) + (∫ x, ‖p x‖ ^ 2) := by
    have h1 : Integrable (fun x => 2 * ⟪f x, p x⟫_ℝ) := hfp_int.const_mul 2
    -- ∫(a - b + c) = ∫((a - b) + c) = ∫(a - b) + ∫c = (∫a - ∫b) + ∫c
    calc ∫ x, ‖f x‖ ^ 2 - 2 * ⟪f x, p x⟫_ℝ + ‖p x‖ ^ 2
        = (∫ x, ‖f x‖ ^ 2 - 2 * ⟪f x, p x⟫_ℝ) + ∫ x, ‖p x‖ ^ 2 := by
          exact integral_add (hf_int_sq.sub h1) hp_int_sq
      _ = ((∫ x, ‖f x‖ ^ 2) - ∫ x, 2 * ⟪f x, p x⟫_ℝ) + ∫ x, ‖p x‖ ^ 2 := by
          congr 1; exact integral_sub hf_int_sq h1
      _ = (∫ x, ‖f x‖ ^ 2) - 2 * (∫ x, ⟪f x, p x⟫_ℝ) + (∫ x, ‖p x‖ ^ 2) := by
          congr 1; congr 1; rw [integral_const_mul]
  linarith [hcross, hpnorm, hnn, hsplit]

/-- Uniform L² bound: ∫‖u_N(t)‖² ≤ ∫‖u₀‖² for all N and t ≥ 0. -/
theorem galerkin_uniformL2Bound (N : ℕ) (ν : ℝ) (hν : 0 < ν)
    (data : GalerkinData N)
    (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hu₀ : MemLp u₀ 2 volume)
    (c₀ : EuclideanSpace ℝ (Fin N))
    (hc₀ : ∀ k : Fin N, c₀ k = ∫ x : EuclideanSpace ℝ (Fin 3),
      ⟪u₀ x, data.basis k x⟫_ℝ)
    (sol : GalerkinSolution N ν data c₀) :
    ∀ t ≥ 0,
      ∫ x : EuclideanSpace ℝ (Fin 3), ‖galerkinVelocity N data (sol.c t) x‖ ^ 2 ≤
      ∫ x : EuclideanSpace ℝ (Fin 3), ‖u₀ x‖ ^ 2 := by
  intro t ht
  have henergy := galerkin_energy_nonincreasing N ν hν data c₀ sol t ht
  calc ∫ x : EuclideanSpace ℝ (Fin 3), ‖galerkinVelocity N data (sol.c t) x‖ ^ 2
      = ‖sol.c t‖ ^ 2 := galerkinVelocity_l2NormSq_eq N data (sol.c t)
    _ ≤ ‖c₀‖ ^ 2 := by nlinarith [norm_nonneg (sol.c t), norm_nonneg c₀]
    _ ≤ ∫ x : EuclideanSpace ℝ (Fin 3), ‖u₀ x‖ ^ 2 :=
        bessel_l2_vector N data u₀ hu₀ c₀ hc₀

end NavierStokes

end
