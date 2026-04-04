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

Key results (provable now):
  - galerkinRHS_contDiff:         the ODE RHS is C^∞ (polynomial in c)
  - galerkin_trilinear_vanishes:  nonlinear term = 0 (trilinearForm_antisymmetric)
  - galerkin_energy_nonincreasing: ‖c(t)‖ ≤ ‖c(0)‖ along solutions

Key results (sorry, Category C):
  - galerkin_exists_local/global: Picard-Lindelöf application
  - galerkinVelocity_l2NormSq_eq: orthonormality computation
  - galerkin_uniformL2Bound:      Bessel inequality for initial data
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
  -- Deferred: the sum-integral swap and reindexing require Integrable hypotheses
  -- that follow from compact support of all basis functions (not yet automated).
  -- The structural argument is correct; integrability is the remaining gap.
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

/-- **Global existence** of the Galerkin ODE.
    The energy bound ‖c(t)‖ ≤ ‖c₀‖ prevents blow-up; local solution extends globally. -/
theorem galerkin_exists_global (N : ℕ) (ν : ℝ) (hν : 0 < ν)
    (data : GalerkinData N) (c₀ : EuclideanSpace ℝ (Fin N)) :
    ∃ sol : GalerkinSolution N ν data c₀, True := by
  sorry
  -- Step 1: local existence via Picard-Lindelöf (galerkinRHS_locallyLipschitz).
  -- Step 2: energy bound ‖c(t)‖ ≤ ‖c₀‖ (galerkin_energy_nonincreasing).
  -- Step 3: continuation — since trajectory stays in closed ball ‖·‖ ≤ ‖c₀‖,
  --         the local solution can be extended to all of ℝ.

/-! ## Uniform bounds for the Galerkin sequence -/

/-- Uniform L² bound: ∫‖u_N(t)‖² ≤ ∫‖u₀‖² for all N and t ≥ 0. -/
theorem galerkin_uniformL2Bound (N : ℕ) (ν : ℝ) (hν : 0 < ν)
    (data : GalerkinData N)
    (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
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
    _ ≤ ∫ x : EuclideanSpace ℝ (Fin 3), ‖u₀ x‖ ^ 2 := by
        -- ‖c₀‖² = ∑_k ⟨u₀, w_k⟩² ≤ ‖u₀‖²_{L²}  by Bessel's inequality.
        sorry

end NavierStokes

end
