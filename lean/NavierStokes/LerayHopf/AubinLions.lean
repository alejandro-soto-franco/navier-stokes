/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Navier-Stokes project -- Aubin-Lions compactness lemma.

The Aubin-Lions lemma (J.-P. Aubin 1963, J.-L. Lions 1969) is the principal
compactness tool for parabolic PDE existence proofs.  It states:

  If a sequence (u_N) is bounded in L^q_t(0,T; B₁) ∩ W^{1,r}_t(0,T; B₃)
  and B₁ ↪↪ B₂ ↪ B₃ (compact embedding of B₁ into B₂), then (u_N)
  is precompact in L^q_t(0,T; B₂).

For the Leray-Hopf theorem the relevant instance is:
  B₁ = H¹_σ(Ω),  B₂ = L²_σ(Ω),  B₃ = H⁻¹_σ(Ω)
  q = 2,  r = ∞ (or r = 4/3 in 3D)

The compact embedding H¹ ↪↪ L² is Rellich-Kondrachov (RellichKondrachov.lean).
The bound on ∂_t u_N in a negative Sobolev space follows from the NS equation
applied to the Galerkin approximation (energy estimate + trilinear estimates).

All proofs are sorry.

Category C: requires
  (1) A formalization of the abstract Aubin-Lions theorem, including the
      notion of compact embedding in the Banach space sense.
  (2) The Rellich-Kondrachov compact embedding H¹ ↪↪ L² (RellichKondrachov.lean).
  (3) Estimates on ∂_t u_N in H⁻¹ from the Galerkin equation.
-/
import NavierStokes.LerayHopf.GalerkinApproximation
import NavierStokes.Foundations.RellichKondrachov
import Mathlib.MeasureTheory.Function.LpSpace.Complete

open MeasureTheory Measure TopologicalSpace Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace NavierStokes

/-! ## Abstract Aubin-Lions compactness -/

/-- **Aubin-Lions Lemma** (abstract form).

    Let B₁ ↪↪ B₂ ↪ B₃ be Banach spaces with B₁ compactly embedded in B₂.
    Suppose (fₙ) is a sequence satisfying:
      (i)  sup_n ‖fₙ‖_{L²(0,T; B₁)} < ∞     (uniform H¹ bound)
      (ii) sup_n ‖∂_t fₙ‖_{L^r(0,T; B₃)} < ∞  (uniform time-derivative bound)
    Then (fₙ) has a subsequence convergent in L²(0,T; B₂).

    For the Leray-Hopf application: B₁ = H¹_σ, B₂ = L²_σ, B₃ = H⁻¹_σ.

    Category C: requires abstract Banach-space valued L^p space theory and
    a formal definition of compact embedding not yet in Mathlib. -/
theorem aubinLions_compactness
    -- Time horizon
    (T : ℝ) (hT : 0 < T)
    -- A sequence of functions fₙ : [0,T] → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)
    (f : ℕ → ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    -- Uniform L^∞_t L²_x bound: all functions bounded by C in energy
    (C : ℝ) (hC : 0 < C)
    (hL2 : ∀ n : ℕ, ∀ t ∈ Set.Icc 0 T,
      ∫ x, ‖f n t x‖ ^ 2 ≤ C)
    -- Uniform L²_t H¹_x bound: all functions bounded in enstrophy
    (hH1 : ∀ n : ℕ, ∫ t in Set.Icc 0 T, ∑ i : Fin 3,
      ∫ x, ‖fderiv ℝ (f n t) x (EuclideanSpace.single i 1)‖ ^ 2 ≤ C)
    -- Time-derivative bound in H⁻¹: encoded abstractly
    (hDt : ∀ n : ℕ, True) :  -- Placeholder: ‖∂_t fₙ‖_{L^{4/3}(H⁻¹)} ≤ C
    -- Conclusion: subsequence converging in L²([0,T]; L²_x)
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ g : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
        Tendsto (fun n => ∫ t in Set.Icc 0 T, ∫ x, ‖f (φ n) t x - g t x‖ ^ 2)
                atTop (nhds 0) := by
  sorry

/-- **Galerkin sequence compactness**: the Galerkin approximations u_N(t,x)
    have a subsequence converging in L²([0,T] × ℝ³) to a limit g.

    This is the primary application of aubinLions_compactness in the
    Leray-Hopf proof.  The uniform bounds come from galerkin_uniformL2Bound
    and the enstrophy bound from the Galerkin energy identity. -/
theorem galerkin_sequence_has_convergent_subseq
    (T : ℝ) (hT : 0 < T)
    (ν : ℝ) (hν : 0 < ν)
    -- Sequence of Galerkin levels and their solutions
    (N : ℕ → ℕ) (hN : StrictMono N)
    (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hu₀ : MemLp u₀ 2 volume)
    -- For each n, data_n is the Galerkin data at level N n
    (data : ∀ n, GalerkinData (N n))
    (c₀ : ∀ n, EuclideanSpace ℝ (Fin (N n)))
    (sol : ∀ n, GalerkinSolution (N n) ν (data n) (c₀ n)) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ g : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
        Tendsto
          (fun n => ∫ t in Set.Icc 0 T, ∫ x,
            ‖galerkinVelocity (N (φ n)) (data (φ n)) (sol (φ n) |>.c t) x - g t x‖ ^ 2)
          atTop (nhds 0) := by
  -- Apply aubinLions_compactness to the sequence f n t x := galerkinVelocity (sol n .c t) x.
  -- The uniform L² bound is galerkin_uniformL2Bound.
  -- The enstrophy bound follows from the Galerkin energy identity.
  -- The time-derivative bound follows from the Galerkin ODE + trilinear estimates.
  sorry

end NavierStokes

end
