/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Navier-Stokes project — Sobolev spaces W^{1,p} and H^1.

W^{1,p}(Omega) is the space of L^p functions whose weak first partial
derivatives all exist and are in L^p.  H^1(Omega) = W^{1,2}(Omega) inherits
a Hilbert space structure.  H^1_0(Omega) is the closure of C^inf_c(Omega) in H^1.
-/
import NavierStokes.Foundations.WeakDerivative
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

open MeasureTheory Measure TopologicalSpace
open scoped ENNReal NNReal

noncomputable section

namespace NavierStokes

variable {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)

/-- A function `f` belongs to W^{1,p}(Omega) if f in L^p(Omega) and for each
    coordinate direction i, there exists a weak partial derivative partial_i f in L^p(Omega).
    The weak derivative is taken in the distributional sense: for every smooth compactly
    supported test function phi in C^inf_c(Omega), integration by parts holds. -/
structure SobolevW1p (p : ℝ≥0∞) where
  /-- The function itself. -/
  f : EuclideanSpace ℝ (Fin n) → ℝ
  /-- The weak partial derivatives, one per coordinate direction. -/
  weakDeriv : Fin n → EuclideanSpace ℝ (Fin n) → ℝ
  /-- f is in L^p(Omega). -/
  f_mem_lp : MemLp f p (volume.restrict Ω)
  /-- Each weak partial derivative is in L^p(Omega). -/
  weakDeriv_mem_lp : ∀ i : Fin n, MemLp (weakDeriv i) p (volume.restrict Ω)
  /-- f is locally integrable on Omega (derived from L^p membership, but stated explicitly
      to discharge the hypothesis of IsWeakPartialDeriv). -/
  f_loc_int : LocallyIntegrableOn f Ω
  /-- Each weak partial derivative is locally integrable on Omega. -/
  weakDeriv_loc_int : ∀ i : Fin n, LocallyIntegrableOn (weakDeriv i) Ω
  /-- The integration-by-parts identity holds for each coordinate direction. -/
  isWeakDeriv : ∀ i : Fin n,
    IsWeakPartialDeriv Ω hΩ f (weakDeriv i) i
      (f_loc_int) (weakDeriv_loc_int i)

/-- H^1(Omega) = W^{1,2}(Omega): the Sobolev space of L^2 functions with
    L^2 weak first partial derivatives. This space carries a Hilbert space
    structure under the H^1 inner product. -/
abbrev SobolevH1 := SobolevW1p Ω hΩ 2

/-- The H^1(Omega) inner product:
      <u, v>_{H^1} = integral_Omega u*v dx + sum_i integral_Omega (partial_i u)*(partial_i v) dx.
    This combines the L^2 inner product of the functions with the L^2 inner products
    of all first-order weak partial derivatives. -/
def sobolevH1InnerProduct (u v : SobolevH1 Ω hΩ) : ℝ :=
  -- L^2 part: integral_Omega u * v
  (∫ x in Ω, u.f x * v.f x) +
  -- H^1 seminorm part: sum over coordinate directions of integral_Omega partial_i u * partial_i v
  Finset.sum Finset.univ (fun i : Fin n =>
    ∫ x in Ω, u.weakDeriv i x * v.weakDeriv i x)

/-- H^1_0(Omega) is the closure of C^inf_c(Omega) in the H^1 norm.
    Equivalently, by the Meyers-Serrin theorem and trace theory, it is the subspace of
    H^1(Omega) whose elements have zero trace on the boundary partial Omega.
    Here we define it abstractly as a sorry-stub pending the construction of the
    H^1 norm topology and the completion/closure machinery. -/
def SobolevH1Zero : Type :=
  sorry

/-- The H^1(Omega) norm squared: ||u||^2_{H^1} = <u, u>_{H^1}. -/
def sobolevH1NormSq (u : SobolevH1 Ω hΩ) : ℝ :=
  sobolevH1InnerProduct Ω hΩ u u

/-- The H^1(Omega) inner product is symmetric. -/
theorem sobolevH1InnerProduct_comm (u v : SobolevH1 Ω hΩ) :
    sobolevH1InnerProduct Ω hΩ u v = sobolevH1InnerProduct Ω hΩ v u := by
  simp [sobolevH1InnerProduct, mul_comm]

end NavierStokes
