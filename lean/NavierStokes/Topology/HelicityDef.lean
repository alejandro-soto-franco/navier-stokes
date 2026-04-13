/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Navier-Stokes project -- Helicity definition.

Helicity H(u) = int u . omega dx = int A ^ dA (Chern-Simons invariant).
This is the topological content of Moffatt's linking number formula.

`curl` is defined here as the standard three-dimensional curl

    (curl u)_0 = d u_2 / d x_1 - d u_1 / d x_2
    (curl u)_1 = d u_0 / d x_2 - d u_2 / d x_0
    (curl u)_2 = d u_1 / d x_0 - d u_0 / d x_1

via Frechet derivatives against the canonical Euclidean basis. With this
in hand, `helicityDensity u x = inner (u x) (curl u x)` and
`helicity u = int helicityDensity u dx` are genuine definitions (not
sorry-stubs). The lemma `helicity_eq_integral_density` then reduces to
the definitional equality of the two sides.

The physical / analytic results that _do_ require proofs (helicity
conservation in the inviscid limit, Arnold's helicity-energy bound,
Freedman-He) still live as `sorry` in adjacent files.
-/
import NavierStokes.LerayHopf.WeakNSSolution
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

noncomputable section

namespace NavierStokes

/-- Partial derivative of the `j`-th component of a vector field `u : ℝ^3 → ℝ^3`
    with respect to the `i`-th coordinate, evaluated at `x`.

    This is `fderiv` of the scalar function `y ↦ u y j` applied to the
    `i`-th canonical Euclidean basis vector. -/
private def partialComp
    (u : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (i j : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  fderiv ℝ (fun y => u y j) x (EuclideanSpace.single i 1)

/-- The three-dimensional curl of a vector field.

    In components, `curl u = (∂_1 u_2 - ∂_2 u_1, ∂_2 u_0 - ∂_0 u_2, ∂_0 u_1 - ∂_1 u_0)`,
    matching the Levi-Civita convention `(curl u)_i = ε_{ijk} ∂_j u_k`. -/
def curl
    (u : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm fun i =>
    if i = 0 then partialComp u 1 2 x - partialComp u 2 1 x
    else if i = 1 then partialComp u 2 0 x - partialComp u 0 2 x
    else partialComp u 0 1 x - partialComp u 1 0 x

/-- Helicity density `h(x) = u(x) · curl(u)(x)` at a point, defined as the
    Euclidean inner product of the velocity and vorticity at `x`. -/
def helicityDensity
    (u : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  inner ℝ (u x) (curl u x)

/-- The helicity of a velocity field `u` is the integral of its helicity
    density against Lebesgue measure on ℝ³. This is the Chern-Simons
    functional of the velocity one-form `A = u♭`. -/
def helicity
    (u : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∫ x, helicityDensity u x

/-- The helicity equals the integral of the helicity density — true by
    definition of `helicity`. -/
theorem helicity_eq_integral_density
    (u : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) :
    helicity u = ∫ x, helicityDensity u x := rfl

end NavierStokes
