/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Navier-Stokes project -- Helicity definition.

Helicity H(u) = int u . omega dx = int A ^ dA (Chern-Simons invariant).
This is the topological content of Moffatt's linking number formula.

All proofs are deferred (sorry).
-/
import NavierStokes.LerayHopf.WeakNSSolution

open MeasureTheory

noncomputable section

namespace NavierStokes

/-- The helicity of a divergence-free velocity field u is the L^2 inner product
    of u with its curl (vorticity).  Equivalently, the Chern-Simons functional
    of the velocity one-form A = u-flat. -/
def helicity
    (u : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) : ℝ :=
  sorry -- int_Omega u . (curl u) dx

/-- Helicity density h(x) = u(x) . omega(x) at a point. -/
def helicityDensity
    (u : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  sorry -- u(x) . curl(u)(x)

/-- The helicity equals the integral of the helicity density. -/
theorem helicity_eq_integral_density
    (u : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) :
    helicity u = sorry := by -- integral of helicityDensity u
  sorry

end NavierStokes
