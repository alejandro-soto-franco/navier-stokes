/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Navier-Stokes project — Lean-dojo Millennium interop scaffold.

This file documents the correspondence between this project's formalisation and
the Lean-dojo
[LeanMillenniumPrizeProblems](https://github.com/lean-dojo/LeanMillenniumPrizeProblems)
formulation of the Clay Navier-Stokes Millennium Problem (Fefferman).

Lean-dojo packages Fefferman's four alternatives (A)-(D) as:

  MillenniumNSRDomain.FeffermanA           -- existence & smoothness on R^3
  MillenniumNSRDomain.FeffermanC           -- breakdown on R^3
  MillenniumNS_BoundedDomain.FeffermanB    -- existence & smoothness on T^3
  MillenniumNS_BoundedDomain.FeffermanD    -- breakdown on T^3
  MillenniumNS_BoundedDomain.FeffermanMillenniumProblem  -- (A ∨ C) ∨ (B ∨ D)

These target global **smooth** solutions (`GlobalSmoothSolution`), which is what
the Clay prize requires. Note: Leray-Hopf weak existence (our `lerayHopf_existence`)
is not FeffermanA; the Millennium Problem asks whether weak solutions can be
upgraded to smooth ones unconditionally.

The interop is therefore a two-level commitment:

1. **Weak-level** (immediate, cheap):
   The lean-dojo `GlobalSmoothSolution` of the R^3 Navier-Stokes system
   satisfies the weak integral identity encoded in our
   `IsWeakNSSolution`, and any such smooth solution is a Leray-Hopf solution
   (the energy inequality becomes equality in the smooth case).
   So a proof of `FeffermanA` would yield, as a corollary, existence of a
   Leray-Hopf solution matching our definition — this is the "smooth ⇒ Leray-Hopf"
   direction and is directly provable.

2. **Strong-level** (the Millennium Problem proper):
   Proving our chapter 6 singularity-analysis theorem closes the reconnection-
   dominance gap identified in chapter 5 and settles FeffermanA ∨ FeffermanC on R^3.
   That implication is exactly what the monograph targets; this file will host the
   compatibility theorem once both (a) our `main_theorem` lands sorry-free, and
   (b) lean-dojo is added as a Lake dependency.

We do **not** yet add `LeanMillenniumPrizeProblems` as a Lake dep — the versions
they track may lag ours, and the interop should not hold our build hostage. Instead
we mirror minimal signatures below (`LeanDojoShadow` namespace) so the theorem
statements can be stated, compiled against our own project, and audited.

When lean-dojo is added as a dep, swap `LeanDojoShadow.*` for
`MillenniumNavierStokes.*` throughout and the interop theorem should `rfl`-match
the real lean-dojo statement up to universe / `Euc` / `EuclideanSpace` conversions.
-/
import NavierStokes.LerayHopf.Existence

open MeasureTheory

noncomputable section

namespace NavierStokes

/-! ## Shadow signatures mirroring lean-dojo

The definitions in this namespace are deliberate shadows of
`LeanMillenniumPrizeProblems/Problems/NavierStokes/MillenniumRDomain.lean`.
Names and shapes match so that, when we add lean-dojo as a Lake dep, the
swap is mechanical. Types use our `EuclideanSpace ℝ (Fin n)` rather than
their `Euc ℝ n` (definitionally the same).
-/

namespace LeanDojoShadow

/-- Mirror of `MillenniumNSRDomain.InitialVelocityR3`. -/
abbrev InitialVelocityR3 : Type :=
  EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)

/-- Mirror of `MillenniumNSRDomain.ForceFieldR3`: a space-time force field. -/
abbrev ForceFieldR3 : Type :=
  EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 3)

/-- Mirror of `MillenniumNSRDomain.DivergenceFreeInitial`: the classical
    (not distributional) divergence-free condition for a smooth initial
    velocity. -/
def DivergenceFreeInitial (u₀ : InitialVelocityR3) : Prop :=
  ∀ x, ∑ i : Fin 3, fderiv ℝ (fun y => (u₀ y) i) x (EuclideanSpace.single i 1) = 0

/-- Mirror of `MillenniumNSRDomain.FeffermanCond4`: smoothness + fast decay
    of the initial velocity in every spatial direction. We do not reproduce
    the exact multi-index machinery here; the smoothness clause is the
    structurally relevant piece for the interop. -/
def FeffermanCond4 (u₀ : InitialVelocityR3) : Prop :=
  ContDiff ℝ ⊤ u₀ ∧
    ∀ (K : ℕ), ∃ C : ℝ, 0 < C ∧ ∀ x : EuclideanSpace ℝ (Fin 3),
      ‖u₀ x‖ ≤ C / (1 + ‖x‖) ^ K

/-- Mirror of `MillenniumNSRDomain.FeffermanCond7`: uniform-in-time bounded
    kinetic energy. -/
def FeffermanCond7
    (u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ∫ x, ‖u t x‖ ^ 2 ≤ C

/-- Mirror of `MillenniumNSRDomain.FeffermanCond6`: smoothness of the
    velocity-pressure pair on R^3 × [0, ∞). We elide the pressure here
    (the interop needs only the velocity regularity). -/
def FeffermanCond6
    (u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ContDiff ℝ ⊤ (Function.uncurry u)

/-- Mirror of `GlobalSmoothSolution` for the force-free Navier-Stokes system
    on R^3, capturing only the velocity-side content (pressure is inferred
    in the full PDE package via Leray projection). A full interop would
    also track the pressure field and the space-time PDE identity. -/
structure GlobalSmoothSolution
    (ν : ℝ) (_hν : 0 < ν)
    (u₀ : InitialVelocityR3) where
  u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)
  initial : u 0 = u₀
  smooth  : FeffermanCond6 u

/-- Mirror of `MillenniumNSRDomain.FeffermanA`: force-free existence and
    smoothness of a global solution on R^3, for every smooth, decaying,
    divergence-free initial velocity, with uniformly bounded kinetic
    energy.

    This is the Clay statement we would need to either prove or refute
    via the chapter-6 obstruction theorem. -/
def FeffermanA : Prop :=
  ∀ (ν : ℝ) (hν : 0 < ν) (u₀ : InitialVelocityR3),
    FeffermanCond4 u₀ → DivergenceFreeInitial u₀ →
      ∃ sol : GlobalSmoothSolution ν hν u₀, FeffermanCond7 sol.u

end LeanDojoShadow

/-! ## The immediate (weak-level) interop

A smooth global solution satisfies the weak-form integral identity that
defines `IsWeakNSSolution`, and hence is a Leray-Hopf weak solution
(the energy inequality becomes equality in the smooth regime).

The full proof of this direction is mechanical but depends on:
- the integration-by-parts that turns the classical PDE into the weak form
- the energy identity `(1/2) d/dt ‖u‖² + ν ‖∇u‖² = 0` for smooth solutions
- the fact that smooth `u₀` with bounded energy lies in `L²_σ`

The project's `IsWeakNSSolution` currently encodes the weak integral
identity abstractly (`weakFormulation : True` placeholder in
`WeakNSSolution.lean`), so the interop below is stated but deferred until
that placeholder is upgraded to a real integral identity.
-/

/-- A global smooth solution of the force-free R^3 Navier-Stokes system
    (in the sense of `LeanDojoShadow.GlobalSmoothSolution`) induces a
    Leray-Hopf weak solution of the same system.

    Status: `sorry` on two counts. First, the weak-form integral identity
    in `IsWeakNSSolution.weakFormulation` is currently a `True` placeholder
    and must be upgraded before a real proof can be given. Second, even
    once that upgrade lands, the proof itself requires integration by
    parts and the smooth energy identity, which are infrastructure work
    on top of Mathlib's Bochner integral over product domains. -/
theorem globalSmooth_implies_lerayHopf
    (ν : ℝ) (hν : 0 < ν) (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (sol : LeanDojoShadow.GlobalSmoothSolution ν hν u₀) :
    -- Place the L²_σ hypothesis on u₀ as a free parameter; in the full
    -- FeffermanA setup it is implied by Cond4 + DivergenceFreeInitial.
    u₀ ∈ L2sigma (Set.univ : Set (EuclideanSpace ℝ (Fin 3))) isOpen_univ →
    IsLerayHopfSolution ν hν sol.u u₀ := by
  sorry

/-! ## The strong-level interop (Millennium target)

If the chapter-6 obstruction theorem rules out the ReconnectionDominance
scenario unconditionally, FeffermanA ∨ FeffermanC is settled on R^3. The
concrete implication is stated as an abbreviation below; the real proof
awaits both chapter 6 and the signature upgrade in
`NavierStokes.Topology.ConcentrationTopology`. -/

/-- Compatibility target: a resolution of Fefferman's A / C disjunction on
    R^3. This is the ultimate output the project's monograph produces, and
    matches (modulo our shadow-shimming of `GlobalSmoothSolution`)
    `MillenniumNSRDomain.FeffermanA ∨ MillenniumNSRDomain.FeffermanC` in the
    lean-dojo formulation. -/
abbrev NavierStokesMillenniumR3 : Prop :=
  LeanDojoShadow.FeffermanA ∨
    (∃ (ν : ℝ) (hν : 0 < ν) (u₀ : LeanDojoShadow.InitialVelocityR3),
      LeanDojoShadow.FeffermanCond4 u₀ ∧
      LeanDojoShadow.DivergenceFreeInitial u₀ ∧
      ¬ (∃ sol : LeanDojoShadow.GlobalSmoothSolution ν hν u₀,
           LeanDojoShadow.FeffermanCond7 sol.u))

end NavierStokes
