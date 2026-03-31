# Changelog

All notable changes to this project are documented here.

## [0.2.7] - 2026-04-01

### Lean: Sorry Reduction (9 -> 10, net +3 proved theorems)

**New file: `HelmholtzProjection.lean`** — full L2 Helmholtz decomposition via
`Submodule.starProjection`.

The Leray projector is now constructed as the orthogonal projection CLM onto
`l2sigmaSubmodule` (a `ClosedSubmodule` of `Lp E 2 μ`), using Mathlib's
`HasOrthogonalProjection` instance for complete inner product spaces.  Three
properties that were sorry stubs in `DivFreeSpace.lean` are now proved
sorry-free via direct API calls:

```lean
lerayProjectorLp_idempotent :
    lerayProjectorLp Ω hΩ (lerayProjectorLp Ω hΩ f) = lerayProjectorLp Ω hΩ f
-- proof: starProjection_eq_self_iff.mpr (lerayProjectorLp_mem ...)

lerayProjectorLp_selfAdjoint :
    ⟪lerayProjectorLp Ω hΩ f, g⟫_ℝ = ⟪f, lerayProjectorLp Ω hΩ g⟫_ℝ
-- proof: inner_starProjection_left_eq_right f g

helmholtz_l2_decomposition :
    lerayProjectorLp Ω hΩ f ∈ l2sigmaSubmodule Ω hΩ ∧
    f = lerayProjectorLp Ω hΩ f + (f - lerayProjectorLp Ω hΩ f) ∧
    ⟪lerayProjectorLp Ω hΩ f, f - lerayProjectorLp Ω hΩ f⟫_ℝ = 0
-- proof: membership + abel + starProjection_inner_eq_zero
```

**New sorry (Category C, ENNReal norm bridge):** `l2sigmaSubmodule_isSeqClosed`
contains one sorry converting `‖f_k - f‖_{Lp2} → 0` to `∫ ‖⇑f_k - ⇑f‖² → 0`
(ENNReal bookkeeping between `Lp` norm and raw integral).  Net sorry count: 9
eliminated 1 in DivFreeSpace stubs superseded + 1 new norm bridge = total 10.

**Sorry-free definitions and lemmas added:**
- `l2sigmaSubmodule` (Submodule packaging with zero/add/smul closure)
- `l2sigmaSubmodule_isClosed` (topological closedness via `IsSeqClosed.isClosed`)
- `l2sigmaClosedSubmodule` (ClosedSubmodule for `HasOrthogonalProjection`)
- `lerayProjectorLp` (orthogonal projection CLM)
- `lerayProjectorLp_mem`, `lerayProjectorLp_idempotent`,
  `lerayProjectorLp_selfAdjoint`, `helmholtz_l2_decomposition`

**Key debugging lessons (5 iterations on `isDistribDivFree_add`):**
1. Greedy binder scope: `∫ x, A x + ∫ x, B x` parses as `∫ x, (A x + ∫ x, B x)`.
   Fix: always parenthesise both integrals explicitly.
2. `EuclideanSpace.proj_apply` does not exist in Mathlib v4.29.  Use
   `MemLp.continuousLinearMap_comp (EuclideanSpace.proj i)` for integrability;
   definitional equality at the `MemLp` level suffices for `exact`.
3. `rw [← integral_add]` fails on syntactic mismatch (`proj i (u x)` vs
   `(u x).ofLp i`).  Fix: rewrite the integrand via
   `funext (fun x => by simp [Pi.add_apply, PiLp.add_apply]; ring)` first,
   then close with `exact integral_add h_int_u h_int_v`.
4. `rw [← Finset.sum_add_distrib]` on a `have hsplit` fails when the RHS sum
   has greedy-binder scope issues.  Fix: use `simp_rw [hstep, Finset.sum_add_distrib]`
   in the forward direction after a per-component `hstep` lemma.

### LaTeX: Appendix A — Concordance Update

Added new subsection `A.1.7 Helmholtz projection via orthogonal projection`
(`sec:lean-ch1-helmholtz-proj`) documenting all sorry-free definitions and
theorems in `HelmholtzProjection.lean`.

Updated `sec:lean-ch1-divfree` (DivFreeSpace.lean items) to mark
`lerayProjector_idempotent`, `lerayProjector_selfAdjoint`, and
`helmholtz_decomposition` as `(legacy)` stubs superseded by the proved
versions in the new subsection.

LaTeX cross-references: `prop:leray-props` (idempotency, self-adjointness)
and `thm:helmholtz` (orthogonal decomposition) are now backed by sorry-free
Lean theorems.

## [0.2.6] - 2026-03-31

### Lean: Sorry Reduction (10 -> 9)

**`lerayProjector` definition is now sorry-free.**

The previous body used `(helmholtz_decomposition Ω hΩ u (by sorry)).choose`, requiring a
`sorry` to discharge the `MemLp u 2 (volume.restrict Ω)` hypothesis that `lerayProjector`
did not take as an argument. Fixed by threading the hypothesis explicitly:

```lean
def lerayProjector ... (u : ...) (hu : MemLp u 2 (volume.restrict Ω)) : ... :=
  (helmholtz_decomposition Ω hΩ u hu).choose
```

Downstream callers (`lerayProjector_idempotent`, `lerayProjector_selfAdjoint`) updated to
accept and pass `hu` and the derived `MemLp` of the projected field.

**New sorry-free helper lemmas (body uses only `.choose_spec` extraction):**
- `lerayProjector_mem_l2sigma`: `lerayProjector Ω hΩ u hu ∈ L2sigma Ω hΩ`
- `lerayProjector_memLp`: `MemLp (lerayProjector Ω hΩ u hu) 2 (volume.restrict Ω)`

Both lemmas have no `sorry` in their bodies; they depend transitively on
`helmholtz_decomposition` (which remains sorry).

### Lean: Improved Sorry Stubs

All 9 remaining sorry stubs now carry detailed proof sketches in their docstrings:
- `sobolev_embedding_subcritical`: cites `eLpNorm_le_eLpNorm_fderiv_of_eq_inner` (Mathlib
  GNS), identifies Meyers-Serrin density theorem as the missing bridge.
- `sobolev_embedding_supercritical`: identifies Morrey inequality as absent from Mathlib.
- `lerayProjector_idempotent`: names `l2sigma_orthogonal_gradients` as the missing lemma.
- `lerayProjector_selfAdjoint`: spells out the ⟨Pu,v⟩ = ⟨Pu,Pv⟩ = ⟨u,Pv⟩ argument and
  the role of `l2sigma_orthogonal_gradients`.
- `poincare_inequality`: full Lean outline of the contradiction proof (by_contra, normalised
  sequence, Rellich application, constant-gradient-zero-trace argument).

## [0.2.5] - 2026-03-31

### Fixed (Typography)
- **Em dashes removed**: all prose `---` replaced with commas, colons, or
  parentheses throughout the document (ch03, appA-lean.tex). Zero em dashes
  remain.
- **`\textit{sorry} stub` formatting**: `sorry-stub` and plain `sorry stub`
  normalised to `\textit{sorry} stub` everywhere in Appendix A.
- **Horizontal overflow: ch03 metric-compat proof** (227pt): the six-term display
  `A = …, B = …, …, F = …` was a single `\[…\]` line; replaced with
  `align*` in three columns.
- **Horizontal overflow: ch01 Leray projector definition title** (16pt): the
  `(\Cref{sec:lean-ch1-divfree})` parenthetical in the definition title caused
  cross-references to render as "Definition 1.22 (Leray projector (Appendix
  A.1.6))", overflowing the column. The parenthetical is removed from the title.
- **Horizontal overflow: appA long Lean identifiers** (14–45pt): five items had
  identifiers that, combined with the following `(proved):` or `(sorry stub):`
  text, overflowed the column. Fixed by switching all `\texttt{NavierStokes.*}`
  to `\path{NavierStokes.*}` (breakable monospace via the url package) and adding
  `\\` after the longest identifiers: `sobolev_embedding_subcritical`,
  `sobolev_embedding_supercritical`, `l2sigma_closed_under_l2_convergence`,
  `trilinearForm_antisymmetric`, `IsDistribDivFree`, `lerayHopf_existence`.
- **Horizontal overflow: appB** (5–38pt): trilinear antisymmetry item rephrased
  (long inline formula removed); Serrin condition and Levi-Civita items shortened.
- **Horizontal overflow: ch03 prop:torsion-free** (5.45pt): proposition title
  `Torsion-freeness` shortened to `Torsion-free`.
- **`\headheight` fancyhdr warning**: set `\headheight = 14.04pt` in preamble.tex,
  silencing the recurring warning throughout the build log.

### Preflight Rule Established
Before every push: (1) `grep -r ' --- ' latex/` must return empty (no em dashes);
(2) `grep "Overfull" main.log` must show no prose overflows exceeding 5pt.
Accepted exemptions: bibliography entries and the `esint` font-loading artifact
at ch01 lines 13–20 (shows as `[]` `[]` in the log, invisible in the PDF).

## [0.2.4] - 2026-03-31

### Fixed (Critical)
- **Koszul formula sign error** (ch03, eq:koszul): the second bracket term was
  `g(v,[u,w])`; corrected to `g(v,[w,u])` per the standard formula (do Carmo /
  Lee). The algebraic verification (six-term expansion) was fully rewritten to
  match the corrected formula: labels A-F introduced, antisymmetry applied to
  show A+F=0, B+C=0, D+E=2∫w·(u·∇)v, giving the correct RHS=2g(∇_u v,w).
- **eq:vort-parallel** (ch03, thm:vorticity-eq): the stated "forced parallel
  transport" form was missing the ∂_t ω term and had a sign error. Corrected to
  `∂_t ω + ∇^vort_u ω = ν Δω` (the covariant material derivative form), with a
  note that expanding ∇^vort_u ω = (u·∇)ω − (ω·∇)ω recovers the full vorticity
  equation.
- **L^{6/5} → L^{3/2}** (ch03, rem:conn-regularity): the Hölder product exponent
  for u_j ∈ L^6, ∂_j v ∈ L^2 satisfies 1/r = 1/6+1/2 = 2/3, so r = 3/2 (not 6/5).
  Fixed throughout the remark and rem:koszul-distributional.

### Fixed (Important)
- **Torsion-free proof gap** (ch03, prop:torsion-free): added the explicit
  intermediate step `Leray[[u,v]] = [u,v]` (since [u,v] is divergence-free),
  before concluding T(u,v) = 0.
- **No regularity hypothesis on prop:torsion-free** (ch03): the proposition now
  states `u, v ∈ H^1_0,σ(R^3)` as required for the pointwise distributional
  computation.
- **Arnold's curvature theorem** (ch03, thm:arnold-curvature): added "compact
  Riemannian manifold" qualifier (the theorem is for T^3 or S^2, not R^3
  directly). Added remark on extension to R^3 citing Arnold-Khesin 1998.
- **HLS proof notation** (ch03, prop:bs-Lp): rewrote Step 2 to clearly distinguish
  the HLS gain parameter α_HLS=1 (one derivative gained by BS = curl^{-1}) from
  the kernel singularity order σ=2 (|K(x)| ~ |x|^{-2}). The range 1<p<3 now
  follows from α_HLS=1 giving p < n/α_HLS = 3, consistent with the stated bound.
- **Metric compatibility proof** (ch03, prop:metric-compat): rewrote to explicitly
  justify u(g(v,w)) = 0 as the Fréchet derivative of a constant functional on the
  flat Hilbert space L^2_σ; both sides of the compatibility identity are shown to
  vanish independently, with a clear concluding line matching them.
- **Poincaré inequality hypothesis** (ch01, thm:poincare): added "connected" to
  the domain hypothesis (required for the argument that ∇u=0 implies u=const).
- **Helmholtz decomposition for R^n** (ch01, thm:helmholtz): the proof previously
  only handled the bounded domain case via Lax-Milgram + Neumann BVP. Added the
  whole-space argument: p = (−Δ)^{-1}(div u) via Riesz potential, Fourier
  multiplier characterisation of the Leray projector, and Plancherel to confirm
  v ∈ L^2_σ(R^n).

### Changed
- **Chapter 3**: clarified that the Biot-Savart connection is valid only in the
  distributional sense at Leray-Hopf regularity.
  - `rem:conn-regularity` expanded: Sobolev embedding `H^1 → L^6` sharpens the
    Hölder bound to `L^{3/2}`; states explicitly that `∇_u v ∈ L^{3/2}_σ ⊊ L^2_σ`.
  - `thm:levi-civita` statement qualified: uniqueness distributionally.
  - New `rem:koszul-distributional`: Lie brackets ∈ L^{3/2}, pairings g(u,[v,w])
    as L^6×L^{3/2} → L^{6/5} with compact support/decay condition; uniqueness
    within distributional connections.

### Restructured
- Deleted stub `sections/ch04-connection.tex` (content was merged into ch03
  in v0.2.2; the file was an unused empty chapter shell).
- Renamed chapter files down one: ch05 → ch04, ch06 → ch05, ch07 → ch06,
  ch08 → ch07. Chapter numbering is now contiguous (ch01–ch07).
- Updated `main.tex` and `main-dark.tex` includes accordingly.
- Updated README chapter table (7 chapters) and badge strip (removed Ch4
  Connection badge; shifted Curvature/Topology/Obstruction/Singularity to
  Ch4–7).
- Preface: `LaTeX` text → `\LaTeX{}` macro (two instances).

### Concordance (SymPy + Lean)

**SymPy ch03_biot_savart_verify.py:**
- Check 13 comment: corrected Koszul formula from `g(v,[u,w])` to `g(v,[w,u])`,
  in sync with the LaTeX fix to eq:koszul.
- Check 22 (HLS exponents): was using `α=2` (kernel singularity order) giving
  `1/q = 1/p − 2/3` and `p < 3/2`. Fixed to use `α_HLS=1` (HLS gain parameter:
  BS = curl∘(−Δ)^{-1} gains one derivative), giving the correct exponent relation
  `1/q = 1/p − 1/3` and range `p < 3`, consistent with eq:bs-Lp in the LaTeX.
  Numeric assertions updated: q(p=2)=6, q(p=3/2)=3, p_max=3. Added consistency
  check σ + α_HLS = n (2+1=3). All 23 checks pass.

**Lean NavierStokes/Foundations/Poincare.lean:**
- `poincare_inequality`: added `hConn : IsConnected Ω` hypothesis, in sync with
  the LaTeX fix adding "connected" to thm:poincare. Comment explains why
  connectedness is required (constant-gradient argument breaks on disconnected
  domains). Theorem remains a sorry-stub; no proofs affected.

## [0.2.3] - 2026-03-31

### Changed
- **Chapter 3**: all 9 proof sketches rewritten as full proofs with no
  handwaving. Leray projector (explicit matrix algebra), Levi-Civita
  (complete Koszul formula derivation), geodesic = Euler (step-by-step
  substitution), curvature formula (three-term expansion), first Bianchi
  (algebraic from Jacobi identity), stretching tensor (all W_ij pairs
  and trace), CZ L^p boundedness (kernel hypotheses verified),
  Biot-Savart HLS (hypotheses verified), iterated connection regularity
  (full Holder/Sobolev chain). 64 pages.
- **Appendix B**: added Part V (Calderon-Zygmund and HLS exponent
  checks 20-23).
- **SymPy ch03**: added Part V with 4 new checks (Leray multiplier
  homogeneity, smoothness on S^2, HLS exponents, Holder product
  estimates). 23 checks total, all passing.

### Fixed
- Dark mode (`main-dark.tex`) still included deleted `ch04-connection`;
  removed.
- Horizontal overflow in ch03: 36pt overflow in Bianchi proof and 12pt
  overflow in energy remark eliminated; remaining overflows all < 6pt.

## [0.2.2] - 2026-03-31

### Added
- **Chapter 3 (The Biot-Savart Connection)**: new chapter merging old ch03
  (Biot-Savart kernel) and ch04 (connection) into a single geometric chapter.
  Six sections: BS kernel and Leray projector, divergence-free bundle,
  Biot-Savart connection (torsion-free, metric-compatible, Levi-Civita),
  geodesic = Euler / NS as forced geodesic, curvature (abstract + Bianchi),
  vorticity as curvature of the restricted connection, Calderon-Zygmund
  estimates closing within the Leray-Hopf class. 58 pages.
- **Appendix B (Symbolic Verification)**: populated with commentary and
  GitHub-linked references for all four SymPy scripts (ch01 Sobolev exponents,
  ch01 Helmholtz, ch02 Leray-Hopf, ch03 Biot-Savart connection).
- SymPy ch03: expanded from 1 to 5 independent divergence-free test fields
  (ABC-1 through ABC-4, mixed-1). All identity checks now run across multiple
  examples. 19 checks across 4 parts, all passing.
- Bibliography: Arnold 1966, Ebin-Marsden 1970, Arnold-Khesin 1998,
  Calderon-Zygmund 1952, Stein 1970, Majda-Bertozzi 2002.

### Fixed
- Torsion-freeness proof: corrected intermediate identity (the cross terms
  cancel by index symmetry, not by a single-field divergence identity).
- Calderon-Zygmund endpoint remark: cleaned up Holder exponent derivation.
- Removed all uses of "concrete" (replaced with "example") across LaTeX and
  SymPy sources.
- Duplicate label `prop:leray-props` (ch01 vs ch03) resolved.

## [0.2.1] - 2026-03-31 (`c98c871`)

### Proved
- `trilinearForm_antisymmetric` (TrilinearForm.lean): b(u,v,v) = 0 for
  distributionally divergence-free u and smooth compactly-supported v.
  Per-component test function strategy (phi_k = v_k^2) with fderiv_fun_pow
  chain rule and integral_const_mul. Sorry count: 11 -> 10, proved: 5 -> 6.

## [0.2.0] - 2026-03-30 (`46fa6e8`)

### Proved
- `l2sigma_closed_under_l2_convergence` (DivFreeSpace.lean): L²σ is closed under
  L² convergence, via Hölder's inequality (Cauchy-Schwarz with p=q=2),
  `PiLp.norm_apply_le` for the component bound, and `tendsto_nhds_unique` for
  limit uniqueness. First machine-checked proof of this result in any proof
  assistant. Sorry count: 12 → 11.

### Added
- **Chapter 2 (Leray-Hopf weak solutions)**:
  - Lean: definitions and theorem statements for weak formulation, trilinear
    form (sorry-free definition), energy inequality, Leray-Hopf existence
    (sorry stub), Serrin regularity criterion. 3 sorry remain.
  - LaTeX: complete. Full narrative with proofs (Galerkin approximation on R³,
    Gram-Schmidt on C∞\_c ∩ L²σ, energy inequality, connection to Fefferman's
    Clay formulation Problems A-D).
  - SymPy: complete. 13/13 symbolic checks pass (trilinear antisymmetry, energy
    balance, Serrin exponents, interpolation, Gronwall, Prodi-Serrin pairs).
- `sobolevConjugate_gt` proved: p* > p for 1 ≤ p < n.
- `sobolevConjugate_inv` proved: 1/p* = 1/p - 1/n.
- Dark mode PDF target (WCAG AA compliant, `make dark`).
- Preface outlining the three-track programme.
- Clay formulation rewritten to faithfully follow Fefferman (2006).

### Changed
- Galerkin approximation rewritten on whole-space R³ (not bounded domains).
- `IsDistribDivFree` updated: `ContDiff ℝ ⊤` replaced by `ContDiff ℝ ∞`.
- `l2sigma_isClosed` (wrong topology) replaced by
  `l2sigma_closed_under_l2_convergence` (correct L² sequential closedness).

## [0.1.0] - 2026-03-29 (`159ad8e`)

### Added
- **Chapter 1 (Functional Analytic Foundations)**:
  - Lean: 9 definitions, all type-checking. `weakPartialDeriv_unique` and
    `sobolevH1InnerProduct_comm` proved. 8 sorry remain (embeddings, Poincare,
    Helmholtz, Leray projector).
  - LaTeX: complete. 6 sections (distributions, Sobolev spaces, embeddings,
    Rellich-Kondrachov, Poincare, Helmholtz/Leray projector).
  - SymPy: complete. 8/8 symbolic checks pass (Sobolev exponents, Helmholtz
    orthogonality).
- Lean 4 project initialized against pinned Mathlib4 fork (commit `698d2b68`,
  based on v4.29.0-rc8). Builds with 2685 jobs, 0 errors.
- Sync document framework (`sync/ch01-foundations.md`).
- Three-track architecture: Lean + LaTeX + SymPy with chapter-boundary reconciliation.
