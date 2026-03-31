# Changelog

All notable changes to this project are documented here.

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
