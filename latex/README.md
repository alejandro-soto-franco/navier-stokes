# LaTeX Build Instructions

The manuscript is typeset with XeLaTeX and Biber. Two output modes are provided: a light-mode PDF for print and a WCAG AA compliant dark-mode PDF for screen reading.

## Prerequisites

A full TeX Live installation (2023 or later) with `xelatex` and `biber` on `PATH`. No additional fonts or packages beyond the standard TeX Live distribution are required.

## Building

From the `latex/` directory:

```
make          # builds both light and dark PDFs
make light    # builds main.pdf only
make dark     # builds main-dark.pdf only
make clean    # removes all auxiliary files
```

Each target runs three XeLaTeX passes with a Biber pass after the first, which resolves all cross-references, citations, and the table of contents.

## Manual builds

If `make` is unavailable, run the following from the `latex/` directory:

```
xelatex -interaction=nonstopmode main.tex
biber main
xelatex -interaction=nonstopmode main.tex
xelatex -interaction=nonstopmode main.tex
```

For dark mode, substitute `main-dark` for `main` in every command above.

## Project structure

```
main.tex            Light-mode entry point
main-dark.tex       Dark-mode entry point (loads darkmode.sty)
preamble.tex        Shared package imports, macros, theorem environments
lightmode.sty       Colours and page styling for print
darkmode.sty        Colours and page styling for screen (dark background)
preface.tex         Preface and programme outline
bibliography.bib    BibLaTeX references (Biber backend)

sections/
  ch01-foundations.tex    Functional analytic foundations
  ch02-leray-hopf.tex    Leray-Hopf weak solutions
  ch03-biot-savart.tex    Biot-Savart law and vorticity
  ch04-connection.tex     Connection and parallel transport
  ch05-curvature.tex      Curvature of the diffeomorphism group
  ch06-topology.tex       Topological obstructions
  ch07-obstruction.tex    Obstruction theory
  ch08-singularity.tex    Singularity analysis

appendices/
  appA-lean.tex     Lean 4 formalisation appendix
  appB-sympy.tex    SymPy verification appendix
  appC-numerics.tex Numerical experiments appendix
  appD-code.tex     Code listings appendix
```

## Verification

After building, confirm no unresolved references:

```
grep -c "Warning.*undefined" main.log
```

A count of zero means all labels, citations, and cross-references resolved correctly.
