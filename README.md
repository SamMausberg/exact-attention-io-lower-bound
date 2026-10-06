# An I/O Lower Bound for Exact Attention

Samuel Mausberg, Independent Researcher

Every bounded deterministic real-arithmetic program that computes exact softmax attention on
`Q, K, V` in `R^{n x d}` needs `Omega(nd + n^2/M)` transfers between slow memory and an `M`-word
cache, for `n >= d^2`, `d >= 2` and `M >= d^2`. The paper also shows that field containment alone
cannot recover the dimension factor, and proves the full `Omega(nd + n^2 d^2/M)` bound under
numerical pair coverage.

## Contents

- `paper/main.tex`, `paper/figures/epoch.tex`, `paper/references.bib`: source of the paper.
- `paper/main.pdf`: compiled paper.
- `paper/main.bbl`: generated bibliography.

## Building the paper

```sh
cd paper
./build.sh
```

The build needs pdfLaTeX and BibTeX with standard packages (`newtx`, `mathtools`, `microtype`,
`aliascnt`, `flafter`, TikZ, `hyperref`, `cleveref`, `fancyhdr`) and the `alphaurl` bibliography
style from `urlbst`. `LATEX` and `BIBTEX` can be set to executable paths.
