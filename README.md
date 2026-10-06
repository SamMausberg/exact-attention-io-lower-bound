# An I/O Lower Bound for Exact Attention

Samuel Mausberg, Independent Researcher

Every bounded deterministic real-arithmetic program that computes exact softmax attention on
`Q, K, V` in `R^{n x d}` needs `Omega(nd + n^2/M)` transfers between slow memory and an `M`-word
cache, for `n >= 2`, `d >= 2` and `M >= d^2`. When every exponential argument is a polynomial in
the full scores `q_i . k_j`, the bound improves to `Omega(nd + n^2 d^2/M)`, which is tight. The paper
also bounds the dimension of linear score mixtures recoverable from numerical summaries, and shows
that field containment alone cannot recover the dimension factor.

## Contents

- `paper/main.tex`, `paper/figures/epoch.tex`, `paper/references.bib`: source of the paper.
- `paper/main.pdf`: compiled paper.
- `paper/main.bbl`: generated bibliography.
- `formalization/`: Lean 4 formalization of the main lemmas and theorems. See
  `formalization/README.md` for the map from paper labels to Lean theorems and for what is not
  formalized.

## Building the paper

```sh
cd paper
./build.sh
```

The build needs pdfLaTeX and BibTeX with standard packages (`newtx`, `mathtools`, `microtype`,
`aliascnt`, `flafter`, TikZ, `hyperref`, `cleveref`, `fancyhdr`) and the `alphaurl` bibliography
style from `urlbst`. `LATEX` and `BIBTEX` can be set to executable paths.

## Checking the formalization

```sh
cd formalization
lake exe cache get
python3 verify.py
```

The script builds the Lean project with warnings treated as errors, rejects `sorry` and other
escape hatches, and checks that each listed theorem depends only on the standard axioms.
`attention_io_lower_bound` is the counting part of the main theorem: for an execution trace whose
outputs carry the Jacobian of attention, it derives `(nd + n^2/M)/32 <= I` from the formalized
derivative-field and independence results. The passage from a program to its trace is not
formalized.

