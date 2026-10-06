# Lean formalization

Lean 4 (`leanprover/lean4:v4.34.0-rc2`) with Mathlib at revision `2631d1cc`. Paper results are cited
by title and TeX label, so the Lean files do not depend on the numbering of the manuscript.

## Building

```sh
lake exe cache get
python3 verify.py
```

`verify.py` scans the sources for `sorry`, `admit`, `axiom`, `native_decide`, and similar tokens,
runs `lake build` with warnings treated as errors, runs `AxiomAudit.lean`, and checks that every
listed theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. It writes
`lean-verification.json`.

## Map from the paper

| Paper (TeX label) | Lean theorems | File |
|---|---|---|
| Exponentials of polynomials (`lem:independence`) | `exp_poly_relation_eq_zero`, `algebraicIndependent_exp_poly` | `ExpPoly.lean` |
| The coefficient field (`prop:attention-field`) | `attnOutput_isLinearMap`, `hasDerivAt_attnOutput_value`, `attnWeight_div_last`, `attnOutput_eq_ratio`, `hasDerivAt_attnRatio`, `ratioExponent_intCombNonconst`, `attnRatio_algebraicIndependent`, `attnRatio_eq_deriv_div_deriv`, `attnOutput_deriv_mem_ratioField`, `ratio_algebraicIndependent`, `ratio_eq_jacobian_div` | `CoefficientField.lean`, `Main.lean` |
| An open execution path (`lem:open`) | `exists_open_path`, `OpenPath.Expr.analyticAt_eval` | `OpenPath.lean` |
| Analytic functions on an open path (`sec:model`) | `isDomain_analyticRing`, `polyToAnalytic_injective`, `ratFuncToAnalytic_injective` | `AnalyticField.lean` |
| Numerical factorisation (`lem:factor-rank`) | `finrank_range_fderiv_le_of_eqOn_comp`, `le_of_eqOn_comp_id` | `Factorization.lean` |
| Boundary factorisation (`lem:boundary`) and `eq:chain` | `boundary_factorization`, `epoch_chain_rule`, `chain_rule_jacobian` | `History.lean` |
| I/O and the first-derivative field (`thm:history`) | `History.Trace.row_mem_history`, `epochs_le`, `history_bound` | `History.lean` |
| Exact attention, counting part (`thm:attention`) | `attention_io_lower_bound`, `attention_bound_of_trace` | `Main.lean`, `History.lean` |
| The seven-product decomposition (`lem:strassen`, `app:strassen`) | `strassen_mul`, `strassen_minor_eq`, `strassen_minor_det`, `strassen_base_linearIndependent`, `strassen_bilinear`, `strassen_bilinear_linearIndependent`, `strassen_forms_span`, `strassen_eq_zero_of_forms`, `strassen_forms_ne_zero`, `strassen_decomposition` | `Strassen.lean` |
| Algebraic parts of `thm:bilinear-prefix` | `bilinearPrefix_kernel_product`, `bilinearPrefix_hasDerivAt_aux`, `bilinearPrefix_leaf_recovery`, `bilinearPrefix_intCombNonconst`, `bilinearPrefix_leafExp_algebraicIndependent` | `BilinearPrefix.lean` |
| `cor:subintermediate` | `Certificate.sigma_lt_three`, `subintermediate` | `Certificate.lean` |
| Counting argument of `thm:certificate` | `no_certificate_charge` | `Certificate.lean` |
| Rank of a selected dot-product family (`lem:pair-rank`) | `pairRank_card_le_degree_sums`, `pairRank_exists_dense_open`, `pairRank` | `PairRank.lean` |
| Numerical compression (`thm:compression`) | `compression` | `Compression.lean` |
| The full bound under pair coverage (`cor:pair-cover`) | `pairCover_epoch`, `pairCover` | `Compression.lean` |

`AxiomAudit.lean` lists every theorem in the table together with the lemmas they rest on.

## Modelling choices

- **Exact attention.** `attention_io_lower_bound` concerns an execution trace (`History.Trace`) over
  the rational function field `ℝ(x)` inside the fraction field of analytic functions on a nonempty
  connected open input set. If the trace's output words carry the Jacobian rows of `Y`, with
  `n ≥ 2`, `d ≥ 2` and at least `nd` transfers, then `(nd + n²/M)/32 ≤ I`. The `n(n-1)`
  algebraically independent output derivatives are not assumed; they come from
  `ratio_algebraicIndependent` and `ratio_eq_jacobian_div`. The local Jacobians of the trace are
  arbitrary matrices over the field, and the results for `lem:open`, `lem:boundary` and
  `eq:chain` are proved separately and not used by this theorem.
- **Traces.** A trace records a derivative row for every word, epochs with at most `M` transfers
  (exactly `M` except the last), incoming and outgoing words with `a_t, b_t ≤ 2M`, and local
  Jacobians `Λ_t` with `DB_t = Λ_t DC_t`.
- **Programs.** `OpenPath.lean` models a bounded program as a finite decision tree with three-way
  sign tests of straight-line expressions over `+, -, ×, ÷, exp`, together with the condition that
  executed divisions have nonzero denominators.
- **`lem:independence`** is stated with polynomial coefficients, as the paper's proof begins by
  clearing denominators. `algebraicIndependent_exp_poly` includes the input coordinates in the
  independent family, which is equivalent to independence over `ℝ(x)`.
- **Strassen.** At depth `k` the coefficients are products over levels of the base tables, indexed
  by digit strings and transported to `Fin (2^k)` and `Fin (7^k)`.
- **`thm:certificate`.** The condition that a history contains `𝒯` is an abstract predicate, and
  the prefix facts from `thm:bilinear-prefix` (transfer count, epoch count, containment) enter as
  hypotheses. The conclusion is the nonexistence of charges with the stated properties on these
  prefix histories. The attention computation that follows each prefix is not modelled.
- **`thm:compression`.** Numerical recovery means a C¹ decoder on an open neighbourhood of the
  image of the summaries. The centred family allows any reference key.

## Not formalized

- The passage from a program to a trace. In `attention_io_lower_bound` the trace, the bounds
  `a_t, b_t ≤ 2M` and the `nd` output stores are hypotheses. `lem:boundary` is proved for
  straight-line expressions in which same-epoch reloads are already substituted.
- The field equalities `F₀(DY) = 𝒯` (`eq:attention-field`) and `F₀(Dg) = F₀(E_abr)`
  (`eq:aux-field`) as equalities of subfields, and the values `τ₁(Y) = n(n-1)` and `τ₁(g) = B²R`.
  For `Y`, both inclusions are proved as identities between functions. For `g`, the leaf
  recovery and the kernel product give `E_abr` and `𝒯` in terms of derivatives of `g` and of the
  `E_abr`. The independence statements behind both transcendence degrees are proved.
- The I/O and work bounds of `thm:bilinear-prefix` (`eq:aux-io`) and of `app:upper`, and the
  containment of `𝒯` in the history of every epoch partition of the prefix. The independence of
  the leaf exponentials is stated in the variables `Q, K`.
- The instruction and transfer bounds of `lem:strassen`, and the identification of the
  digit-product forms with the recursion on `2 × 2` blocks. The identities do not depend on it.
- The example `H_L` after `thm:history` and the product-of-exponentials example after
  `cor:pair-cover`.
