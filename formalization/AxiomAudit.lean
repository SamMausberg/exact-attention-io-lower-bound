import ExactAttention

/-! `#print axioms` for every theorem that corresponds to a statement in the paper. -/

-- ExpPoly.lean
#print axioms ExactAttention.ExpPoly.coeff_eq_zero_of_eventually_sum_mul_exp  -- lem:independence
#print axioms ExactAttention.exp_poly_relation_eq_zero  -- lem:independence
#print axioms ExactAttention.algebraicIndependent_exp_poly  -- lem:independence
-- Character.lean
#print axioms ExactAttention.exp_poly_linear_relation_eq_zero  -- lem:independence
#print axioms ExactAttention.linearIndependent_expElem  -- lem:independence
#print axioms ExactAttention.ratioElem_eq_expElem  -- lem:character
#print axioms ExactAttention.exp_mem_adjoin_exp  -- lem:character
-- CoefficientField.lean
#print axioms ExactAttention.attnOutput_isLinearMap  -- prop:attention-field
#print axioms ExactAttention.hasDerivAt_attnOutput_value  -- prop:attention-field
#print axioms ExactAttention.attnWeight_div_last  -- prop:attention-field
#print axioms ExactAttention.attnOutput_eq_ratio  -- prop:attention-field
#print axioms ExactAttention.hasDerivAt_attnRatio  -- prop:attention-field
#print axioms ExactAttention.ratioExponent_intCombNonconst  -- lem:independence
#print axioms ExactAttention.attnRatio_relation_eq_zero  -- prop:attention-field
#print axioms ExactAttention.attnRatio_algebraicIndependent  -- prop:attention-field
#print axioms ExactAttention.attnRatio_eq_deriv_div_deriv  -- prop:attention-field
#print axioms ExactAttention.attnOutput_deriv_mem_ratioField  -- prop:attention-field
-- OpenPath.lean
#print axioms ExactAttention.OpenPath.Expr.analyticAt_eval  -- lem:open
#print axioms ExactAttention.exists_open_path  -- lem:open
-- AnalyticField.lean
#print axioms ExactAttention.isDomain_analyticRing  -- lem:open
#print axioms ExactAttention.polyToAnalytic_injective  -- lem:open
#print axioms ExactAttention.ratFuncToAnalytic_injective  -- lem:open
-- History.lean
#print axioms ExactAttention.History.Trace.row_mem_history  -- eq:history
#print axioms ExactAttention.epochs_le  -- eq:epochs
#print axioms ExactAttention.history_bound  -- thm:history
#print axioms ExactAttention.attention_bound_of_trace  -- thm:attention
#print axioms ExactAttention.chain_rule_jacobian  -- eq:chain
#print axioms ExactAttention.boundary_factorization  -- lem:boundary
#print axioms ExactAttention.epoch_chain_rule  -- eq:chain
-- Main.lean
#print axioms ExactAttention.ratio_algebraicIndependent  -- prop:attention-field
#print axioms ExactAttention.ratio_eq_jacobian_div  -- prop:attention-field
#print axioms ExactAttention.attention_io_lower_bound  -- thm:attention
-- Factorization.lean
#print axioms ExactAttention.finrank_range_fderiv_le_of_eqOn_comp  -- lem:factor-rank
#print axioms ExactAttention.le_of_eqOn_comp_id  -- lem:factor-rank
-- PairRank.lean
#print axioms ExactAttention.linearScore_rank_bound  -- lem:pair-rank
#print axioms ExactAttention.spanIO  -- eq:span-io
#print axioms ExactAttention.spanIO_bound  -- cor:pair-cover
-- Compression.lean
#print axioms ExactAttention.compression  -- thm:compression
#print axioms ExactAttention.compression_finrank_span  -- thm:compression
#print axioms ExactAttention.pairCover_epoch  -- cor:pair-cover
#print axioms ExactAttention.pairCover  -- cor:pair-cover
#print axioms ExactAttention.le_finrank_span_of_centred  -- cor:pair-cover
#print axioms ExactAttention.le_finrank_span_of_scores  -- cor:pair-cover
-- ScoreExp.lean
#print axioms ExactAttention.linCoeff_rank_le  -- thm:score-exp
#print axioms ExactAttention.centred_eq_sum_linCoeff  -- thm:score-exp
#print axioms ExactAttention.centred_mem_span_linCoeff  -- thm:score-exp
#print axioms ExactAttention.ScoreExp.count_arith  -- cor:pair-cover
#print axioms ExactAttention.score_exp_io_lower_bound  -- thm:score-exp
-- Strassen.lean
#print axioms ExactAttention.Strassen.products_eq  -- eq:strassen-base
#print axioms ExactAttention.strassen_mul  -- eq:strassen-base
#print axioms ExactAttention.strassen_minor_eq  -- app:strassen
#print axioms ExactAttention.strassen_minor_det  -- app:strassen
#print axioms ExactAttention.strassen_base_linearIndependent  -- lem:strassen
#print axioms ExactAttention.Strassen.mul_transpose_apply_of_tensor  -- eq:bilinear
#print axioms ExactAttention.strassen_bilinear  -- lem:strassen
#print axioms ExactAttention.strassen_bilinear_linearIndependent  -- lem:strassen
#print axioms ExactAttention.strassen_forms_span  -- lem:strassen
#print axioms ExactAttention.strassen_eq_zero_of_forms  -- lem:strassen
#print axioms ExactAttention.strassen_forms_ne_zero  -- lem:strassen
#print axioms ExactAttention.strassen_decomposition  -- lem:strassen
-- BilinearPrefix.lean
#print axioms ExactAttention.bilinearPrefix_kernel_product  -- thm:bilinear-prefix
#print axioms ExactAttention.bilinearPrefix_hasDerivAt_aux  -- thm:bilinear-prefix
#print axioms ExactAttention.bilinearPrefix_leaf_recovery  -- thm:bilinear-prefix
#print axioms ExactAttention.bilinearPrefix_expPoly_isHomogeneous  -- thm:bilinear-prefix
#print axioms ExactAttention.bilinearPrefix_expPoly_linearIndependent  -- thm:bilinear-prefix
#print axioms ExactAttention.BilinearPrefix.intCombNonconst_of_linearIndependent  -- lem:independence
#print axioms ExactAttention.bilinearPrefix_intCombNonconst  -- thm:bilinear-prefix
#print axioms ExactAttention.bilinearPrefix_leafExp_algebraicIndependent  -- thm:bilinear-prefix
-- Certificate.lean
#print axioms ExactAttention.subintermediate  -- cor:subintermediate
#print axioms ExactAttention.no_certificate_charge  -- thm:certificate
#print axioms ExactAttention.Certificate.sigma_lt_three
