import ExactAttention.Factorization
import ExactAttention.PairRank

/-!
# Numerical compression of score forms

This file proves `thm:compression` and `cor:pair-cover` of `app:recovery`.

An input is a pair `(x, y)` with `x = (Q, K)` and `y` in a real normed space `Y`. The space `Y`
holds the values `V` or any other input coordinates, so summaries may depend on all of them.
Summaries `S` numerically recover a target `f` on `U` (`NumericallyRecovers`) when a continuously
differentiable decoder, defined on an open neighbourhood of `S(U)`, sends `S z` to `f z` for every
`z ∈ U`. The targets are the affine score forms `c_ℓ + p_{C_ℓ}(Q, K)` or their exponentials
(`RecoversScores`).

The proof follows the paper. Numerical factorisation (`lem:factor-rank`) bounds the Jacobian rank
of the recovered forms by the number of summaries, and `lem:pair-rank` turns this into the bound.
For exponentials we compose the decoder with a coordinatewise logarithm, which decodes the
affine forms themselves. The projection `(x, y) ↦ x` is open, so the rank bound holds on an open
set of query and key inputs.

`compression_finrank_span` states the bound for the span of an arbitrary finite family of
coefficient matrices, which is the form used per epoch.

For `cor:pair-cover` the execution model is not formalized. Each epoch is represented by `2M`
continuously differentiable summaries on a common open input set (its incoming values, padded
with constants if there are fewer) and by the score forms it recovers. The relation
`e ≤ I / M + 1` (`eq:epochs`) and the bound `n d ≤ I` from the output stores are hypotheses. The
last two theorems check the span condition for families named in the remark after
`cor:pair-cover`: all scores or kernels, and ratios against a fixed key.
-/

namespace ExactAttention

open Finset Module PairRank

/-- Summaries `S` numerically recover a target `f` on `U` when a continuously differentiable
decoder, defined on an open neighbourhood of `S(U)`, sends `S z` to `f z` for every `z ∈ U`. -/
def NumericallyRecovers {X F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}
    (S : X → Fin m → ℝ) (U : Set X) (f : X → F) : Prop :=
  ∃ W : Set (Fin m → ℝ), ∃ Dec : (Fin m → ℝ) → F,
    IsOpen W ∧ S '' U ⊆ W ∧ ContDiffOn ℝ 1 Dec W ∧ ∀ z ∈ U, Dec (S z) = f z

/-- The affine score forms `c_ℓ + p_{C_ℓ}(Q, K)` of an input `((Q, K), y)`. -/
noncomputable def affineScores {n d B : ℕ} {Y : Type*} (C : Fin B → Matrix (Fin n) (Fin n) ℝ)
    (c : Fin B → ℝ) (z : QKInputs n d × Y) : Fin B → ℝ :=
  fun ℓ => c ℓ + scoreForm (C ℓ) z.1

/-- The summaries `S` numerically recover on `U` the affine score forms `c_ℓ + p_{C_ℓ}`, or
their coordinatewise exponentials. -/
def RecoversScores {n d B m : ℕ} {Y : Type*} (S : QKInputs n d × Y → Fin m → ℝ)
    (U : Set (QKInputs n d × Y)) (C : Fin B → Matrix (Fin n) (Fin n) ℝ) (c : Fin B → ℝ) : Prop :=
  NumericallyRecovers S U (affineScores C c) ∨
    NumericallyRecovers S U (fun z ℓ => Real.exp (affineScores C c z ℓ))

namespace Compression

variable {n d B m : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- If differentiable summaries decode the affine score forms on `U`, the Jacobian of
`(p_{C_ℓ})_ℓ` has rank at most `m` on the projection of `U` to the query and key inputs. -/
private lemma rank_le_of_decode (C : Fin B → Matrix (Fin n) (Fin n) ℝ) (c : Fin B → ℝ)
    {U : Set (QKInputs n d × Y)} (hU : IsOpen U) {S : QKInputs n d × Y → Fin m → ℝ}
    {Dec : (Fin m → ℝ) → Fin B → ℝ} (hS : DifferentiableOn ℝ S U)
    (hDec : ∀ z ∈ U, DifferentiableAt ℝ Dec (S z))
    (h : ∀ z ∈ U, Dec (S z) = affineScores C c z) :
    ∀ x ∈ Prod.fst '' U, finrank ℝ (LinearMap.range
      (fderiv ℝ (fun y (ℓ : Fin B) => scoreForm (C ℓ) y) x : QKInputs n d →ₗ[ℝ] (Fin B → ℝ))) ≤
        m := by
  rintro _ ⟨z, hz, rfl⟩
  have hfac := finrank_range_fderiv_le_of_eqOn_comp hU (F := affineScores C c) hS hDec
    (fun z hz => (h z hz).symm) hz
  have hF : HasFDerivAt (affineScores C c)
      ((LinearMap.toContinuousLinearMap (jac C z.1)).comp
        (ContinuousLinearMap.fst ℝ (QKInputs n d) Y)) z :=
    ((hasFDerivAt_scoreForms C z.1).comp z hasFDerivAt_fst).const_add c
  rw [hF.fderiv, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 Prod.fst_surjective),
    LinearMap.coe_toContinuousLinearMap] at hfac
  rw [finrank_range_fderiv_scoreForms]
  exact hfac

/-- A decoder for exponentials, followed by a coordinatewise logarithm, decodes the exponents. -/
private lemma log_decoder {X : Type*} {S : X → Fin m → ℝ} {Dec : (Fin m → ℝ) → Fin B → ℝ}
    {g : X → Fin B → ℝ} {U : Set X} (hDec : ∀ z ∈ U, DifferentiableAt ℝ Dec (S z))
    (h : ∀ z ∈ U, Dec (S z) = fun ℓ => Real.exp (g z ℓ)) :
    (∀ z ∈ U, DifferentiableAt ℝ (fun v ℓ => Real.log (Dec v ℓ)) (S z)) ∧
      ∀ z ∈ U, (fun v ℓ => Real.log (Dec v ℓ)) (S z) = g z := by
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · rw [differentiableAt_pi]
    intro ℓ
    refine (differentiableAt_pi.1 (hDec z hz) ℓ).log ?_
    rw [h z hz]
    exact (Real.exp_pos _).ne'
  · funext ℓ
    simp [h z hz]

/-- Recovery passes to a subfamily of the targets. -/
private lemma recovers_comp_index {X : Type*} {S : X → Fin m → ℝ} {U : Set X}
    {B' : ℕ} {f : X → Fin B → ℝ} (g : Fin B' → Fin B) (h : NumericallyRecovers S U f) :
    NumericallyRecovers S U (fun z ℓ => f z (g ℓ)) := by
  obtain ⟨W, Dec, hW, hSW, hDec, hDS⟩ := h
  refine ⟨W, fun v ℓ => Dec v (g ℓ), hW, hSW, ?_, fun z hz => by simp [hDS z hz]⟩
  exact contDiffOn_pi.2 fun ℓ => contDiffOn_pi.1 hDec (g ℓ)

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] in
private lemma recoversScores_comp_index {S : QKInputs n d × Y → Fin m → ℝ}
    {U : Set (QKInputs n d × Y)} {C : Fin B → Matrix (Fin n) (Fin n) ℝ} {c : Fin B → ℝ}
    {B' : ℕ} (g : Fin B' → Fin B) (h : RecoversScores S U C c) :
    RecoversScores S U (C ∘ g) (c ∘ g) := by
  rcases h with h | h
  · exact Or.inl (recovers_comp_index g h)
  · exact Or.inr (recovers_comp_index g h)

/-- The dimension of a finite sum of subspaces is at most the sum of their dimensions. -/
private lemma finrank_iSup_le_sum {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [Fintype ι] [DecidableEq ι] (p : ι → Submodule ℝ V) :
    finrank ℝ ↥(⨆ t, p t) ≤ ∑ t, finrank ℝ (p t) := by
  have key : ∀ s : Finset ι, finrank ℝ ↥(⨆ t ∈ s, p t) ≤ ∑ t ∈ s, finrank ℝ (p t) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.iSup_insert, Finset.sum_insert ha]
      exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (by omega)
  have huniv : (⨆ t ∈ (Finset.univ : Finset ι), p t) = ⨆ t, p t :=
    le_antisymm (iSup₂_le fun t _ => le_iSup p t)
      (iSup_le fun t => le_iSup₂_of_le t (Finset.mem_univ t) le_rfl)
  exact (Submodule.finrank_mono huniv.symm.le).trans (key Finset.univ)

end Compression

open Compression

/-- Numerical compression (`thm:compression`). Let `C_1, …, C_B` be linearly independent real
`n × n` matrices and `c ∈ ℝ^B`, with `d > 0`. Suppose `m` continuously differentiable real
summaries of the inputs `((Q, K), y)` numerically recover the affine score forms
`c_ℓ + p_{C_ℓ}(Q, K)`, or their coordinatewise exponentials, on a nonempty open set. Then
`B ≤ m + m² / (4 d²)`. The extra input `y` stands for `V` or any other coordinates the summaries
may read. -/
theorem compression {n d B m : ℕ} (hd : 0 < d) {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (C : Fin B → Matrix (Fin n) (Fin n) ℝ) (hC : LinearIndependent ℝ C)
    (c : Fin B → ℝ) {U : Set (QKInputs n d × Y)} (hU : IsOpen U) (hne : U.Nonempty)
    {S : QKInputs n d × Y → Fin m → ℝ} (hS : ContDiffOn ℝ 1 S U)
    (hrec : RecoversScores S U C c) :
    (B : ℝ) ≤ m + m ^ 2 / (4 * d ^ 2) := by
  have hSd : DifferentiableOn ℝ S U := hS.differentiableOn one_ne_zero
  have hopen : IsOpen (Prod.fst '' U) := isOpenMap_fst U hU
  have hne' : (Prod.fst '' U).Nonempty := hne.image _
  rcases hrec with ⟨W, Dec, hWo, hSW, hDec, hDS⟩ | ⟨W, Dec, hWo, hSW, hDec, hDS⟩
  all_goals
    have hDecd : ∀ z ∈ U, DifferentiableAt ℝ Dec (S z) := fun z hz =>
      (hDec.differentiableOn one_ne_zero).differentiableAt (hWo.mem_nhds (hSW ⟨z, hz, rfl⟩))
  · exact linearScore_rank_bound hd C hC hopen hne' (rank_le_of_decode C c hU hSd hDecd hDS)
  · obtain ⟨h1, h2⟩ := log_decoder (g := affineScores C c) hDecd hDS
    exact linearScore_rank_bound hd C hC hopen hne' (rank_le_of_decode C c hU hSd h1 h2)

/-- `thm:compression` for a family of coefficient matrices that need not be linearly
independent: the recovered coefficient space `span {C_ℓ}` has dimension at most
`m + m² / (4 d²)`. -/
theorem compression_finrank_span {n d B m : ℕ} (hd : 0 < d) {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (C : Fin B → Matrix (Fin n) (Fin n) ℝ) (c : Fin B → ℝ)
    {U : Set (QKInputs n d × Y)} (hU : IsOpen U) (hne : U.Nonempty)
    {S : QKInputs n d × Y → Fin m → ℝ} (hS : ContDiffOn ℝ 1 S U)
    (hrec : RecoversScores S U C c) :
    (finrank ℝ (Submodule.span ℝ (Set.range C)) : ℝ) ≤ m + m ^ 2 / (4 * d ^ 2) := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℝ C
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  set σ := Fintype.equivFin κ
  have hli' : LinearIndependent ℝ (C ∘ (a ∘ σ.symm)) := hli.comp σ.symm σ.symm.injective
  have hcard : finrank ℝ (Submodule.span ℝ (Set.range C)) = Fintype.card κ := by
    rw [← hspan, finrank_span_eq_card hli]
  rw [hcard]
  exact compression hd (C ∘ (a ∘ σ.symm)) hli' (c ∘ (a ∘ σ.symm)) hU hne hS
    (recoversScores_comp_index (a ∘ σ.symm) hrec)

/-- The per-epoch count in `cor:pair-cover`. If `2M` continuously differentiable summaries
recover affine score forms, or their exponentials, on a nonempty open set and `d² ≤ M`, then the
recovered coefficient space has dimension at most `2M + M² / d² ≤ 3M² / d²`. -/
theorem pairCover_epoch {n d M B : ℕ} (hd : 0 < d) (hM : d ^ 2 ≤ M) {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (C : Fin B → Matrix (Fin n) (Fin n) ℝ)
    (c : Fin B → ℝ) {U : Set (QKInputs n d × Y)} (hU : IsOpen U) (hne : U.Nonempty)
    {S : QKInputs n d × Y → Fin (2 * M) → ℝ} (hS : ContDiffOn ℝ 1 S U)
    (hrec : RecoversScores S U C c) :
    (finrank ℝ (Submodule.span ℝ (Set.range C)) : ℝ) ≤ 3 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2 := by
  have h := compression_finrank_span hd C c hU hne hS hrec
  have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  have hM' : (d : ℝ) ^ 2 ≤ M := by exact_mod_cast hM
  have h2M : ((2 * M : ℕ) : ℝ) + ((2 * M : ℕ) : ℝ) ^ 2 / (4 * (d : ℝ) ^ 2) =
      2 * M + (M : ℝ) ^ 2 / (d : ℝ) ^ 2 := by
    push_cast
    field_simp
    ring
  have hMd : (M : ℝ) ≤ (M : ℝ) ^ 2 / (d : ℝ) ^ 2 := by
    rw [le_div_iff₀ hd2]
    nlinarith
  have h3 : 3 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2 = 2 * ((M : ℝ) ^ 2 / (d : ℝ) ^ 2) +
      (M : ℝ) ^ 2 / (d : ℝ) ^ 2 := by ring
  rw [h2M] at h
  linarith

/-- The full bound under numerical span coverage (`cor:pair-cover`). Consider `e` epochs on a
common nonempty open input set. In epoch `t`, `2M` continuously differentiable summaries (the
incoming values) numerically recover affine score forms `c_{tℓ} + p_{C_{tℓ}}`, or their
exponentials. Suppose the coefficient matrices of all epochs span at least `n (n - 1)`
dimensions, `d ≥ 1`, and `d² ≤ M`. If `e ≤ I / M + 1` (`eq:epochs`) and the `I` transfers
include the `n d` output stores, then `I ≥ n (n - 1) d² / (3M) - M` (`eq:span-io`) and
`I ≥ (n d + n² d² / M) / 16`. -/
theorem pairCover {n d M e I : ℕ} (hd : 0 < d) (hM : d ^ 2 ≤ M) {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {U : Set (QKInputs n d × Y)} (hU : IsOpen U)
    (hne : U.Nonempty) {B : Fin e → ℕ} (C : ∀ t, Fin (B t) → Matrix (Fin n) (Fin n) ℝ)
    (c : ∀ t, Fin (B t) → ℝ) (S : Fin e → QKInputs n d × Y → Fin (2 * M) → ℝ)
    (hS : ∀ t, ContDiffOn ℝ 1 (S t) U) (hrec : ∀ t, RecoversScores (S t) U (C t) (c t))
    (hspan : n * (n - 1) ≤ finrank ℝ (Submodule.span ℝ (⋃ t, Set.range (C t))))
    (hepochs : (e : ℝ) ≤ I / M + 1) (hstores : n * d ≤ I) :
    (n : ℝ) * (n - 1) * (d : ℝ) ^ 2 / (3 * M) - M ≤ I ∧
      ((n : ℝ) * d + (n : ℝ) ^ 2 * (d : ℝ) ^ 2 / M) / 16 ≤ I := by
  classical
  have hsum : (finrank ℝ (Submodule.span ℝ (⋃ t, Set.range (C t))) : ℝ) ≤
      e * (3 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2) := by
    calc (finrank ℝ (Submodule.span ℝ (⋃ t, Set.range (C t))) : ℝ)
        ≤ ∑ t, (finrank ℝ (Submodule.span ℝ (Set.range (C t))) : ℝ) := by
          rw [Submodule.span_iUnion]
          exact_mod_cast finrank_iSup_le_sum _
      _ ≤ ∑ _t : Fin e, 3 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2 :=
          Finset.sum_le_sum fun t _ => pairCover_epoch hd hM (C t) (c t) hU hne (hS t) (hrec t)
      _ = e * (3 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2) := by simp
  have hn : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * (n - 1) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · push_cast [Nat.cast_sub hn]
      ring
  have hcov : (n : ℝ) * (n - 1) ≤ e * (3 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2) := by
    rw [← hn]
    exact (Nat.cast_le.2 hspan).trans hsum
  exact ⟨spanIO hd (lt_of_lt_of_le (pow_pos hd 2) hM) hcov hepochs,
    spanIO_bound hd hM hcov hepochs hstores⟩

/-- The coefficient matrix of the score `q_i · k_j` is the matrix unit `E_{ij}`. -/
theorem scoreForm_single {n d : ℕ} (i j : Fin n) (x : QKInputs n d) :
    scoreForm (Matrix.single i j 1) x = ∑ l, x.1 i l * x.2 j l := by
  simp [scoreForm, Matrix.single_apply, ite_and]

/-- The coverage condition of `cor:pair-cover` for ratios relative to a fixed key `o`, as in the
remark after that corollary. If the span of the recovered coefficient matrices contains the
coefficients `E_{ij} - E_{io}` of the centred scores `q_i · (k_j - k_o)` for all `i` and all
`j ≠ o`, it has dimension at least `n (n - 1)`. -/
theorem le_finrank_span_of_centred {n : ℕ} {s : Set (Matrix (Fin n) (Fin n) ℝ)} (o : Fin n)
    (h : ∀ i j, j ≠ o → Matrix.single i j 1 - Matrix.single i o 1 ∈ Submodule.span ℝ s) :
    n * (n - 1) ≤ finrank ℝ (Submodule.span ℝ s) := by
  classical
  let v : Fin n × {j : Fin n // j ≠ o} → Matrix (Fin n) (Fin n) ℝ :=
    fun p => Matrix.single p.1 p.2.1 1 - Matrix.single p.1 o 1
  have hv : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg p
    have h0 := congrFun (congrFun hg p.1) p.2.1
    have hne : o ≠ (p.2 : Fin n) := fun h => p.2.2 h.symm
    have heq : ∀ c : Fin n × {j : Fin n // j ≠ o}, (c.1 = p.1 ∧ (c.2 : Fin n) = p.2) ↔ c = p :=
      fun c => ⟨fun ⟨h1, h2⟩ => Prod.ext h1 (Subtype.ext h2), fun h => h ▸ ⟨rfl, rfl⟩⟩
    simp only [v, Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply,
      hne, and_false, ite_false, sub_zero, heq, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.zero_apply] at h0
    exact h0
  have hcard : Fintype.card (Fin n × {j : Fin n // j ≠ o}) = n * (n - 1) := by
    simp [Fintype.card_subtype_compl]
  calc n * (n - 1) = finrank ℝ (Submodule.span ℝ (Set.range v)) := by
        rw [finrank_span_eq_card hv, hcard]
    _ ≤ finrank ℝ (Submodule.span ℝ s) :=
        Submodule.finrank_mono (Submodule.span_le.2
          (Set.range_subset_iff.2 fun p => h p.1 p.2.1 p.2.2))

/-- The coverage condition of `cor:pair-cover` for all scores or all kernels: if the recovered
coefficient matrices include every matrix unit `E_{ij}`, they span at least `n (n - 1)`
dimensions. -/
theorem le_finrank_span_of_scores {n : ℕ} {s : Set (Matrix (Fin n) (Fin n) ℝ)}
    (h : ∀ i j, Matrix.single i j 1 ∈ s) :
    n * (n - 1) ≤ finrank ℝ (Submodule.span ℝ s) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact le_finrank_span_of_centred ⟨0, hn⟩ fun i j _ =>
      Submodule.sub_mem _ (Submodule.subset_span (h i j)) (Submodule.subset_span (h i _))

end ExactAttention
