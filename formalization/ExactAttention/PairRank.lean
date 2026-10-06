import ExactAttention.Defs

/-!
# Rank of a selected dot-product family

This file proves `lem:pair-rank` of `app:recovery`. Queries `q_i` (`i : ι`) and keys `k_j`
(`j : κ`) are vectors in `ℝ^d`, and `E` is a finite set of query-key pairs. Write
`r = ∑_i min(deg i, d)` and `c = ∑_j min(deg j, d)`.

* `pairRank_card_le_degree_sums`: `|E| ≤ r c / d² + r + c`.
* `pairRank_card_le_of_degree_sums_le`: `|E| ≤ ρ² / d² + 2ρ` whenever `r ≤ ρ` and `c ≤ ρ`.
* `pairRank_exists_dense_open`: on a dense open set of `(Q, K)`, the Jacobian of
  `(q_i · k_j)_{(i,j) ∈ E}` has rank at least `r` and at least `c`.
* `pairRank`: if that Jacobian has rank at most `ρ` on a nonempty open set, then
  `|E| ≤ ρ² / d² + 2ρ`.

The rank of a derivative is the dimension of its range. The paper puts the keys in general
position with Vandermonde vectors. Here each query `i` gets `min(deg i, d)` of its keys, and we
take the minor of those keys on the first `min(deg i, d)` coordinates. The product of these
minors is a nonzero polynomial in the keys, so it is nonzero on a dense open set, and there the
derivative in the query variables has rank at least `r`. The key side is symmetric, and both
bounds hold on the intersection of the two sets.
-/

namespace ExactAttention

namespace PairRank

open Finset Module

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The degree of the query `i` in the edge set `E`. -/
def qdeg (E : Finset (ι × κ)) (i : ι) : ℕ := #{e ∈ E | e.1 = i}

/-- The degree of the key `j` in the edge set `E`. -/
def kdeg (E : Finset (ι × κ)) (j : κ) : ℕ := #{e ∈ E | e.2 = j}

/-- `r = ∑_i min(deg i, d)`, summed over queries. -/
def qsum (E : Finset (ι × κ)) (d : ℕ) : ℕ := ∑ i, min (qdeg E i) d

/-- `c = ∑_j min(deg j, d)`, summed over keys. -/
def ksum (E : Finset (ι × κ)) (d : ℕ) : ℕ := ∑ j, min (kdeg E j) d

/-- Edges whose endpoint `f e` lies outside `H` number at most `∑_i min(deg i, d)` when every
vertex outside `H` has degree below `d`. -/
private lemma card_filter_not_mem_le {P α : Type*} [Fintype α] [DecidableEq α]
    (E : Finset P) (f : P → α) (d : ℕ) (H : Finset α)
    (hH : ∀ i ∉ H, #{e ∈ E | f e = i} < d) :
    #{e ∈ E | f e ∉ H} ≤ ∑ i, min #{e ∈ E | f e = i} d := by
  rw [card_eq_sum_card_fiberwise (f := f) (t := Hᶜ)
    (fun e he => by simpa using (mem_filter.1 he).2)]
  calc ∑ i ∈ Hᶜ, #{e ∈ {e ∈ E | f e ∉ H} | f e = i}
      = ∑ i ∈ Hᶜ, min #{e ∈ E | f e = i} d := by
        refine sum_congr rfl fun i hi => ?_
        have hi' : i ∉ H := by simpa using hi
        rw [min_eq_left (hH i hi').le, filter_filter]
        congr 1
        refine filter_congr fun e _ => ?_
        constructor
        · exact fun h => h.2
        · intro h; exact ⟨h ▸ hi', h⟩
    _ ≤ ∑ i, min #{e ∈ E | f e = i} d := sum_le_sum_of_subset (subset_univ _)

/-- At most `(∑_i min(deg i, d)) / d` vertices have degree at least `d`. -/
private lemma card_high_mul_le {P α : Type*} [Fintype α] [DecidableEq α]
    (E : Finset P) (f : P → α) (d : ℕ) :
    #{i | d ≤ #{e ∈ E | f e = i}} * d ≤ ∑ i, min #{e ∈ E | f e = i} d := by
  rw [← smul_eq_mul, ← sum_const]
  calc ∑ _i ∈ {i | d ≤ #{e ∈ E | f e = i}}, d
      = ∑ i ∈ {i | d ≤ #{e ∈ E | f e = i}}, min #{e ∈ E | f e = i} d := by
        refine sum_congr rfl fun i hi => ?_
        rw [min_eq_right (mem_filter.1 hi).2]
    _ ≤ ∑ i, min #{e ∈ E | f e = i} d := sum_le_sum_of_subset (subset_univ _)

private theorem card_le_qsum_mul_ksum (E : Finset (ι × κ)) {d : ℕ} (hd : 0 < d) :
    (#E : ℝ) ≤ (qsum E d : ℝ) * ksum E d / (d : ℝ) ^ 2 + qsum E d + ksum E d := by
  set H : Finset ι := {i | d ≤ qdeg E i}
  set Hk : Finset κ := {j | d ≤ kdeg E j}
  have hsplit : #E ≤ #H * #Hk + qsum E d + ksum E d := by
    have hsub : E ⊆ ({e ∈ E | e.1 ∈ H ∧ e.2 ∈ Hk} ∪ {e ∈ E | e.1 ∉ H}) ∪
        {e ∈ E | e.2 ∉ Hk} := by
      intro e he
      by_cases h1 : e.1 ∈ H <;> by_cases h2 : e.2 ∈ Hk <;> simp [he, h1, h2]
    have h1 : #{e ∈ E | e.1 ∈ H ∧ e.2 ∈ Hk} ≤ #H * #Hk := by
      rw [← card_product]
      exact card_le_card fun e he => by
        simp only [mem_filter] at he
        exact mem_product.2 he.2
    have h2 : #{e ∈ E | e.1 ∉ H} ≤ qsum E d :=
      card_filter_not_mem_le E Prod.fst d H fun i hi => by
        simp only [H, mem_filter, mem_univ, true_and, not_le] at hi
        exact hi
    have h3 : #{e ∈ E | e.2 ∉ Hk} ≤ ksum E d :=
      card_filter_not_mem_le E Prod.snd d Hk fun j hj => by
        simp only [Hk, mem_filter, mem_univ, true_and, not_le] at hj
        exact hj
    calc #E ≤ #(({e ∈ E | e.1 ∈ H ∧ e.2 ∈ Hk} ∪ {e ∈ E | e.1 ∉ H}) ∪ {e ∈ E | e.2 ∉ Hk}) :=
          card_le_card hsub
      _ ≤ #({e ∈ E | e.1 ∈ H ∧ e.2 ∈ Hk} ∪ {e ∈ E | e.1 ∉ H}) + #{e ∈ E | e.2 ∉ Hk} :=
          card_union_le _ _
      _ ≤ #{e ∈ E | e.1 ∈ H ∧ e.2 ∈ Hk} + #{e ∈ E | e.1 ∉ H} + #{e ∈ E | e.2 ∉ Hk} := by
          gcongr; exact card_union_le _ _
      _ ≤ #H * #Hk + qsum E d + ksum E d := by gcongr
  have hH : #H * d ≤ qsum E d := card_high_mul_le E Prod.fst d
  have hHk : #Hk * d ≤ ksum E d := card_high_mul_le E Prod.snd d
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hprod : (#H * #Hk : ℝ) ≤ (qsum E d : ℝ) * ksum E d / (d : ℝ) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have hH' : (#H : ℝ) * d ≤ qsum E d := by exact_mod_cast hH
    have hHk' : (#Hk : ℝ) * d ≤ ksum E d := by exact_mod_cast hHk
    calc (#H * #Hk : ℝ) * (d : ℝ) ^ 2 = ((#H : ℝ) * d) * ((#Hk : ℝ) * d) := by ring
      _ ≤ (qsum E d : ℝ) * ksum E d := by gcongr
  have hsplit' : (#E : ℝ) ≤ (#H * #Hk : ℝ) + qsum E d + ksum E d := by exact_mod_cast hsplit
  linarith

private theorem card_le_of_qsum_ksum_le (E : Finset (ι × κ)) {d : ℕ} (hd : 0 < d) {ρ : ℝ}
    (hr : (qsum E d : ℝ) ≤ ρ) (hc : (ksum E d : ℝ) ≤ ρ) :
    (#E : ℝ) ≤ ρ ^ 2 / (d : ℝ) ^ 2 + 2 * ρ := by
  have h := card_le_qsum_mul_ksum E hd
  have hrc : (qsum E d : ℝ) * ksum E d ≤ ρ ^ 2 := by
    rw [sq]; exact mul_le_mul hr hc (by positivity) ((Nat.cast_nonneg _).trans hr)
  have : (qsum E d : ℝ) * ksum E d / (d : ℝ) ^ 2 ≤ ρ ^ 2 / (d : ℝ) ^ 2 := by
    gcongr
  linarith

section Rank

variable {d : ℕ}

/-- The selected dot products `(q_i · k_j)_{(i,j) ∈ E}`, as a function of the query vectors
`x.1 i` and the key vectors `x.2 j` in `ℝ^d`. -/
def scores (E : Finset (ι × κ)) (x : (ι → Fin d → ℝ) × (κ → Fin d → ℝ)) : E → ℝ :=
  fun e => ∑ a, x.1 e.1.1 a * x.2 e.1.2 a

/-- The linear map `z ↦ (z_{π e} · v_e)_e`. With `π` the query endpoint and `v` the keys, it is
the derivative of the selected dot products in the query variables. -/
def blockMap {P α : Type*} (π : P → α) (v : P → Fin d → ℝ) :
    (α → Fin d → ℝ) →ₗ[ℝ] (P → ℝ) where
  toFun z e := ∑ a, z (π e) a * v e a
  map_add' z w := by ext e; simp [add_mul, sum_add_distrib]
  map_smul' c z := by ext e; simp [mul_sum, mul_assoc]

/-- Extension by zero from the first `t i` coordinates, block by block. -/
private def blockExt {α : Type*} (t : α → ℕ) (ht : ∀ i, t i ≤ d) :
    ((Σ i, Fin (t i)) → ℝ) →ₗ[ℝ] (α → Fin d → ℝ) where
  toFun w i a := ∑ b : Fin (t i), if a = Fin.castLE (ht i) b then w ⟨i, b⟩ else 0
  map_add' w w' := by
    funext i a
    simp only [Pi.add_apply, ← sum_add_distrib]
    exact sum_congr rfl fun b _ => by split_ifs <;> simp
  map_smul' c w := by
    funext i a
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    exact sum_congr rfl fun b _ => by split_ifs <;> simp

private lemma blockMap_blockExt {P α : Type*} (π : P → α) (v : P → Fin d → ℝ) (t : α → ℕ)
    (ht : ∀ i, t i ≤ d) (w : (Σ i, Fin (t i)) → ℝ) (e : P) (i : α) (he : π e = i) :
    blockMap π v (blockExt t ht w) e = ∑ b : Fin (t i), w ⟨i, b⟩ * v e (Fin.castLE (ht i) b) := by
  subst he
  simp only [blockMap, blockExt, LinearMap.coe_mk, AddHom.coe_mk, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun b _ => ?_
  simp [ite_mul]

/-- If each block has an invertible `t i × t i` minor, the block map has rank at least
`∑_i t i`. -/
private lemma le_finrank_range_blockMap {P α : Type*} [Fintype P] [Fintype α] (π : P → α)
    (v : P → Fin d → ℝ) (t : α → ℕ) (ht : ∀ i, t i ≤ d) (s : ∀ i, Fin (t i) → P)
    (hs : ∀ i b, π (s i b) = i)
    (hdet : ∀ i, (Matrix.of fun b a : Fin (t i) => v (s i b) (Fin.castLE (ht i) a)).det ≠ 0) :
    ∑ i, t i ≤ finrank ℝ (LinearMap.range (blockMap π v)) := by
  have hinj : Function.Injective (blockMap π v ∘ₗ blockExt t ht) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    funext ⟨i, b⟩
    have hmul : Matrix.mulVec (Matrix.of fun b a : Fin (t i) => v (s i b) (Fin.castLE (ht i) a))
        (fun b => w ⟨i, b⟩) = 0 := by
      funext b'
      have := congrFun hw (s i b')
      simp only [LinearMap.comp_apply, Pi.zero_apply] at this
      rw [blockMap_blockExt π v t ht w (s i b') i (hs i b')] at this
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
      rw [← this]
      exact sum_congr rfl fun a _ => mul_comm _ _
    exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero (hdet i) hmul) b
  calc ∑ i, t i = finrank ℝ ((Σ i, Fin (t i)) → ℝ) := by simp
    _ = finrank ℝ (LinearMap.range (blockMap π v ∘ₗ blockExt t ht)) :=
        (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ _ := Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)

private lemma exists_selection {P α : Type*} [Fintype P] [DecidableEq α] (π : P → α)
    (t : α → ℕ) (ht : ∀ i, t i ≤ #{e | π e = i}) :
    ∃ s : ∀ i, Fin (t i) → P, (∀ i, Function.Injective (s i)) ∧ ∀ i b, π (s i b) = i := by
  have h : ∀ i, Nonempty (Fin (t i) ↪ {e // π e = i}) := fun i =>
    Function.Embedding.nonempty_of_card_le (by simpa [Fintype.card_subtype] using ht i)
  exact ⟨fun i b => ((h i).some b).1,
    fun i b b' hbb' => (h i).some.injective (Subtype.ext hbb'), fun i b => ((h i).some b).2⟩

/-- The minor polynomial `det (X_{(σ (s b), a)})_{b, a < t}`. -/
private noncomputable def minorPoly {P β : Type*} (σ : P → β) {t : ℕ} (htd : t ≤ d)
    (s : Fin t → P) : MvPolynomial (β × Fin d) ℝ :=
  (Matrix.of fun b a : Fin t =>
    (MvPolynomial.X (σ (s b), Fin.castLE htd a) : MvPolynomial (β × Fin d) ℝ)).det

private lemma minorPoly_ne_zero {P β : Type*} (σ : P → β) {t : ℕ} (htd : t ≤ d)
    (s : Fin t → P) (hinj : Function.Injective (σ ∘ s)) : minorPoly σ htd s ≠ 0 := by
  set g : Fin t × Fin t → β × Fin d := fun p => (σ (s p.1), Fin.castLE htd p.2)
  have hg : Function.Injective g := by
    rintro ⟨b, a⟩ ⟨b', a'⟩ h
    simp only [g, Prod.mk.injEq] at h
    exact Prod.ext (hinj h.1) (Fin.castLE_injective htd h.2)
  have : minorPoly σ htd s = MvPolynomial.rename g (Matrix.mvPolynomialX (Fin t) (Fin t) ℝ).det := by
    rw [AlgHom.map_det]
    unfold minorPoly
    congr 1
    ext b a
    simp [Matrix.mvPolynomialX, g]
  rw [this]
  intro h0
  apply Matrix.det_mvPolynomialX_ne_zero (Fin t) ℝ
  exact MvPolynomial.rename_injective _ hg (by rw [h0, map_zero])

private lemma eval_minorPoly {P β : Type*} (σ : P → β) {t : ℕ} (htd : t ≤ d)
    (s : Fin t → P) (y : β → Fin d → ℝ) :
    MvPolynomial.eval (fun p => y p.1 p.2) (minorPoly σ htd s) =
      (Matrix.of fun b a : Fin t => y (σ (s b)) (Fin.castLE htd a)).det := by
  unfold minorPoly
  rw [RingHom.map_det]
  congr 1
  ext b a
  simp

/-- One side of the rank bound: off the zero set of a nonzero polynomial in the other group of
vectors, the block map has rank at least `∑_i t i`. -/
private lemma exists_poly_le_finrank {P α β : Type*} [Fintype P] [Fintype α] [DecidableEq α]
    (π : P → α) (σ : P → β) (hπσ : ∀ e e', π e = π e' → σ e = σ e' → e = e')
    (t : α → ℕ) (htd : ∀ i, t i ≤ d) (ht : ∀ i, t i ≤ #{e | π e = i}) :
    ∃ Pol : MvPolynomial (β × Fin d) ℝ, Pol ≠ 0 ∧ ∀ y : β → Fin d → ℝ,
      MvPolynomial.eval (fun p => y p.1 p.2) Pol ≠ 0 →
      ∑ i, t i ≤ finrank ℝ (LinearMap.range (blockMap π (fun e => y (σ e)))) := by
  obtain ⟨s, hsinj, hs⟩ := exists_selection π t ht
  refine ⟨∏ i, minorPoly σ (htd i) (s i), ?_, fun y hy => ?_⟩
  · rw [prod_ne_zero_iff]
    intro i _
    apply minorPoly_ne_zero
    intro b b' h
    exact hsinj i (hπσ _ _ (by rw [hs, hs]) h)
  · rw [map_prod, prod_ne_zero_iff] at hy
    refine le_finrank_range_blockMap π _ t htd s hs fun i => ?_
    rw [← eval_minorPoly]
    exact hy i (mem_univ _)

private lemma exists_mem_eval_ne_zero {α : Type*} [Fintype α] {Pol : MvPolynomial (α × Fin d) ℝ}
    (hP : Pol ≠ 0) {W : Set (α → Fin d → ℝ)} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ y ∈ W, MvPolynomial.eval (fun p => y p.1 p.2) Pol ≠ 0 := by
  by_contra h
  push Not at h
  apply hP
  refine mvPolynomial_eq_zero_of_isOpen (U := {z : α × Fin d → ℝ | (fun i a => z (i, a)) ∈ W})
    (hW.preimage (by fun_prop)) ?_ fun z hz => h _ hz
  obtain ⟨y, hy⟩ := hne
  exact ⟨fun p => y p.1 p.2, hy⟩

omit [DecidableEq ι] [DecidableEq κ] in
/-- The selected dot products are differentiable in `(Q, K)`. -/
lemma differentiable_scores (E : Finset (ι × κ)) : Differentiable ℝ (scores (d := d) E) := by
  intro x
  rw [differentiableAt_pi]
  intro e
  unfold scores
  fun_prop

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
private lemma card_subtype_fst (E : Finset (ι × κ)) (i : ι) :
    #{e : E | e.1.1 = i} = qdeg E i := by
  unfold qdeg
  rw [← card_map (Function.Embedding.subtype _)]
  congr 1
  ext p
  simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e.2, he⟩
  · rintro ⟨hp, he⟩
    exact ⟨⟨p, hp⟩, he, rfl⟩

omit [Fintype ι] [Fintype κ] [DecidableEq ι] in
private lemma card_subtype_snd (E : Finset (ι × κ)) (j : κ) :
    #{e : E | e.1.2 = j} = kdeg E j := by
  unfold kdeg
  rw [← card_map (Function.Embedding.subtype _)]
  congr 1
  ext p
  simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e.2, he⟩
  · rintro ⟨hp, he⟩
    exact ⟨⟨p, hp⟩, he, rfl⟩

omit [DecidableEq ι] [DecidableEq κ] in
/-- The derivative of the selected dot products in the query variables is the block map built
from the keys. -/
private lemma fderiv_scores_comp_inl (E : Finset (ι × κ)) (Q : ι → Fin d → ℝ)
    (K : κ → Fin d → ℝ) :
    (fderiv ℝ (scores E) (Q, K)).comp (ContinuousLinearMap.inl ℝ _ _) =
      LinearMap.toContinuousLinearMap (blockMap (fun e : E => e.1.1) (fun e => K e.1.2)) := by
  have h1 : HasFDerivAt (fun Q' => scores E (Q', K))
      ((fderiv ℝ (scores E) (Q, K)).comp (ContinuousLinearMap.inl ℝ _ _)) Q :=
    (differentiable_scores E _).hasFDerivAt.comp Q (hasFDerivAt_prodMk_left Q K)
  have hfun : (fun Q' => scores E (Q', K)) =
      LinearMap.toContinuousLinearMap (blockMap (fun e : E => e.1.1) (fun e => K e.1.2)) := by
    funext Q' e
    rfl
  have h2 : HasFDerivAt (fun Q' => scores E (Q', K))
      (LinearMap.toContinuousLinearMap (blockMap (fun e : E => e.1.1) (fun e => K e.1.2))) Q := by
    rw [hfun]
    exact (LinearMap.toContinuousLinearMap _).hasFDerivAt
  exact h1.unique h2

omit [DecidableEq ι] [DecidableEq κ] in
/-- The derivative of the selected dot products in the key variables is the block map built
from the queries. -/
private lemma fderiv_scores_comp_inr (E : Finset (ι × κ)) (Q : ι → Fin d → ℝ)
    (K : κ → Fin d → ℝ) :
    (fderiv ℝ (scores E) (Q, K)).comp (ContinuousLinearMap.inr ℝ _ _) =
      LinearMap.toContinuousLinearMap (blockMap (fun e : E => e.1.2) (fun e => Q e.1.1)) := by
  have h1 : HasFDerivAt (fun K' => scores E (Q, K'))
      ((fderiv ℝ (scores E) (Q, K)).comp (ContinuousLinearMap.inr ℝ _ _)) K :=
    (differentiable_scores E _).hasFDerivAt.comp K (hasFDerivAt_prodMk_right Q K)
  have hfun : (fun K' => scores E (Q, K')) =
      LinearMap.toContinuousLinearMap (blockMap (fun e : E => e.1.2) (fun e => Q e.1.1)) := by
    funext K' e
    simp only [scores, LinearMap.coe_toContinuousLinearMap', blockMap, LinearMap.coe_mk,
      AddHom.coe_mk]
    exact sum_congr rfl fun a _ => mul_comm _ _
  have h2 : HasFDerivAt (fun K' => scores E (Q, K'))
      (LinearMap.toContinuousLinearMap (blockMap (fun e : E => e.1.2) (fun e => Q e.1.1))) K := by
    rw [hfun]
    exact (LinearMap.toContinuousLinearMap _).hasFDerivAt
  exact h1.unique h2

end Rank

end PairRank

open Finset Module PairRank

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The counting step of `lem:pair-rank`. For a bipartite edge set `E` between queries and keys,
put `r = ∑_i min(deg i, d)` over queries and `c = ∑_j min(deg j, d)` over keys. Then
`|E| ≤ r c / d² + r + c`. -/
theorem pairRank_card_le_degree_sums (E : Finset (ι × κ)) {d : ℕ} (hd : 0 < d) :
    (#E : ℝ) ≤ (qsum E d : ℝ) * ksum E d / (d : ℝ) ^ 2 + qsum E d + ksum E d :=
  card_le_qsum_mul_ksum E hd

/-- The counting step of `lem:pair-rank`, second form: if `ρ` bounds both degree sums
`r = ∑_i min(deg i, d)` and `c = ∑_j min(deg j, d)`, then `|E| ≤ ρ² / d² + 2ρ`. -/
theorem pairRank_card_le_of_degree_sums_le (E : Finset (ι × κ)) {d : ℕ} (hd : 0 < d) {ρ : ℝ}
    (hr : (qsum E d : ℝ) ≤ ρ) (hc : (ksum E d : ℝ) ≤ ρ) :
    (#E : ℝ) ≤ ρ ^ 2 / (d : ℝ) ^ 2 + 2 * ρ :=
  card_le_of_qsum_ksum_le E hd hr hc

/-- The rank step of `lem:pair-rank`. There is a dense open set of query and key vectors at
which the Jacobian of `(q_i · k_j)_{(i,j) ∈ E}` with respect to `(Q, K)` has rank at least
`r = ∑_i min(deg i, d)` and at least `c = ∑_j min(deg j, d)`. -/
theorem pairRank_exists_dense_open (E : Finset (ι × κ)) (d : ℕ) :
    ∃ G : Set ((ι → Fin d → ℝ) × (κ → Fin d → ℝ)), IsOpen G ∧ Dense G ∧ ∀ x ∈ G,
      qsum E d ≤ finrank ℝ (LinearMap.range (fderiv ℝ (scores E) x :
        (ι → Fin d → ℝ) × (κ → Fin d → ℝ) →ₗ[ℝ] E → ℝ)) ∧
      ksum E d ≤ finrank ℝ (LinearMap.range (fderiv ℝ (scores E) x :
        (ι → Fin d → ℝ) × (κ → Fin d → ℝ) →ₗ[ℝ] E → ℝ)) := by
  obtain ⟨PK, hPK, hK⟩ := exists_poly_le_finrank (d := d) (P := E) (fun e => e.1.1)
    (fun e => e.1.2) (fun e e' h1 h2 => Subtype.ext (Prod.ext h1 h2))
    (fun i => min (qdeg E i) d) (fun i => min_le_right _ _)
    (fun i => (min_le_left _ _).trans (card_subtype_fst E i).ge)
  obtain ⟨PQ, hPQ, hQ⟩ := exists_poly_le_finrank (d := d) (P := E) (fun e => e.1.2)
    (fun e => e.1.1) (fun e e' h1 h2 => Subtype.ext (Prod.ext h2 h1))
    (fun j => min (kdeg E j) d) (fun j => min_le_right _ _)
    (fun j => (min_le_left _ _).trans (card_subtype_snd E j).ge)
  refine ⟨{x | MvPolynomial.eval (fun p => x.2 p.1 p.2) PK ≠ 0 ∧
      MvPolynomial.eval (fun p => x.1 p.1 p.2) PQ ≠ 0}, ?_, ?_, ?_⟩
  · exact (isOpen_ne_fun ((MvPolynomial.continuous_eval PK).comp (by fun_prop))
      continuous_const).inter
      (isOpen_ne_fun ((MvPolynomial.continuous_eval PQ).comp (by fun_prop)) continuous_const)
  · rw [dense_iff_inter_open]
    rintro W hW ⟨⟨Q₀, K₀⟩, h₀⟩
    obtain ⟨Q, hQW, hQne⟩ := exists_mem_eval_ne_zero hPQ (W := {Q | (Q, K₀) ∈ W})
      (hW.preimage (by fun_prop)) ⟨Q₀, h₀⟩
    obtain ⟨K, hKW, hKne⟩ := exists_mem_eval_ne_zero hPK (W := {K | (Q, K) ∈ W})
      (hW.preimage (by fun_prop)) ⟨K₀, hQW⟩
    exact ⟨(Q, K), hKW, hKne, hQne⟩
  · rintro ⟨Q, K⟩ ⟨h1, h2⟩
    constructor
    · calc qsum E d = ∑ i, min (qdeg E i) d := rfl
        _ ≤ finrank ℝ (LinearMap.range (blockMap (fun e : E => e.1.1) (fun e => K e.1.2))) :=
          hK K h1
        _ = finrank ℝ (LinearMap.range
              (((fderiv ℝ (scores E) (Q, K)).comp (ContinuousLinearMap.inl ℝ _ _) :
                (ι → Fin d → ℝ) →L[ℝ] E → ℝ) : (ι → Fin d → ℝ) →ₗ[ℝ] E → ℝ)) := by
          rw [fderiv_scores_comp_inl, LinearMap.coe_toContinuousLinearMap]
        _ ≤ _ := by
          rw [ContinuousLinearMap.toLinearMap_comp]
          exact Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
    · calc ksum E d = ∑ j, min (kdeg E j) d := rfl
        _ ≤ finrank ℝ (LinearMap.range (blockMap (fun e : E => e.1.2) (fun e => Q e.1.1))) :=
          hQ Q h2
        _ = finrank ℝ (LinearMap.range
              (((fderiv ℝ (scores E) (Q, K)).comp (ContinuousLinearMap.inr ℝ _ _) :
                (κ → Fin d → ℝ) →L[ℝ] E → ℝ) : (κ → Fin d → ℝ) →ₗ[ℝ] E → ℝ)) := by
          rw [fderiv_scores_comp_inr, LinearMap.coe_toContinuousLinearMap]
        _ ≤ _ := by
          rw [ContinuousLinearMap.toLinearMap_comp]
          exact Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)

/-- Rank of a selected dot-product family (`lem:pair-rank`). If the Jacobian of
`(q_i · k_j)_{(i,j) ∈ E}` has rank at most `ρ` at every point of a nonempty open set, then
`|E| ≤ ρ² / d² + 2ρ`. The generic Jacobian rank is the largest rank attained, so the statement
in the paper follows by taking `ρ` to be that rank. -/
theorem pairRank (E : Finset (ι × κ)) {d : ℕ} (hd : 0 < d)
    {W : Set ((ι → Fin d → ℝ) × (κ → Fin d → ℝ))} (hW : IsOpen W) (hne : W.Nonempty) {ρ : ℕ}
    (hρ : ∀ x ∈ W, finrank ℝ (LinearMap.range (fderiv ℝ (scores E) x :
        (ι → Fin d → ℝ) × (κ → Fin d → ℝ) →ₗ[ℝ] E → ℝ)) ≤ ρ) :
    (#E : ℝ) ≤ (ρ : ℝ) ^ 2 / (d : ℝ) ^ 2 + 2 * ρ := by
  obtain ⟨G, hGo, hGd, hG⟩ := pairRank_exists_dense_open E d
  obtain ⟨x, hxW, hxG⟩ := hGd.inter_open_nonempty W hW hne
  obtain ⟨hr, hc⟩ := hG x hxG
  exact card_le_of_qsum_ksum_le E hd (by exact_mod_cast hr.trans (hρ x hxW))
    (by exact_mod_cast hc.trans (hρ x hxW))

end ExactAttention
