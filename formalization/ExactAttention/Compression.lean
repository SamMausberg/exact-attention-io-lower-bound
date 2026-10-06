import ExactAttention.Factorization
import ExactAttention.PairRank

/-!
# Numerical compression of pair families

This file proves `thm:compression` and the counting in `cor:pair-cover`, both from
`app:recovery`.

Inputs are triples `(Q, K, V)` of `n × d` real matrices. A family is one of `q_i · k_j`,
`e^{q_i · k_j}`, or `e^{q_i · (k_j - k_o)}` for `j ≠ o`. The paper takes `o` to be the last key;
any fixed reference key is allowed here. Summaries `S` numerically recover a target `f` on `U`
(`NumericallyRecovers`) when a continuously differentiable decoder, defined on an open
neighbourhood of `S(U)`, sends `S x` to `f x` for every `x ∈ U`.

The proof follows the paper. Numerical factorisation (`lem:factor-rank`) bounds the rank of the
recovered vector by the number of summaries, and `lem:pair-rank` turns this into the bound on
`|E|`. For the two kernel families we compose the decoder with a coordinatewise logarithm, which
gives a decoder for the exponents; this undoes the invertible diagonal factor of the paper's
argument. The centred family uses the invertible change of key variables `k_j ↦ k_j - k_o`
(`j ≠ o`), and the open mapping theorem carries the open input set through it.

`pairCover` is the count behind `cor:pair-cover`. The execution model is not formalized. Each
epoch is represented by its incoming values, a `C¹` map into `ℝ^{2M}` on a common open input set,
and the relations `e ≤ I / M + 1` (`eq:epochs`) and `n d ≤ I` (the output stores) are
hypotheses.
-/

namespace ExactAttention

namespace Compression

open Finset Module PairRank

/-- Inputs `(Q, K, V)`, three `n × d` real matrices stored by rows. -/
abbrev Inputs (n d : ℕ) : Type :=
  (Fin n → Fin d → ℝ) × (Fin n → Fin d → ℝ) × (Fin n → Fin d → ℝ)

/-- The three pair families of `thm:compression`: scores `q_i · k_j`, kernels `e^{q_i · k_j}`,
and centred kernels `e^{q_i · (k_j - k_o)}` against a reference key `k_o`. The paper takes the
last key as reference. -/
inductive PairFamily (n : ℕ)
  | scores
  | kernels
  | centred (o : Fin n)

variable {n d : ℕ}

/-- The entry at the pair `(i, j)` of a family, as a function of the inputs `x = (Q, K, V)`. -/
noncomputable def PairFamily.entry : PairFamily n → Inputs n d → Fin n × Fin n → ℝ
  | .scores, x, p => ∑ a, x.1 p.1 a * x.2.1 p.2 a
  | .kernels, x, p => Real.exp (∑ a, x.1 p.1 a * x.2.1 p.2 a)
  | .centred o, x, p => Real.exp (∑ a, x.1 p.1 a * (x.2.1 p.2 a - x.2.1 o a))

/-- The index set of a full family: all pairs, except those with `j = o` in the centred family. -/
def PairFamily.pairs : PairFamily n → Finset (Fin n × Fin n)
  | .centred o => {p | p.2 ≠ o}
  | _ => univ

/-- The entries of a family selected by `E`. -/
noncomputable def PairFamily.select (F : PairFamily n) (E : Finset (Fin n × Fin n))
    (x : Inputs n d) : E → ℝ :=
  fun p => F.entry x p.1

/-- Summaries `S` numerically recover a target `f` on `U` when a continuously differentiable
decoder, defined on an open neighbourhood of `S(U)`, sends `S x` to `f x` for every `x ∈ U`. -/
def NumericallyRecovers {X Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {m : ℕ}
    (S : X → Fin m → ℝ) (U : Set X) (f : X → Y) : Prop :=
  ∃ W : Set (Fin m → ℝ), ∃ Dec : (Fin m → ℝ) → Y,
    IsOpen W ∧ S '' U ⊆ W ∧ ContDiffOn ℝ 1 Dec W ∧ ∀ x ∈ U, Dec (S x) = f x

/-- Key change of variables: `k_j ↦ k_j - k_o` for `j ≠ o`, and `k_o` unchanged. -/
private def centreKeys (o : Fin n) : (Fin n → Fin d → ℝ) →ₗ[ℝ] (Fin n → Fin d → ℝ) where
  toFun K j := if j = o then K o else K j - K o
  map_add' K K' := by
    funext j
    by_cases hj : j = o
    · simp [hj]
    · simp only [hj, ↓reduceIte, Pi.add_apply]
      abel
  map_smul' c K := by
    funext j
    by_cases hj : j = o
    · simp [hj]
    · simp [hj, smul_sub]

private lemma centreKeys_surjective (o : Fin n) :
    Function.Surjective (centreKeys (d := d) o) := by
  intro K'
  refine ⟨fun j => if j = o then K' o else K' j + K' o, ?_⟩
  funext j
  by_cases hj : j = o
  · subst hj
    simp [centreKeys]
  · simp [centreKeys, hj]

/-- The linear map from `(Q, K, V)` to the query and key variables seen by a family. -/
private noncomputable def inputMap : PairFamily n →
    Inputs n d →L[ℝ] (Fin n → Fin d → ℝ) × (Fin n → Fin d → ℝ)
  | .centred o => (ContinuousLinearMap.fst ℝ _ _).prod
      ((LinearMap.toContinuousLinearMap (centreKeys o)).comp
        ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))
  | _ => (ContinuousLinearMap.fst ℝ _ _).prod
      ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))

private lemma inputMap_surjective (F : PairFamily n) :
    Function.Surjective (inputMap (d := d) F) := by
  rintro ⟨Q, K'⟩
  cases F with
  | centred o =>
    obtain ⟨K, hK⟩ := centreKeys_surjective (d := d) o K'
    exact ⟨(Q, K, 0), by simp [inputMap, hK]⟩
  | scores => exact ⟨(Q, K', 0), rfl⟩
  | kernels => exact ⟨(Q, K', 0), rfl⟩

/-- The common core: if differentiable summaries recover the selected dot products of linearly
transformed inputs, where the linear map is onto, then `|E| ≤ m² / d² + 2m`. -/
private theorem card_le_of_recover_scores {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {m : ℕ} (hd : 0 < d) (E : Finset (ι × κ))
    (L : X →L[ℝ] (ι → Fin d → ℝ) × (κ → Fin d → ℝ)) (hL : Function.Surjective L)
    {U : Set X} (hU : IsOpen U) (hne : U.Nonempty) {S : X → Fin m → ℝ}
    {Dec : (Fin m → ℝ) → E → ℝ} (hS : DifferentiableOn ℝ S U)
    (hDec : ∀ x ∈ U, DifferentiableAt ℝ Dec (S x))
    (h : ∀ x ∈ U, Dec (S x) = scores E (L x)) :
    (#E : ℝ) ≤ (m : ℝ) ^ 2 / (d : ℝ) ^ 2 + 2 * m := by
  refine pairRank E hd (L.isOpenMap hL U hU) (hne.image L) ?_
  rintro _ ⟨x, hx, rfl⟩
  have hfac := finrank_range_fderiv_le_of_eqOn_comp hU (F := fun x => scores E (L x)) hS hDec
    (fun x hx => (h x hx).symm) hx
  have hcomp : fderiv ℝ (fun x => scores E (L x)) x = (fderiv ℝ (scores E) (L x)).comp L :=
    ((differentiable_scores E (L x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv
  rw [hcomp, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 hL)] at hfac
  exact hfac

/-- A decoder for exponentials, followed by a coordinatewise logarithm, decodes the exponents. -/
private lemma log_decoder {X P : Type*} [Fintype P] {m : ℕ} {S : X → Fin m → ℝ}
    {Dec : (Fin m → ℝ) → P → ℝ} {g : X → P → ℝ} {U : Set X}
    (hDec : ∀ x ∈ U, DifferentiableAt ℝ Dec (S x))
    (h : ∀ x ∈ U, Dec (S x) = fun p => Real.exp (g x p)) :
    (∀ x ∈ U, DifferentiableAt ℝ (fun y p => Real.log (Dec y p)) (S x)) ∧
      ∀ x ∈ U, (fun y p => Real.log (Dec y p)) (S x) = g x := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [differentiableAt_pi]
    intro p
    refine (differentiableAt_pi.1 (hDec x hx) p).log ?_
    rw [h x hx]
    exact (Real.exp_pos _).ne'
  · funext p
    simp [h x hx]

/-- A full family has at least `n (n - 1)` entries. -/
private lemma le_card_pairs (F : PairFamily n) : (n : ℝ) * (n - 1) ≤ #F.pairs := by
  cases F with
  | centred o =>
    have hn : 1 ≤ n := o.pos
    have : ({p | p.2 ≠ o} : Finset (Fin n × Fin n)) = univ ×ˢ ({o}ᶜ) := by
      ext p
      simp
    simp only [PairFamily.pairs, this, card_product, card_univ, Fintype.card_fin, card_compl,
      card_singleton]
    push_cast [Nat.cast_sub hn]
    exact le_rfl
  | scores =>
    simp only [PairFamily.pairs, card_univ, Fintype.card_prod, Fintype.card_fin]
    push_cast
    nlinarith
  | kernels =>
    simp only [PairFamily.pairs, card_univ, Fintype.card_prod, Fintype.card_fin]
    push_cast
    nlinarith

/-- The arithmetic at the end of `cor:pair-cover`. -/
private lemma pairCover_arith {N D M e I : ℝ} (hD : 1 ≤ D) (hM : D ^ 2 ≤ M) (hN : 0 ≤ N)
    (hN' : N ≤ 1 ∨ 2 ≤ N) (hcov : N * (N - 1) ≤ e * (8 * M ^ 2 / D ^ 2))
    (he : e ≤ I / M + 1) (hI : N * D ≤ I) :
    (N * D + N ^ 2 * D ^ 2 / M) / 32 ≤ I := by
  have hD0 : 0 < D := by linarith
  have hDM : D ≤ M := by nlinarith
  have hM0 : 0 < M := by linarith
  have hND : 0 ≤ N * D := by positivity
  have hA : N ^ 2 * D ^ 2 / M ≤ 31 * I := by
    rw [div_le_iff₀ hM0]
    rcases hN' with hN1 | hN2
    · have h1 : N * D ≤ M := by nlinarith
      nlinarith
    · have hcov' : N * (N - 1) * D ^ 2 ≤ 8 * (e * M ^ 2) := by
        have := mul_le_mul_of_nonneg_right hcov (sq_nonneg D)
        rwa [show e * (8 * M ^ 2 / D ^ 2) * D ^ 2 = 8 * (e * M ^ 2) by field_simp] at this
      have heM : e * M ^ 2 ≤ I * M + M ^ 2 := by
        have := mul_le_mul_of_nonneg_right he (sq_nonneg M)
        rwa [show (I / M + 1) * M ^ 2 = I * M + M ^ 2 by field_simp] at this
      have hsq : N ^ 2 * D ^ 2 ≤ 16 * (I * M) + 16 * M ^ 2 := by nlinarith
      rcases le_or_gt (8 * M) (N * D) with h8 | h8
      · nlinarith
      · nlinarith
  linarith

end Compression

open Finset Module PairRank Compression

variable {n d : ℕ}

/-- Numerical compression (`thm:compression`). Suppose `m` continuously differentiable real
summaries of the inputs `(Q, K, V)` numerically recover, on a nonempty open set, the entries at
the pairs `E` of one of the families `q_i · k_j`, `e^{q_i · k_j}`, `e^{q_i · (k_j - k_o)}`
(`j ≠ o`). Then `|E| ≤ m² / d² + 2m`. -/
theorem compression {m : ℕ} (hd : 0 < d) (F : PairFamily n) {E : Finset (Fin n × Fin n)}
    (hE : E ⊆ F.pairs) {U : Set (Inputs n d)} (hU : IsOpen U) (hne : U.Nonempty)
    {S : Inputs n d → Fin m → ℝ} (hS : ContDiffOn ℝ 1 S U)
    (hrec : NumericallyRecovers S U (F.select E)) :
    (#E : ℝ) ≤ (m : ℝ) ^ 2 / (d : ℝ) ^ 2 + 2 * m := by
  obtain ⟨W, Dec, hWo, hSW, hDec, hDS⟩ := hrec
  have hSd : DifferentiableOn ℝ S U := hS.differentiableOn one_ne_zero
  have hDecd : ∀ x ∈ U, DifferentiableAt ℝ Dec (S x) := fun x hx =>
    (hDec.differentiableOn one_ne_zero).differentiableAt (hWo.mem_nhds (hSW ⟨x, hx, rfl⟩))
  have hL := inputMap_surjective (d := d) F
  cases F with
  | scores =>
    refine card_le_of_recover_scores hd E _ hL hU hne hSd hDecd fun x hx => ?_
    rw [hDS x hx]
    rfl
  | kernels =>
    obtain ⟨h1, h2⟩ := log_decoder (g := fun x => scores E (inputMap .kernels x)) hDecd
      fun x hx => by rw [hDS x hx]; rfl
    exact card_le_of_recover_scores hd E _ hL hU hne hSd h1 h2
  | centred o =>
    obtain ⟨h1, h2⟩ := log_decoder (g := fun x => scores E (inputMap (.centred o) x)) hDecd
      fun x hx => by
        rw [hDS x hx]
        funext p
        have hp : p.1.2 ≠ o := by simpa [PairFamily.pairs] using hE p.2
        simp [PairFamily.select, PairFamily.entry, scores, inputMap, centreKeys, hp]
    exact card_le_of_recover_scores hd E _ hL hU hne hSd h1 h2

/-- The per-epoch count in `cor:pair-cover`. If `2M` continuously differentiable summaries
numerically recover the entries at the pairs `E` of one of the families of `thm:compression`,
and `d² ≤ M`, then `|E| ≤ 8M² / d²`. -/
theorem pairCover_epoch {M : ℕ} (hd : 0 < d) (hM : d ^ 2 ≤ M) (F : PairFamily n)
    {E : Finset (Fin n × Fin n)} (hE : E ⊆ F.pairs) {U : Set (Inputs n d)} (hU : IsOpen U)
    (hne : U.Nonempty) {S : Inputs n d → Fin (2 * M) → ℝ} (hS : ContDiffOn ℝ 1 S U)
    (hrec : NumericallyRecovers S U (F.select E)) :
    (#E : ℝ) ≤ 8 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2 := by
  have h := compression hd F hE hU hne hS hrec
  have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  have hM' : (d : ℝ) ^ 2 ≤ M := by exact_mod_cast hM
  have hMd : 4 * (M : ℝ) ≤ 4 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2 := by
    rw [le_div_iff₀ hd2]
    nlinarith
  push_cast at h
  have h8 : 8 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2 = 4 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2 +
      4 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2 := by ring
  calc (#E : ℝ) ≤ (2 * (M : ℝ)) ^ 2 / (d : ℝ) ^ 2 + 2 * (2 * M) := h
    _ = 4 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2 + 4 * M := by ring
    _ ≤ 8 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2 := by rw [h8]; linarith

/-- The full bound under pair coverage (`cor:pair-cover`). Consider `e` epochs on a common
nonempty open input set. In epoch `t`, `2M` continuously differentiable summaries (the incoming
values) numerically recover the entries at the pairs `E t` of one family, and together the epochs
cover the whole family. If `e ≤ I / M + 1` (`eq:epochs`) and the `I` transfers include the
`n d` output stores, then `I ≥ (n d + n² d² / M) / 32`. -/
theorem pairCover {M e I : ℕ} (hd : 0 < d) (hM : d ^ 2 ≤ M) (F : PairFamily n)
    {U : Set (Inputs n d)} (hU : IsOpen U) (hne : U.Nonempty)
    (E : Fin e → Finset (Fin n × Fin n)) (hEF : ∀ t, E t ⊆ F.pairs)
    (hcover : F.pairs ⊆ univ.biUnion E)
    (S : Fin e → Inputs n d → Fin (2 * M) → ℝ) (hS : ∀ t, ContDiffOn ℝ 1 (S t) U)
    (hrec : ∀ t, NumericallyRecovers (S t) U (F.select (E t)))
    (hepochs : (e : ℝ) ≤ I / M + 1) (hstores : n * d ≤ I) :
    ((n : ℝ) * d + (n : ℝ) ^ 2 * (d : ℝ) ^ 2 / M) / 32 ≤ I := by
  have hcard : (#F.pairs : ℝ) ≤ e * (8 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2) := by
    calc (#F.pairs : ℝ) ≤ ∑ t, (#(E t) : ℝ) := by
          exact_mod_cast (card_le_card hcover).trans card_biUnion_le
      _ ≤ ∑ _t : Fin e, 8 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2 :=
          sum_le_sum fun t _ => pairCover_epoch hd hM F (hEF t) hU hne (hS t) (hrec t)
      _ = e * (8 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2) := by simp
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  exact pairCover_arith hd1 (by exact_mod_cast hM) (Nat.cast_nonneg n)
    (by rcases Nat.lt_or_ge n 2 with h | h
        · left; exact_mod_cast Nat.lt_succ_iff.1 h
        · right; exact_mod_cast h)
    ((le_card_pairs F).trans hcard) hepochs (by exact_mod_cast hstores)

end ExactAttention
