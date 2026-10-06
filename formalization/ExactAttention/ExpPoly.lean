import ExactAttention.Defs

/-!
# Exponentials of polynomials

This file proves `lem:independence`. Let `p₁, …, pₛ` be real polynomials in finitely many
variables such that every nonzero integer combination of them is nonconstant. Then no nonzero
polynomial in `e^{p₁}, …, e^{pₛ}` whose coefficients are polynomials in the variables vanishes on
a nonempty open set.

The lemma in the paper is stated over the field of rational functions. A relation with rational
coefficients becomes one with polynomial coefficients after multiplying by a common denominator,
and a nonzero rational function cannot vanish identically on an open set, so the statement with
polynomial coefficients is the substance of the lemma. We also record the equivalent form in
terms of `AlgebraicIndependent`: on a nonempty open set `U`, the coordinate functions together
with the functions `e^{pⱼ}` are algebraically independent over `ℝ` in the ring `U → ℝ`.

The proof follows the paper. The relation is an analytic function on all of `ℝ^N`, so it vanishes
everywhere. Restricting to a generic line `u ↦ u • z` gives a one-variable relation
`∑ₐ rₐ(u) e^{Qₐ(u)} = 0` with nonzero polynomials `rₐ` and pairwise nonconstant differences
`Qₐ - Q_b`. Dividing by the eventually largest exponential and letting `u → ∞` kills the
coefficient of that exponential, and induction removes the others.
-/

open MvPolynomial Filter Topology Asymptotics

namespace ExactAttention

namespace ExpPoly

/-! ### The one-variable statement -/

/-- A polynomial times `e^{-q}` tends to zero when the polynomial `q` tends to `+∞`. -/
theorem tendsto_eval_mul_exp_neg (r q : Polynomial ℝ)
    (hq : Tendsto (fun u => q.eval u) atTop atTop) :
    Tendsto (fun u => r.eval u * Real.exp (-q.eval u)) atTop (𝓝 0) := by
  have hdeg : 0 < q.degree :=
    (Polynomial.abs_tendsto_atTop_iff q).mp (tendsto_abs_atTop_atTop.comp hq)
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hnat : 1 ≤ q.natDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr hdeg
  set k := r.natDegree
  have hO : (fun u => r.eval u) =O[atTop] (fun u => (q ^ k).eval u) := by
    apply Polynomial.isBigO_atTop_of_degree_le
    rw [Polynomial.degree_eq_natDegree (pow_ne_zero _ hq0), Polynomial.natDegree_pow]
    refine (Polynomial.degree_le_natDegree).trans ?_
    exact_mod_cast Nat.le_mul_of_pos_right k hnat
  have hlim : Tendsto (fun u => (q ^ k).eval u * Real.exp (-q.eval u)) atTop (𝓝 0) := by
    simp only [Polynomial.eval_pow]
    exact (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp hq
  exact (hO.mul (isBigO_refl (fun u => Real.exp (-q.eval u)) atTop)).trans_tendsto hlim

/-- If `Q₁ - Q₂` has positive degree, one of the two differences tends to `+∞`. -/
theorem tendsto_sub_or_tendsto_sub (Q₁ Q₂ : Polynomial ℝ) (h : 0 < (Q₁ - Q₂).degree) :
    Tendsto (fun u => (Q₁ - Q₂).eval u) atTop atTop ∨
      Tendsto (fun u => (Q₂ - Q₁).eval u) atTop atTop := by
  rcases le_or_gt 0 (Q₁ - Q₂).leadingCoeff with hc | hc
  · exact Or.inl (Polynomial.tendsto_atTop_of_leadingCoeff_nonneg _ h hc)
  · right
    have := Polynomial.tendsto_atBot_of_leadingCoeff_nonpos _ h hc.le
    refine (tendsto_neg_atBot_atTop.comp this).congr fun u => ?_
    simp

/-- Among finitely many polynomials with nonconstant pairwise differences there is one that
eventually exceeds all the others by an amount tending to `+∞`. -/
theorem exists_top {α : Type*} [DecidableEq α] (Q : α → Polynomial ℝ) (S : Finset α)
    (hS : S.Nonempty) (hQ : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 0 < (Q a - Q b).degree) :
    ∃ a₀ ∈ S, ∀ b ∈ S, b ≠ a₀ → Tendsto (fun u => (Q a₀ - Q b).eval u) atTop atTop := by
  induction S using Finset.induction_on with
  | empty => simp at hS
  | insert c S hc ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS'
    · refine ⟨c, by simp, fun b hb hbc => ?_⟩
      simp only [insert_empty_eq, Finset.mem_singleton] at hb
      exact absurd hb hbc
    obtain ⟨a₀, ha₀, htop⟩ := ih hS' fun a ha b hb hab =>
      hQ a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
    have hca : c ≠ a₀ := fun h => hc (h ▸ ha₀)
    rcases tendsto_sub_or_tendsto_sub _ _
        (hQ c (Finset.mem_insert_self _ _) a₀ (Finset.mem_insert_of_mem ha₀) hca) with h | h
    · refine ⟨c, Finset.mem_insert_self _ _, fun b hb hbc => ?_⟩
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact absurd rfl hbc
      by_cases hba : b = a₀
      · subst hba
        exact h
      · refine (h.atTop_add_atTop (htop b hb hba)).congr fun u => ?_
        simp
    · refine ⟨a₀, Finset.mem_insert_of_mem ha₀, fun b hb hba => ?_⟩
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact h
      · exact htop b hb hba

/-- The one-variable form of `lem:independence`: if the exponents `Q a` have pairwise
nonconstant differences and `∑ₐ rₐ(u) e^{Qₐ(u)}` vanishes for all large `u`, then every
coefficient polynomial `rₐ` is zero. -/
theorem coeff_eq_zero_of_eventually_sum_mul_exp {α : Type*} [DecidableEq α]
    (r Q : α → Polynomial ℝ) (S : Finset α)
    (hQ : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 0 < (Q a - Q b).degree)
    (hsum : ∀ᶠ u in atTop, ∑ a ∈ S, (r a).eval u * Real.exp ((Q a).eval u) = 0) :
    ∀ a ∈ S, r a = 0 := by
  induction S using Finset.strongInduction with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simp
    obtain ⟨a₀, ha₀, htop⟩ := exists_top Q S hS hQ
    -- The coefficient of the largest exponential tends to zero, hence vanishes.
    have hr₀ : r a₀ = 0 := by
      have hlim : Tendsto (fun u => -∑ b ∈ S.erase a₀,
          (r b).eval u * Real.exp (-(Q a₀ - Q b).eval u)) atTop (𝓝 0) := by
        rw [← neg_zero]
        refine Tendsto.neg ?_
        rw [← Finset.sum_const_zero (s := S.erase a₀)]
        refine tendsto_finsetSum _ fun b hb => ?_
        exact tendsto_eval_mul_exp_neg _ _ (htop b (Finset.mem_of_mem_erase hb)
          (Finset.ne_of_mem_erase hb))
      have heq : (fun u => -∑ b ∈ S.erase a₀,
          (r b).eval u * Real.exp (-(Q a₀ - Q b).eval u)) =ᶠ[atTop] fun u => (r a₀).eval u := by
        filter_upwards [hsum] with u hu
        rw [← Finset.add_sum_erase _ _ ha₀] at hu
        have hu' := congrArg (· * Real.exp (-(Q a₀).eval u)) hu
        simp only [zero_mul, add_mul, Finset.sum_mul, mul_assoc, ← Real.exp_add,
          add_neg_cancel, Real.exp_zero, mul_one] at hu'
        rw [neg_eq_iff_add_eq_zero, add_comm, ← hu']
        congr 1
        refine Finset.sum_congr rfl fun b _ => ?_
        congr 2
        simp only [Polynomial.eval_sub]
        ring
      have := (Polynomial.tendsto_nhds_iff (r a₀)).mp (hlim.congr' heq)
      exact Polynomial.leadingCoeff_eq_zero.mp this.1
    -- Remove that term and apply the induction hypothesis to the rest.
    have hrest : ∀ a ∈ S.erase a₀, r a = 0 := by
      refine ih (S.erase a₀) (Finset.erase_ssubset ha₀) (fun a ha b hb hab =>
        hQ a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab) ?_
      filter_upwards [hsum] with u hu
      rw [← Finset.add_sum_erase _ _ ha₀, hr₀] at hu
      simpa using hu
    intro a ha
    by_cases h : a = a₀
    · rw [h, hr₀]
    · exact hrest a (Finset.mem_erase.mpr ⟨h, ha⟩)

/-! ### Restriction to a line -/

/-- Restriction of a polynomial in several variables to the line `u ↦ u • z`. -/
noncomputable def line {σ : Type*} (z : σ → ℝ) : MvPolynomial σ ℝ →ₐ[ℝ] Polynomial ℝ :=
  aeval fun i => Polynomial.C (z i) * Polynomial.X

theorem eval_line {σ : Type*} (z : σ → ℝ) (f : MvPolynomial σ ℝ) (u : ℝ) :
    (line z f).eval u = eval (u • z) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [line]
  | add f g hf hg => simp [hf, hg]
  | mul_X f i hf =>
    rw [map_mul, Polynomial.eval_mul, hf]
    simp only [line, aeval_X, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, eval_mul,
      eval_X, Pi.smul_apply, smul_eq_mul]
    ring

/-! ### The relation as a sum of exponentials -/

/-- The exponent `∑ⱼ aⱼ pⱼ` attached to a monomial `a`. -/
noncomputable def expo {ι σ : Type*} [Fintype ι] (p : ι → MvPolynomial σ ℝ) (a : ι →₀ ℕ) :
    MvPolynomial σ ℝ :=
  ∑ j, (a j : ℝ) • p j

theorem eval_relation {ι σ : Type*} [Fintype ι] (p : ι → MvPolynomial σ ℝ)
    (P : MvPolynomial ι (MvPolynomial σ ℝ)) (x : σ → ℝ) :
    MvPolynomial.eval (fun j => Real.exp (MvPolynomial.eval x (p j)))
        (MvPolynomial.map (MvPolynomial.eval x) P) =
      ∑ a ∈ P.support, eval x (P.coeff a) * Real.exp (eval x (expo p a)) := by
  rw [eval_map, eval₂_eq']
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  simp only [expo, map_sum, smul_eval, Real.exp_sum, ← Real.exp_nat_mul]

/-- Distinct monomials have exponents whose difference is not constant. -/
theorem expo_sub_ne_C {ι σ : Type*} [Fintype ι] (p : ι → MvPolynomial σ ℝ)
    (hp : IntCombNonconst p) {a b : ι →₀ ℕ} (hab : a ≠ b) (c : ℝ) :
    expo p a - expo p b ≠ C c := by
  have hc : (fun j => (a j : ℤ) - (b j : ℤ)) ≠ 0 := by
    intro h
    apply hab
    ext j
    have := congrFun h j
    simp only [Pi.zero_apply, sub_eq_zero, Nat.cast_inj] at this
    exact this
  have := hp _ hc c
  convert this using 1
  simp only [expo, ← Finset.sum_sub_distrib, ← sub_smul]
  push_cast
  rfl

end ExpPoly

open ExpPoly

/-- `lem:independence` (Exponentials of polynomials), in the form with polynomial coefficients.
If every nonzero integer combination of the polynomials `p j` is nonconstant and a polynomial
`P` in the `e^{p j}`, with coefficients polynomial in `x`, vanishes on a nonempty open set `U`,
then `P = 0`. -/
theorem exp_poly_relation_eq_zero {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]
    (p : ι → MvPolynomial σ ℝ) (hp : IntCombNonconst p)
    {U : Set (σ → ℝ)} (hU : IsOpen U) (hne : U.Nonempty)
    (P : MvPolynomial ι (MvPolynomial σ ℝ))
    (hP : ∀ x ∈ U, MvPolynomial.eval (fun j => Real.exp (MvPolynomial.eval x (p j)))
        (MvPolynomial.map (MvPolynomial.eval x) P) = 0) :
    P = 0 := by
  classical
  set S := P.support
  set F : (σ → ℝ) → ℝ := fun x => ∑ a ∈ S, eval x (P.coeff a) * Real.exp (eval x (expo p a))
  -- The relation is analytic on all of `ℝ^σ`, so it vanishes everywhere.
  have hF : AnalyticOnNhd ℝ F Set.univ := by
    refine Finset.analyticOnNhd_fun_sum _ fun a _ => ?_
    exact (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℝ) (P.coeff a)).mul
      (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℝ) (expo p a)).rexp
  have hall : ∀ x, F x = 0 := by
    obtain ⟨x₀, hx₀⟩ := hne
    have h₀ : F =ᶠ[𝓝 x₀] 0 := by
      filter_upwards [hU.mem_nhds hx₀] with x hx
      rw [Pi.zero_apply, ← hP x hx, eval_relation]
    intro x
    exact hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ x₀) h₀ (Set.mem_univ x)
  by_contra hP0
  obtain ⟨a₁, ha₁⟩ : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    simpa [S] using hP0
  -- A point `z` at which all coefficients and all nonconstant differences are generic.
  set G : MvPolynomial σ ℝ := (∏ a ∈ S, P.coeff a) *
    ∏ ab ∈ S.offDiag, (expo p ab.1 - expo p ab.2 - C (eval 0 (expo p ab.1 - expo p ab.2)))
  have hG : G ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun a ha => mem_support_iff.mp ha)
      (Finset.prod_ne_zero_iff.mpr fun ab hab => ?_)
    rw [Finset.mem_offDiag] at hab
    exact sub_ne_zero.mpr (expo_sub_ne_C p hp hab.2.2 _)
  obtain ⟨z, hz⟩ : ∃ z, eval z G ≠ 0 := by
    by_contra! h
    exact hG (MvPolynomial.funext fun x => by simp [h x])
  simp only [G, map_mul, map_prod, mul_ne_zero_iff, Finset.prod_ne_zero_iff] at hz
  obtain ⟨hzr, hzQ⟩ := hz
  -- The restricted one-variable relation.
  have hQ : ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      0 < (line z (expo p a) - line z (expo p b)).degree := by
    intro a ha b hb hab
    by_contra hdeg
    have hc := Polynomial.eq_C_of_degree_le_zero (not_lt.mp hdeg)
    have h1 := congrArg (Polynomial.eval 1) hc
    have h0 := congrArg (Polynomial.eval 0) hc
    simp only [Polynomial.eval_sub, eval_line, Polynomial.eval_C, one_smul, zero_smul] at h1 h0
    apply hzQ (a, b) (Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩)
    simp only [map_sub, eval_C]
    rw [h1, h0]
    simp
  have hsum : ∀ᶠ u in atTop, ∑ a ∈ S, (line z (P.coeff a)).eval u *
      Real.exp ((line z (expo p a)).eval u) = 0 := by
    refine Eventually.of_forall fun u => ?_
    simpa only [eval_line] using hall (u • z)
  have := coeff_eq_zero_of_eventually_sum_mul_exp _ _ S hQ hsum a₁ ha₁
  have h1 := congrArg (Polynomial.eval 1) this
  rw [eval_line, one_smul, Polynomial.eval_zero] at h1
  exact hzr a₁ ha₁ h1


/-- `lem:independence` (Exponentials of polynomials) as algebraic independence. On a nonempty
open set `U`, the functions `e^{p j}` together with the coordinate functions are algebraically
independent over `ℝ` in the ring of real functions on `U`. Since the coordinates generate the
polynomial functions, this says that the `e^{p j}` are algebraically independent over the
polynomial functions on `U`, hence over `ℝ(x)`. -/
theorem algebraicIndependent_exp_poly {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]
    (p : ι → MvPolynomial σ ℝ) (hp : IntCombNonconst p)
    {U : Set (σ → ℝ)} (hU : IsOpen U) (hne : U.Nonempty) :
    AlgebraicIndependent ℝ (Sum.elim (fun j (x : U) => Real.exp (eval (x : σ → ℝ) (p j)))
      (fun i (x : U) => (x : σ → ℝ) i)) := by
  rw [algebraicIndependent_iff]
  intro F hF
  have key : ∀ x : U, aeval (Sum.elim (fun j (x : U) => Real.exp (eval (x : σ → ℝ) (p j)))
      (fun i (x : U) => (x : σ → ℝ) i)) F x =
      eval (fun j => Real.exp (eval (x : σ → ℝ) (p j)))
        (map (eval (x : σ → ℝ)) (sumAlgEquiv ℝ ι σ F)) := by
    intro x
    clear hF
    induction F using MvPolynomial.induction_on with
    | C a => simp only [aeval_C, sumAlgEquiv_C_inl, map_C, eval_C]; rfl
    | add f g hf hg => simp only [map_add, Pi.add_apply, hf, hg]
    | mul_X f k hf =>
      rcases k with j | i
      · simp only [map_mul, Pi.mul_apply, hf, aeval_X, sumAlgEquiv_X_inl, map_X, eval_X,
          Sum.elim_inl]
      · simp only [map_mul, Pi.mul_apply, hf, aeval_X, sumAlgEquiv_X_inr, map_C, eval_C, eval_X,
          Sum.elim_inr]
  have h0 := exp_poly_relation_eq_zero p hp hU hne (sumAlgEquiv ℝ ι σ F) fun x hx => by
    rw [← key ⟨x, hx⟩, hF]
    rfl
  exact (sumAlgEquiv ℝ ι σ).injective (h0.trans (map_zero _).symm)

end ExactAttention
