import ExactAttention.Main

/-!
# Containment of an exponential

This file proves the first assertion of `lem:independence` (Exponentials of polynomials) and
`lem:character` (Containment of an exponential).

* `exp_poly_linear_relation_eq_zero`: if real polynomials `P a` have nonconstant pairwise
  differences and `∑ₐ rₐ(x) e^{Pₐ(x)} = 0` on a nonempty open set, with polynomial coefficients
  `rₐ`, then every `rₐ` is zero.
* `expElem U q` is the class of `x ↦ e^{q(x)}` in the field of analytic functions on `U`. These
  classes turn sums of exponents into products, and `linearIndependent_expElem` states the first
  assertion of `lem:independence` in this field: exponentials of polynomials with nonconstant
  pairwise differences are linearly independent over `ℝ(x)`.
* `exp_mem_adjoin_exp` is `lem:character`: if `r` and `p₁, …, p_L` have zero constant term and
  `e^r` lies in `ℝ(x)(e^{p₁}, …, e^{p_L})`, then `r` is an integer combination of the `p_ℓ`.

A linear relation over `ℝ(x)` becomes one with polynomial coefficients after multiplying by a
common denominator, and that relation is handled by the one-variable argument of `ExpPoly.lean`
after restriction to a generic line.
-/

open MvPolynomial Filter Topology

namespace ExactAttention

namespace Character

/-- A linear relation `∑_{a ∈ S} rₐ(x) e^{Pₐ(x)} = 0` on a nonempty open set, with exponents
whose pairwise differences on `S` are nonconstant, has all coefficients zero. -/
theorem coeff_eq_zero_of_sum_mul_exp {α σ : Type*} [Fintype σ] (S : Finset α)
    (P r : α → MvPolynomial σ ℝ) (hP : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∀ c : ℝ, P a - P b ≠ C c)
    {U : Set (σ → ℝ)} (hU : IsOpen U) (hne : U.Nonempty)
    (h : ∀ x ∈ U, ∑ a ∈ S, eval x (r a) * Real.exp (eval x (P a)) = 0) :
    ∀ a ∈ S, r a = 0 := by
  classical
  set F : (σ → ℝ) → ℝ := fun x => ∑ a ∈ S, eval x (r a) * Real.exp (eval x (P a))
  -- The relation is analytic on all of `ℝ^σ`, so it vanishes everywhere.
  have hF : AnalyticOnNhd ℝ F Set.univ := by
    refine Finset.analyticOnNhd_fun_sum _ fun a _ => ?_
    exact (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℝ) (r a)).mul
      (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℝ) (P a)).rexp
  have hall : ∀ x, F x = 0 := by
    obtain ⟨x₀, hx₀⟩ := hne
    have h₀ : F =ᶠ[𝓝 x₀] 0 := by
      filter_upwards [hU.mem_nhds hx₀] with x hx
      exact h x hx
    intro x
    exact hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ x₀) h₀ (Set.mem_univ x)
  intro a₁ ha₁
  by_contra hr
  -- A point `z` where `r a₁` and all nonconstant parts of the differences are nonzero.
  set G : MvPolynomial σ ℝ := r a₁ *
    ∏ ab ∈ S.offDiag, (P ab.1 - P ab.2 - C (eval 0 (P ab.1 - P ab.2)))
  have hG : G ≠ 0 := by
    refine mul_ne_zero hr (Finset.prod_ne_zero_iff.mpr fun ab hab => ?_)
    rw [Finset.mem_offDiag] at hab
    exact sub_ne_zero.mpr (hP _ hab.1 _ hab.2.1 hab.2.2 _)
  obtain ⟨z, hz⟩ : ∃ z, eval z G ≠ 0 := by
    by_contra! h
    exact hG (MvPolynomial.funext fun x => by simp [h x])
  simp only [G, map_mul, map_prod, mul_ne_zero_iff, Finset.prod_ne_zero_iff] at hz
  obtain ⟨hzr, hzQ⟩ := hz
  -- The restriction to the line through `z` is a one-variable relation.
  have hQ : ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      0 < (ExpPoly.line z (P a) - ExpPoly.line z (P b)).degree := by
    intro a ha b hb hab
    by_contra hdeg
    have hc := Polynomial.eq_C_of_degree_le_zero (not_lt.mp hdeg)
    have h1 := congrArg (Polynomial.eval 1) hc
    have h0 := congrArg (Polynomial.eval 0) hc
    simp only [Polynomial.eval_sub, ExpPoly.eval_line, Polynomial.eval_C, one_smul,
      zero_smul] at h1 h0
    apply hzQ (a, b) (Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩)
    simp only [map_sub, eval_C]
    rw [h1, h0]
    simp
  have hsum : ∀ᶠ u in atTop, ∑ a ∈ S, (ExpPoly.line z (r a)).eval u *
      Real.exp ((ExpPoly.line z (P a)).eval u) = 0 := by
    refine Eventually.of_forall fun u => ?_
    simpa only [ExpPoly.eval_line] using hall (u • z)
  have := ExpPoly.coeff_eq_zero_of_eventually_sum_mul_exp _ _ S hQ hsum a₁ ha₁
  have h1 := congrArg (Polynomial.eval 1) this
  rw [ExpPoly.eval_line, one_smul, Polynomial.eval_zero] at h1
  exact hzr h1

end Character

/-- `lem:independence` (Exponentials of polynomials), first assertion, with polynomial
coefficients. Let `P a` be real polynomials whose pairwise differences are nonconstant. If
`∑ₐ rₐ(x) e^{Pₐ(x)} = 0` for every `x` in a nonempty open set `U`, where the `rₐ` are
polynomials, then every `rₐ` is zero. -/
theorem exp_poly_linear_relation_eq_zero {α σ : Type*} [Fintype α] [Fintype σ]
    (P : α → MvPolynomial σ ℝ) (hP : ∀ a b, a ≠ b → ∀ c : ℝ, P a - P b ≠ C c)
    (r : α → MvPolynomial σ ℝ) {U : Set (σ → ℝ)} (hU : IsOpen U) (hne : U.Nonempty)
    (h : ∀ x ∈ U, ∑ a, eval x (r a) * Real.exp (eval x (P a)) = 0) :
    ∀ a, r a = 0 := fun a =>
  Character.coeff_eq_zero_of_sum_mul_exp Finset.univ P r
    (fun a _ b _ hab => hP a b hab) hU hne h a (Finset.mem_univ a)

section Field

variable {σ : Type*} [Fintype σ]

/-- The function `x ↦ e^{q(x)}` is analytic everywhere. -/
theorem analyticOnNhd_exp_eval (q : MvPolynomial σ ℝ) :
    AnalyticOnNhd ℝ (fun x : σ → ℝ => Real.exp (eval x q)) Set.univ :=
  (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℝ) q).rexp

variable (U : Set (σ → ℝ))

namespace Character

/-- The function `x ↦ e^{q(x)}` as an element of the analytic ring on `U`. -/
noncomputable def expRingElem (q : MvPolynomial σ ℝ) : analyticRing U :=
  ⟨fun x : U => Real.exp (eval (x : σ → ℝ) q),
    AnalyticField.restrict_mem fun x _ => analyticOnNhd_exp_eval q x (Set.mem_univ x)⟩

theorem expRingElem_apply (q : MvPolynomial σ ℝ) (x : U) :
    (expRingElem U q : U → ℝ) x = Real.exp (eval (x : σ → ℝ) q) :=
  rfl

theorem expRingElem_add (p q : MvPolynomial σ ℝ) :
    expRingElem U (p + q) = expRingElem U p * expRingElem U q := by
  apply Subtype.ext
  funext x
  simp [expRingElem, Real.exp_add]

theorem expRingElem_zero : expRingElem U (0 : MvPolynomial σ ℝ) = 1 := by
  apply Subtype.ext
  funext x
  simp [expRingElem]

end Character

open Character

/-- The class of `x ↦ e^{q(x)}` in the field of analytic functions on `U`. -/
noncomputable def expElem (q : MvPolynomial σ ℝ) : AnalyticFunctionField U :=
  algebraMap (analyticRing U) _ (expRingElem U q)

/-- Exponentials turn sums of exponents into products. -/
theorem expElem_add (p q : MvPolynomial σ ℝ) :
    expElem U (p + q) = expElem U p * expElem U q := by
  rw [expElem, expRingElem_add, map_mul]
  rfl

theorem expElem_zero : expElem U (0 : MvPolynomial σ ℝ) = 1 := by
  rw [expElem, expRingElem_zero, map_one]

theorem expElem_nsmul (n : ℕ) (q : MvPolynomial σ ℝ) :
    expElem U (n • q) = expElem U q ^ n := by
  induction n with
  | zero => rw [zero_smul, expElem_zero, pow_zero]
  | succ n ih => rw [succ_nsmul, expElem_add, ih, pow_succ]

theorem expElem_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℝ) :
    expElem U (∑ i ∈ s, f i) = ∏ i ∈ s, expElem U (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, expElem_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, expElem_add, ih]

theorem expElem_mul_expElem_neg (q : MvPolynomial σ ℝ) :
    expElem U q * expElem U (-q) = 1 := by
  rw [← expElem_add, add_neg_cancel, expElem_zero]

variable [Fact (IsOpen U)] [Fact (IsConnected U)]

theorem expElem_ne_zero (q : MvPolynomial σ ℝ) : expElem U q ≠ 0 :=
  left_ne_zero_of_mul_eq_one (expElem_mul_expElem_neg U q)

namespace Character

/-- The finite form of linear independence: a vanishing combination of the `expElem U (P a)`,
`a ∈ S`, with coefficients in `ℝ(x)` and pairwise nonconstant differences of exponents on `S`,
has all coefficients zero. -/
theorem coeff_eq_zero_of_sum_smul_expElem {α : Type*} (S : Finset α)
    (P : α → MvPolynomial σ ℝ) (hP : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∀ c : ℝ, P a - P b ≠ C c)
    (g : α → FractionRing (MvPolynomial σ ℝ))
    (h : ∑ a ∈ S, g a • expElem U (P a) = 0) : ∀ a ∈ S, g a = 0 := by
  classical
  -- Clear denominators.
  obtain ⟨b, hb⟩ :=
    IsLocalization.exist_integer_multiples (nonZeroDivisors (MvPolynomial σ ℝ)) S g
  simp only [IsLocalization.IsInteger, RingHom.mem_rangeS] at hb
  choose! r hr using hb
  have hbF : algebraMap (MvPolynomial σ ℝ) (FractionRing (MvPolynomial σ ℝ)) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hK : algebraMap (analyticRing U) (AnalyticFunctionField U)
      (∑ a ∈ S, polyToAnalytic U (r a) * expRingElem U (P a)) = 0 := by
    have key : ∀ a ∈ S, algebraMap (analyticRing U) (AnalyticFunctionField U)
        (polyToAnalytic U (r a) * expRingElem U (P a)) =
          algebraMap (FractionRing (MvPolynomial σ ℝ)) (AnalyticFunctionField U)
            (algebraMap (MvPolynomial σ ℝ) (FractionRing (MvPolynomial σ ℝ)) b) *
            (g a • expElem U (P a)) := by
      intro a ha
      rw [map_mul, ← ratFuncToAnalytic_algebraMap, ← Main.algebraMap_ratFunc, hr a ha,
        Algebra.smul_def, Algebra.smul_def (g a), map_mul, mul_assoc]
      rfl
    rw [map_sum, Finset.sum_congr rfl key, ← Finset.mul_sum, h, mul_zero]
  have hring : ∑ a ∈ S, polyToAnalytic U (r a) * expRingElem U (P a) = 0 :=
    IsFractionRing.injective (analyticRing U) (AnalyticFunctionField U)
      (hK.trans (map_zero _).symm)
  have hpt : ∀ x ∈ U, ∑ a ∈ S, eval x (r a) * Real.exp (eval x (P a)) = 0 := by
    intro x hx
    have := congrArg (fun f : analyticRing U => (f : U → ℝ) ⟨x, hx⟩) hring
    simpa [polyToAnalytic_apply, expRingElem_apply] using this
  have hr0 := coeff_eq_zero_of_sum_mul_exp S P r hP Fact.out
    (Fact.out : IsConnected U).nonempty hpt
  intro a ha
  have := hr a ha
  rw [hr0 a ha, map_zero, Algebra.smul_def] at this
  exact (mul_eq_zero.mp this.symm).resolve_left hbF

end Character

open Character

/-- `lem:independence` (Exponentials of polynomials), first assertion. On a nonempty connected
open set `U`, the classes of `e^{P a}` in the field of analytic functions are linearly
independent over `ℝ(x)` whenever the pairwise differences of the `P a` are nonconstant. -/
theorem linearIndependent_expElem {α : Type*} (P : α → MvPolynomial σ ℝ)
    (hP : ∀ a b, a ≠ b → ∀ c : ℝ, P a - P b ≠ C c) :
    LinearIndependent (FractionRing (MvPolynomial σ ℝ)) (fun a => expElem U (P a)) :=
  linearIndependent_iff'.mpr fun s g hg =>
    coeff_eq_zero_of_sum_smul_expElem U s P (fun a _ b _ hab => hP a b hab) g hg

end Field

/-- The ratio `R_{ij}` of `Main.ratioElem` is the exponential of its exponent polynomial
`q_i · (k_j - k_n)`. -/
theorem ratioElem_eq_expElem {m d : ℕ} (U : Set (CoefficientField.Coord (m + 1) d → ℝ))
    [Fact (IsOpen U)] [Fact (IsConnected U)] (i j : Fin (m + 1)) :
    Main.ratioElem U i j = expElem U (CoefficientField.ratioExponent i j) := by
  unfold Main.ratioElem expElem
  congr 1
  apply Subtype.ext
  funext x
  exact CoefficientField.attnRatio_eq_exp_eval (x : CoefficientField.Coord (m + 1) d → ℝ) i j

namespace Character

variable {σ : Type*} [Fintype σ]

/-- A monomial in the `expElem U (p ℓ)` is the exponential of the matching combination of the
`p ℓ`. -/
theorem prod_expElem_pow (U : Set (σ → ℝ)) {L : ℕ} (p : Fin L → MvPolynomial σ ℝ)
    (m : Fin L →₀ ℕ) :
    ∏ ℓ, expElem U (p ℓ) ^ m ℓ = expElem U (ExpPoly.expo p m) := by
  rw [ExpPoly.expo, expElem_sum]
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  rw [Nat.cast_smul_eq_nsmul, expElem_nsmul]

omit [Fintype σ] in
theorem constantCoeff_expo {L : ℕ} (p : Fin L → MvPolynomial σ ℝ)
    (hp : ∀ ℓ, constantCoeff (p ℓ) = 0) (m : Fin L →₀ ℕ) :
    constantCoeff (ExpPoly.expo p m) = 0 := by
  simp [ExpPoly.expo, constantCoeff_smul, hp]

omit [Fintype σ] in
/-- Distinct polynomials with zero constant term have nonconstant difference. -/
theorem sub_ne_C_of_constantCoeff {p q : MvPolynomial σ ℝ} (hp : constantCoeff p = 0)
    (hq : constantCoeff q = 0) (hpq : p ≠ q) (c : ℝ) : p - q ≠ C c := by
  intro h
  have h0 := congrArg constantCoeff h
  rw [map_sub, hp, hq, sub_zero, constantCoeff_C] at h0
  rw [← h0, map_zero, sub_eq_zero] at h
  exact hpq h

end Character

open Character

/-- `lem:character` (Containment of an exponential). Let `r` and `p₁, …, p_L` be real
polynomials with zero constant term, and let `U` be a nonempty connected open set. If `e^r` lies
in the field generated over `ℝ(x)` by `e^{p₁}, …, e^{p_L}` inside the field of analytic functions
on `U`, then `r` is an integer linear combination of the `p_ℓ`. -/
theorem exp_mem_adjoin_exp {σ : Type*} [Fintype σ] [DecidableEq σ]
    (U : Set (σ → ℝ)) [Fact (IsOpen U)] [Fact (IsConnected U)]
    {L : ℕ} (p : Fin L → MvPolynomial σ ℝ) (r : MvPolynomial σ ℝ)
    (hp : ∀ ℓ, MvPolynomial.constantCoeff (p ℓ) = 0) (hr : MvPolynomial.constantCoeff r = 0)
    (h : expElem U r ∈ IntermediateField.adjoin (FractionRing (MvPolynomial σ ℝ))
      (Set.range fun ℓ => expElem U (p ℓ))) :
    ∃ z : Fin L → ℤ, r = ∑ ℓ, (z ℓ : ℝ) • p ℓ := by
  classical
  set F := FractionRing (MvPolynomial σ ℝ)
  set K := AnalyticFunctionField U
  set e : Fin L → K := fun ℓ => expElem U (p ℓ)
  set E := ExpPoly.expo p
  -- Write `e^r = A(e^p) / B(e^p)`.
  obtain ⟨A, B, hAB⟩ := (IntermediateField.mem_adjoin_range_iff F e _).mp h
  have hr0 : expElem U r ≠ 0 := expElem_ne_zero U r
  have hB : aeval e B ≠ 0 := by
    intro hB
    rw [hB, div_zero] at hAB
    exact hr0 hAB
  have hrel : aeval e B * expElem U r = aeval e A := by
    rw [hAB]
    exact mul_div_cancel₀ _ hB
  have hexp : ∀ D : MvPolynomial (Fin L) F,
      aeval e D = ∑ m ∈ D.support, D.coeff m • expElem U (E m) := by
    intro D
    rw [aeval_def, eval₂_eq']
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Algebra.smul_def, prod_expElem_pow]
  -- Group the terms of both sides by their exponents.
  set T : Finset (MvPolynomial σ ℝ) :=
    B.support.image (fun m => E m + r) ∪ A.support.image E
  set β : MvPolynomial σ ℝ → F := fun q => ∑ m ∈ B.support with E m + r = q, B.coeff m
  set α : MvPolynomial σ ℝ → F := fun q => ∑ m ∈ A.support with E m = q, A.coeff m
  have hβ : aeval e B * expElem U r = ∑ q ∈ T, β q • expElem U q := by
    rw [hexp, Finset.sum_mul, ← Finset.sum_fiberwise_of_maps_to (s := B.support) (t := T)
      (g := fun m => E m + r) (fun m hm => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hm))]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [(Finset.mem_filter.mp hm).2.symm, expElem_add, smul_mul_assoc]
  have hα : aeval e A = ∑ q ∈ T, α q • expElem U q := by
    rw [hexp, ← Finset.sum_fiberwise_of_maps_to (s := A.support) (t := T) (g := E)
      (fun m hm => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hm))]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [(Finset.mem_filter.mp hm).2]
  -- Linear independence matches the grouped coefficients.
  have hT : ∀ q ∈ T, constantCoeff q = 0 := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hq
      rw [map_add, constantCoeff_expo p hp, hr, add_zero]
    · obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hq
      exact constantCoeff_expo p hp m
  have hcoeff : ∀ q ∈ T, β q - α q = 0 := by
    refine coeff_eq_zero_of_sum_smul_expElem U T id
      (fun a ha b hb hab => sub_ne_C_of_constantCoeff (hT a ha) (hT b hb) hab) _ ?_
    simp only [id, sub_smul, Finset.sum_sub_distrib, ← hβ, ← hα, hrel, sub_self]
  -- Some grouped coefficient on the left is nonzero.
  obtain ⟨q, hqT, hq⟩ : ∃ q ∈ T, β q ≠ 0 := by
    by_contra! hzero
    apply mul_ne_zero hB hr0
    rw [hβ]
    exact Finset.sum_eq_zero fun q hq => by rw [hzero q hq, zero_smul]
  obtain ⟨m, hm, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
  have hα0 : α q ≠ 0 := by
    rw [← sub_eq_zero.mp (hcoeff q hqT)]
    exact hq
  obtain ⟨m', hm', -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hα0
  have h1 := (Finset.mem_filter.mp hm).2
  have h2 := (Finset.mem_filter.mp hm').2
  refine ⟨fun ℓ => (m' ℓ : ℤ) - (m ℓ : ℤ), ?_⟩
  have hrE : r = E m' - E m := by
    rw [h2, ← h1]
    ring
  rw [hrE]
  simp only [E, ExpPoly.expo, ← Finset.sum_sub_distrib, ← sub_smul]
  push_cast
  rfl

end ExactAttention
