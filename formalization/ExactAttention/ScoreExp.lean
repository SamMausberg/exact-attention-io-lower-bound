import ExactAttention.Main
import ExactAttention.ScoreDefs
import ExactAttention.PairRank
import ExactAttention.Character

/-!
# Polynomial score arguments (`thm:score-exp`)

This file proves the counting part of `thm:score-exp` (Polynomial score arguments) in
`app:recovery`, which is the second assertion of `thm:attention`.

Score polynomials are real polynomials in variables `s_{ij}` indexed by `Fin n × Fin n`. The
algebra map `scoreSubst n d` substitutes `s_{ij} ↦ q_i · k_j` and gives a polynomial in the input
coordinates `Coord n d`. The matrix `linCoeff p` collects the linear part of `p`: its entry
`(i, j)` is the coefficient of `s_{ij}`.

* `centred_eq_sum_linCoeff` is the step of the proof that takes the coefficient of `t` after
  replacing `Q` by `tQ`. If `q_i · (k_j - k_n) = ∑ c_ℓ P_ℓ(q · k)`, then
  `E_{ij} - E_{in} = ∑ c_ℓ linCoeff P_ℓ`. We read off the coefficient of the monomial
  `Q_{a0} K_{b0}`, to which only the linear part of each `P_ℓ` contributes.
* `linCoeff_rank_le` is the rank limit. If the Jacobian of `x ↦ (P_ℓ(q · k))_ℓ` has rank at most
  `r` on a nonempty open set, then the Jacobian of the linear score forms
  `(Q, K) ↦ (p_{C_ℓ}(Q, K))_ℓ` with `C_ℓ = linCoeff P_ℓ` has rank at most `r` at every point.
  Rank bounds are expressed by the vanishing of the minors `ScoreExp.minorDet`. These are analytic
  in the point, so they vanish everywhere once they vanish on an open set, and they pass to the
  limit `t → 0` of `t⁻¹ P(tQ, K)`.
* `score_exp_io_lower_bound` combines these with `lem:character` (`exp_mem_adjoin_exp`) and
  `lem:pair-rank` (`linearScore_rank_bound`) and gives `(nd + n²d²/M)/16 ≤ I`.

The paper derives two facts from the program on an open execution path, and both are hypotheses
of `score_exp_io_lower_bound`. First, the exponential arguments of an epoch are computed from at
most `2M` incoming values, so their Jacobian has rank at most `2M`. Second, every computed value
lies in `F₀(e^{p_1}, …, e^{p_L})`, so the output derivatives lie there, and with them the centred
ratios `R_{ij}` by `prop:attention-field`. The epoch count `e ≤ I/M + 1` of `eq:epochs` and the
`nd` output stores are hypotheses as well, as in `Main.lean`. The step from a program in the
machine model to these facts is not formalized.
-/

open MvPolynomial Filter Topology Module

namespace ExactAttention

open CoefficientField

namespace ScoreExp

/-- The polynomial `q_i · k_j` in the input coordinates. -/
noncomputable def scorePoly (n d : ℕ) (ij : Fin n × Fin n) : MvPolynomial (Coord n d) ℝ :=
  ∑ l, X (.q ij.1 l) * X (.k ij.2 l)

end ScoreExp

open ScoreExp

/-- Substitution of the full scores into a score polynomial: the variable `s_{ij}` is sent to
`q_i · k_j`. -/
noncomputable def scoreSubst (n d : ℕ) :
    MvPolynomial (Fin n × Fin n) ℝ →ₐ[ℝ] MvPolynomial (Coord n d) ℝ :=
  aeval (scorePoly n d)

/-- The coefficient matrix of the linear part of a score polynomial: the entry `(i, j)` is the
coefficient of `s_{ij}`. -/
noncomputable def linCoeff {n : ℕ} (p : MvPolynomial (Fin n × Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => p.coeff (Finsupp.single (i, j) 1)

namespace ScoreExp

variable {n d : ℕ}

theorem linCoeff_apply (p : MvPolynomial (Fin n × Fin n) ℝ) (i j : Fin n) :
    linCoeff p i j = p.coeff (Finsupp.single (i, j) 1) := rfl

theorem linCoeff_sum {L : ℕ} (c : Fin L → ℝ) (p : Fin L → MvPolynomial (Fin n × Fin n) ℝ) :
    linCoeff (∑ ℓ, c ℓ • p ℓ) = ∑ ℓ, c ℓ • linCoeff (p ℓ) := by
  ext a b
  simp [linCoeff_apply, Matrix.sum_apply]

/-- The coefficient of the monomial `Q_{a l₀} K_{b l₀}` in a polynomial in the inputs. -/
noncomputable def coeffQK (l₀ : Fin d) (a b : Fin n) (f : MvPolynomial (Coord n d) ℝ) : ℝ :=
  f.coeff (Finsupp.single (Coord.q a l₀) 1 + Finsupp.single (Coord.k b l₀) 1)

theorem coeffQK_X_mul_X (l₀ : Fin d) (a b i j : Fin n) (l : Fin d) :
    coeffQK l₀ a b (X (Coord.q i l) * X (Coord.k j l) : MvPolynomial (Coord n d) ℝ) =
      if i = a ∧ j = b ∧ l = l₀ then 1 else 0 := by
  rw [coeffQK, X, X, monomial_mul_monomial, coeff_monomial, one_mul]
  congr 1
  apply propext
  constructor
  · intro h
    have h1 := DFunLike.congr_fun h (Coord.q i l)
    have h2 := DFunLike.congr_fun h (Coord.k j l)
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply] at h1 h2
    simp at h1 h2
    obtain ⟨rfl, rfl⟩ := h1
    exact ⟨rfl, h2.1.symm, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem coeffQK_scorePoly (l₀ : Fin d) (a b : Fin n) (ij : Fin n × Fin n) :
    coeffQK l₀ a b (scorePoly n d ij) = if ij = (a, b) then 1 else 0 := by
  have h : coeffQK l₀ a b (scorePoly n d ij) =
      ∑ l, coeffQK l₀ a b (X (Coord.q ij.1 l) * X (Coord.k ij.2 l)) := coeff_sum _ _ _
  rw [h]
  simp_rw [coeffQK_X_mul_X]
  rcases ij with ⟨i, j⟩
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · have h' : ¬ (i, j) = (a, b) := by simpa using h
    simp only [h', ite_false]
    refine Finset.sum_eq_zero fun l _ => ?_
    simp only [ite_eq_right_iff]
    tauto

/-- The coefficient of `Q_{a l₀} K_{b l₀}` in `p(q_i · k_j)` is the coefficient of `s_{ab}`
in `p`. Only the linear part of `p` contributes, since the other homogeneous parts give
polynomials of degree `0` or at least `4`. -/
theorem coeffQK_scoreSubst (l₀ : Fin d) (a b : Fin n) (p : MvPolynomial (Fin n × Fin n) ℝ) :
    coeffQK l₀ a b (scoreSubst n d p) = linCoeff p a b := by
  induction p using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [linCoeff_apply, coeff_monomial]
    by_cases hu : u.degree = 1
    · obtain ⟨ij, rfl⟩ : u ∈ Set.range (fun a => Finsupp.single a 1) := by
        rw [Finsupp.range_single_one]
        exact hu
      rw [scoreSubst, aeval_monomial, Finsupp.prod_single_index (by simp), pow_one, coeffQK,
        algebraMap_eq, coeff_C_mul, ← coeffQK, coeffQK_scorePoly]
      simp only [Finsupp.single_left_inj one_ne_zero, mul_ite, mul_one, mul_zero]
    · have hhom : (scoreSubst n d (monomial u c)).IsHomogeneous (2 * u.degree) :=
        (isHomogeneous_monomial c rfl).aeval _ fun ij => by
          refine IsHomogeneous.sum _ _ _ fun l _ => ?_
          exact (isHomogeneous_X _ _).mul (isHomogeneous_X _ _)
      have hne : ¬ u = Finsupp.single (a, b) 1 := by
        rintro rfl
        exact hu (by simp)
      rw [coeffQK, hhom.coeff_eq_zero]
      · simp [hne]
      · rw [map_add, Finsupp.degree_single, Finsupp.degree_single]
        omega
  | add p q hp hq =>
    have h : coeffQK l₀ a b (scoreSubst n d (p + q)) =
        coeffQK l₀ a b (scoreSubst n d p) + coeffQK l₀ a b (scoreSubst n d q) := by
      simp [coeffQK]
    rw [h, hp, hq]
    simp [linCoeff_apply]

/-- The linear part of a score polynomial is determined by its image under `scoreSubst`. -/
theorem linCoeff_eq_of_scoreSubst_eq (hd : 0 < d) {p p' : MvPolynomial (Fin n × Fin n) ℝ}
    (h : scoreSubst n d p = scoreSubst n d p') : linCoeff p = linCoeff p' := by
  ext a b
  rw [← coeffQK_scoreSubst ⟨0, hd⟩, h, coeffQK_scoreSubst]

/-- The determinant of the square matrix `(φ_a (A w_b))`. For `k = r + 1`, all of these
determinants vanish exactly when `A` has rank at most `r` (`minorDet_eq_zero` and
`exists_minorDet_ne_zero`). -/
noncomputable def minorDet {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] {k : ℕ} (A : E →ₗ[ℝ] F) (w : Fin k → E) (φ : Fin k → F →ₗ[ℝ] ℝ) : ℝ :=
  (Matrix.of fun a b => φ a (A (w b))).det

section Minors

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [FiniteDimensional ℝ F]

/-- If `A` has rank at most `r`, every `(r+1)`-minor `minorDet A w φ` vanishes. -/
theorem minorDet_eq_zero (A : E →ₗ[ℝ] F) {r : ℕ} (h : finrank ℝ (LinearMap.range A) ≤ r)
    (w : Fin (r + 1) → E) (φ : Fin (r + 1) → F →ₗ[ℝ] ℝ) : minorDet A w φ = 0 := by
  rw [minorDet, ← Matrix.exists_mulVec_eq_zero_iff]
  let v : Fin (r + 1) → LinearMap.range A := fun b => ⟨A (w b), LinearMap.mem_range_self A (w b)⟩
  have hv : ¬ LinearIndependent ℝ v := by
    intro hli
    have := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at this
    omega
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hv
  refine ⟨g, fun h0 => hi (congrFun h0 i), ?_⟩
  have hsum : ∑ b, g b • A (w b) = 0 := by
    have := congrArg Subtype.val hg
    simpa [v] using this
  funext a
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
  calc ∑ b, φ a (A (w b)) * g b = φ a (∑ b, g b • A (w b)) := by
        simp [map_sum, mul_comm]
    _ = 0 := by rw [hsum, map_zero]

/-- If `A` has rank more than `r`, some `(r+1)`-minor `minorDet A w φ` is nonzero. -/
theorem exists_minorDet_ne_zero (A : E →ₗ[ℝ] F) {r : ℕ}
    (h : r < finrank ℝ (LinearMap.range A)) :
    ∃ (w : Fin (r + 1) → E) (φ : Fin (r + 1) → F →ₗ[ℝ] ℝ), minorDet A w φ ≠ 0 := by
  classical
  set R := LinearMap.range A
  let bR := Module.finBasis ℝ R
  have hle : r + 1 ≤ finrank ℝ R := h
  let v : Fin (r + 1) → F := fun b => (bR (Fin.castLE hle b) : F)
  have hv : LinearIndependent ℝ v :=
    (bR.linearIndependent.comp _ (Fin.castLE_injective hle)).map' R.subtype R.ker_subtype
  have hw : ∀ b, ∃ x, A x = v b := fun b => (bR (Fin.castLE hle b)).2
  choose w hw using hw
  let T : (Fin (r + 1) → ℝ) →ₗ[ℝ] F := Fintype.linearCombination ℝ v
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro g hg
    funext i
    exact Fintype.linearIndependent_iff.mp hv g (by simpa [T, Fintype.linearCombination_apply]
      using hg) i
  obtain ⟨S, hS⟩ := T.exists_leftInverse_of_injective hT
  refine ⟨w, fun a => (LinearMap.proj a).comp S, ?_⟩
  have hSv : ∀ b, S (v b) = Pi.single b 1 := by
    intro b
    have := LinearMap.congr_fun hS (Pi.single b 1)
    simpa [T, Fintype.linearCombination_apply, Pi.single_apply] using this
  have hM : (Matrix.of fun a b => ((LinearMap.proj a).comp S) (A (w b)) : Matrix _ _ ℝ) = 1 := by
    ext a b
    simp [hw, hSv, Matrix.one_apply, Pi.single_apply]
  rw [minorDet, hM, Matrix.det_one]
  exact one_ne_zero

end Minors

section Limits

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem continuous_minorDet {k : ℕ} (w : Fin k → E) (φ : Fin k → F →ₗ[ℝ] ℝ) :
    Continuous fun B : E →L[ℝ] F => minorDet (B : E →ₗ[ℝ] F) w φ := by
  unfold minorDet
  refine Continuous.matrix_det ?_
  refine continuous_pi fun a => continuous_pi fun b => ?_
  exact (LinearMap.continuous_of_finiteDimensional (φ a)).comp (continuous_eval_const (w b))

/-- The rank is lower semicontinuous: a limit of maps of rank at most `r` has rank at most `r`. -/
theorem finrank_range_le_of_tendsto {A : ℝ → E →L[ℝ] F} {A₀ : E →L[ℝ] F} {r : ℕ}
    (hA : Tendsto A (𝓝[≠] 0) (𝓝 A₀))
    (hr : ∀ t ≠ 0, finrank ℝ (LinearMap.range (A t : E →ₗ[ℝ] F)) ≤ r) :
    finrank ℝ (LinearMap.range (A₀ : E →ₗ[ℝ] F)) ≤ r := by
  by_contra hlt
  push Not at hlt
  obtain ⟨w, φ, hne⟩ := exists_minorDet_ne_zero (A₀ : E →ₗ[ℝ] F) hlt
  have h1 : Tendsto (fun t => minorDet (A t : E →ₗ[ℝ] F) w φ) (𝓝[≠] 0)
      (𝓝 (minorDet (A₀ : E →ₗ[ℝ] F) w φ)) :=
    ((continuous_minorDet w φ).tendsto A₀).comp hA
  have h2 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), minorDet (A t : E →ₗ[ℝ] F) w φ = 0 :=
    eventually_nhdsWithin_of_forall fun t ht => minorDet_eq_zero _ (hr t ht) w φ
  exact hne (tendsto_nhds_unique h1 (tendsto_const_nhds.congr' (h2.mono fun t ht => ht.symm)))

/-- A rank bound for the derivative of an analytic map on a nonempty open set holds
everywhere: the minors are analytic functions that vanish on the open set. -/
theorem finrank_range_fderiv_le {f : E → F} (hf : AnalyticOnNhd ℝ f Set.univ) {U : Set E}
    (hU : IsOpen U) (hne : U.Nonempty) {r : ℕ}
    (h : ∀ x ∈ U, finrank ℝ (LinearMap.range (fderiv ℝ f x : E →ₗ[ℝ] F)) ≤ r) (x : E) :
    finrank ℝ (LinearMap.range (fderiv ℝ f x : E →ₗ[ℝ] F)) ≤ r := by
  have : CompleteSpace F := FiniteDimensional.complete ℝ F
  by_contra hlt
  push Not at hlt
  obtain ⟨w, φ, hne'⟩ := exists_minorDet_ne_zero (fderiv ℝ f x : E →ₗ[ℝ] F) hlt
  set g : E → ℝ := fun y => minorDet (fderiv ℝ f y : E →ₗ[ℝ] F) w φ
  have hentry : ∀ a b, AnalyticOnNhd ℝ (fun y => φ a (fderiv ℝ f y (w b))) Set.univ := by
    intro a b y _
    have h1 := ((ContinuousLinearMap.apply ℝ F (w b)).analyticAt (fderiv ℝ f y)).comp
      (hf.fderiv y (Set.mem_univ y))
    exact (LinearMap.toContinuousLinearMap (φ a)).analyticAt _ |>.comp h1
  have hg : AnalyticOnNhd ℝ g Set.univ := by
    intro y _
    simp only [g, minorDet, Matrix.det_apply', Matrix.of_apply]
    refine Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul ?_
    exact Finset.analyticAt_fun_prod _ fun i _ => hentry _ _ y (Set.mem_univ y)
  obtain ⟨x₀, hx₀⟩ := hne
  have hev : g =ᶠ[𝓝 x₀] 0 := by
    filter_upwards [hU.mem_nhds hx₀] with y hy
    exact minorDet_eq_zero _ (h y hy) w φ
  exact hne' (hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ x₀) hev (Set.mem_univ x))

end Limits

section Homogeneous

variable {σ : Type*}

/-- A homogeneous polynomial of degree `k` scales by `t^k`. -/
theorem eval_smul_of_isHomogeneous {φ : MvPolynomial σ ℝ} {k : ℕ} (hφ : φ.IsHomogeneous k)
    (t : ℝ) (s : σ → ℝ) : eval (t • s) φ = t ^ k * eval s φ := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hk := hφ.degree_eq_sum_deg_support hu
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← hk]
  ring

theorem sum_homogeneousComponent_of_lt (φ : MvPolynomial σ ℝ) {N : ℕ}
    (hN : φ.totalDegree < N) : ∑ k ∈ Finset.range N, homogeneousComponent k φ = φ := by
  conv_rhs => rw [← sum_homogeneousComponent φ]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun k hk hk' => ?_
  simp only [Finset.mem_range, not_lt] at hk hk'
  exact homogeneousComponent_eq_zero k φ (by omega)

/-- `φ(t s)` as a polynomial in `t` whose coefficients are the homogeneous parts of `φ`. -/
theorem eval_smul_eq_sum (φ : MvPolynomial σ ℝ) {N : ℕ} (hN : φ.totalDegree < N) (t : ℝ)
    (s : σ → ℝ) :
    eval (t • s) φ = ∑ k ∈ Finset.range N, t ^ k * eval s (homogeneousComponent k φ) := by
  conv_lhs => rw [← sum_homogeneousComponent_of_lt φ hN]
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ =>
    eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous k φ) t s

/-- The homogeneous part of degree one is the linear part. -/
theorem eval_homogeneousComponent_one [Fintype σ] [DecidableEq σ] (φ : MvPolynomial σ ℝ)
    (s : σ → ℝ) :
    eval s (homogeneousComponent 1 φ) = ∑ i, φ.coeff (Finsupp.single i 1) * s i := by
  have h : homogeneousComponent 1 φ =
      ∑ i, monomial (Finsupp.single i 1) (φ.coeff (Finsupp.single i 1)) := by
    ext u
    rw [coeff_homogeneousComponent, coeff_sum]
    simp only [coeff_monomial]
    by_cases hu : u.degree = 1
    · obtain ⟨i, rfl⟩ : u ∈ Set.range fun i => Finsupp.single i 1 := by
        rw [Finsupp.range_single_one]
        exact hu
      simp [Finsupp.single_left_inj one_ne_zero]
    · simp only [hu, ite_false]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      rw [ite_eq_right_iff]
      rintro rfl
      simp at hu
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_monomial, Finsupp.prod_single_index (by simp), pow_one]

theorem differentiable_eval_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype σ] {s : E → σ → ℝ} (hs : Differentiable ℝ s) (φ : MvPolynomial σ ℝ) :
    Differentiable ℝ fun z => eval (s z) φ := fun z =>
  ((AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℝ) φ) (s z) (Set.mem_univ _)).differentiableAt.comp z
    (hs z)

end Homogeneous

/-- The full scores `q_i · k_j` of a query-key input. -/
noncomputable def fullScores (z : QKInputs n d) : Fin n × Fin n → ℝ :=
  fun ij => ∑ l, z.1 ij.1 l * z.2 ij.2 l

theorem differentiable_fullScores : Differentiable ℝ (fullScores (n := n) (d := d)) := by
  unfold fullScores
  fun_prop

/-- The input point with queries `t Q`, keys `K` and values `0`, as a linear map. -/
noncomputable def embedQKₗ (t : ℝ) : QKInputs n d →ₗ[ℝ] (Coord n d → ℝ) where
  toFun z c := match c with
    | .q i l => t * z.1 i l
    | .k j l => z.2 j l
    | .v _ _ => 0
  map_add' z z' := by
    funext c
    cases c <;> simp [mul_add]
  map_smul' a z := by
    funext c
    cases c <;> simp [mul_left_comm]

/-- The input point with queries `t Q`, keys `K` and values `0`. -/
noncomputable def embedQK (t : ℝ) : QKInputs n d →L[ℝ] (Coord n d → ℝ) :=
  LinearMap.toContinuousLinearMap (embedQKₗ t)

theorem eval_scoreSubst (x : Coord n d → ℝ) (p : MvPolynomial (Fin n × Fin n) ℝ) :
    eval x (scoreSubst n d p) = eval (fun ij => eval x (scorePoly n d ij)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [scoreSubst]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p ij hp => rw [map_mul, map_mul, hp, map_mul, eval_X, scoreSubst, aeval_X]

theorem eval_embedQK_scoreSubst (t : ℝ) (z : QKInputs n d)
    (p : MvPolynomial (Fin n × Fin n) ℝ) :
    eval (embedQK t z) (scoreSubst n d p) = eval (t • fullScores z) p := by
  have h : (fun ij => eval (embedQK t z) (scorePoly n d ij)) = t • fullScores z := by
    funext ij
    simp [scorePoly, embedQK, embedQKₗ, fullScores, Finset.mul_sum, mul_assoc]
  rw [eval_scoreSubst, h]

/-- The degree `k` homogeneous parts of a family of score polynomials, evaluated at the full
scores. -/
noncomputable def homogPart {L : ℕ} (P : Fin L → MvPolynomial (Fin n × Fin n) ℝ) (k : ℕ)
    (z : QKInputs n d) : Fin L → ℝ :=
  fun ℓ => eval (fullScores z) (homogeneousComponent k (P ℓ))

theorem differentiable_homogPart {L : ℕ} (P : Fin L → MvPolynomial (Fin n × Fin n) ℝ) (k : ℕ) :
    Differentiable ℝ (homogPart (d := d) P k) :=
  differentiable_pi.mpr fun _ => differentiable_eval_comp differentiable_fullScores _

theorem homogPart_zero {L : ℕ} (P : Fin L → MvPolynomial (Fin n × Fin n) ℝ) :
    homogPart (d := d) P 0 = fun _ ℓ => (P ℓ).coeff 0 := by
  funext z ℓ
  simp [homogPart]

theorem homogPart_one {L : ℕ} (P : Fin L → MvPolynomial (Fin n × Fin n) ℝ) :
    homogPart (d := d) P 1 = fun z ℓ => scoreForm (linCoeff (P ℓ)) z := by
  funext z ℓ
  rw [homogPart, eval_homogeneousComponent_one, scoreForm, Fintype.sum_prod_type]
  rfl

theorem range_smul_comp_le {E G F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] (c : ℝ)
    (B : G →L[ℝ] F) (C : E →L[ℝ] G) :
    LinearMap.range ((c • B.comp C : E →L[ℝ] F) : E →ₗ[ℝ] F) ≤
      LinearMap.range (B : G →ₗ[ℝ] F) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨c • C x, by simp⟩

end ScoreExp

open ScoreExp

/-- The rank limit in the proof of `thm:score-exp` (Polynomial score arguments). Let `P_ℓ` be
score polynomials. If the Jacobian of `x ↦ (P_ℓ(q_i · k_j))_ℓ` has rank at most `r` on a nonempty
open set of inputs, then at every input `(Q, K)` the Jacobian of the linear parts
`(Q, K) ↦ (p_{C_ℓ}(Q, K))_ℓ`, with `C_ℓ = linCoeff P_ℓ`, has rank at most `r`.

The minors of the first Jacobian are analytic and vanish on the open set, so the rank bound holds
everywhere. For `t ≠ 0`, the map `t⁻¹ P(tQ, K)` has the same Jacobian rank bound, and its
Jacobian tends to the Jacobian of the linear parts as `t → 0`. -/
theorem linCoeff_rank_le {n d L r : ℕ} (P : Fin L → MvPolynomial (Fin n × Fin n) ℝ)
    {U : Set (Coord n d → ℝ)} (hU : IsOpen U) (hne : U.Nonempty)
    (h : ∀ x ∈ U, finrank ℝ (LinearMap.range
      (fderiv ℝ (fun x (ℓ : Fin L) => eval x (scoreSubst n d (P ℓ))) x :
        (Coord n d → ℝ) →ₗ[ℝ] (Fin L → ℝ))) ≤ r)
    (y : QKInputs n d) :
    finrank ℝ (LinearMap.range
      (fderiv ℝ (fun y (ℓ : Fin L) => scoreForm (linCoeff (P ℓ)) y) y :
        QKInputs n d →ₗ[ℝ] (Fin L → ℝ))) ≤ r := by
  set F : (Coord n d → ℝ) → Fin L → ℝ := fun x ℓ => eval x (scoreSubst n d (P ℓ))
  have hFan : AnalyticOnNhd ℝ F Set.univ :=
    AnalyticOnNhd.pi fun ℓ => AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℝ) _
  have hglob := finrank_range_fderiv_le hFan hU hne h
  obtain ⟨N, hN⟩ : ∃ N, ∀ ℓ, (P ℓ).totalDegree < N + 2 :=
    ⟨∑ ℓ, (P ℓ).totalDegree, fun ℓ => by
      have := Finset.single_le_sum (f := fun ℓ => (P ℓ).totalDegree)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ ℓ)
      omega⟩
  set D : ℕ → QKInputs n d →L[ℝ] (Fin L → ℝ) := fun k => fderiv ℝ (homogPart P k) y
  have hdiff := differentiable_homogPart (d := d) P
  have hD0 : D 0 = 0 := by
    simp only [D, homogPart_zero]
    exact fderiv_const_apply _
  have hD1 : D 1 = fderiv ℝ (fun y (ℓ : Fin L) => scoreForm (linCoeff (P ℓ)) y) y := by
    simp only [D, homogPart_one]
  have hexp : ∀ t : ℝ, (fun z => F (embedQK t z)) =
      fun z => ∑ k ∈ Finset.range (N + 2), t ^ k • homogPart P k z := by
    intro t
    funext z ℓ
    simp only [F, eval_embedQK_scoreSubst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      homogPart]
    exact eval_smul_eq_sum (P ℓ) (hN ℓ) t (fullScores z)
  have hderiv : ∀ t : ℝ, fderiv ℝ (fun z => F (embedQK t z)) y =
      ∑ k ∈ Finset.range (N + 2), t ^ k • D k := by
    intro t
    rw [hexp t, fderiv_fun_sum (A := fun k z => t ^ k • homogPart P k z)
      fun k _ => (hdiff k y).const_smul (t ^ k)]
    exact Finset.sum_congr rfl fun k _ => fderiv_fun_const_smul (hdiff k y) _
  have hcomp : ∀ t : ℝ, fderiv ℝ (fun z => F (embedQK t z)) y =
      (fderiv ℝ F (embedQK t y)).comp (embedQK t) := by
    intro t
    have := fderiv_comp (𝕜 := ℝ) y (hFan (embedQK t y) (Set.mem_univ _)).differentiableAt
      (embedQK t).differentiableAt
    rw [(embedQK t).fderiv] at this
    exact this
  rw [← hD1]
  refine finrank_range_le_of_tendsto
    (A := fun t : ℝ => t⁻¹ • ∑ k ∈ Finset.range (N + 2), t ^ k • D k) ?_ ?_
  · have hcont : Continuous fun t : ℝ => ∑ k ∈ Finset.range N, t ^ (k + 1) • D (k + 2) + D 1 :=
      (continuous_finsetSum _ fun k _ => (continuous_pow (k + 1)).smul continuous_const).add
        continuous_const
    have h0 : ∑ k ∈ Finset.range N, (0 : ℝ) ^ (k + 1) • D (k + 2) + D 1 = D 1 := by
      simp
    have hlim := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    rw [h0] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ht
    rw [Finset.sum_range_succ', Finset.sum_range_succ', hD0, smul_zero, add_zero, smul_add,
      Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul]
      congr 1
      field_simp
      ring
    · rw [smul_smul, pow_one, inv_mul_cancel₀ ht', one_smul]
  · intro t _
    rw [← hderiv t, hcomp t]
    calc finrank ℝ (LinearMap.range ((t⁻¹ • (fderiv ℝ F (embedQK t y)).comp (embedQK t) :
          QKInputs n d →L[ℝ] (Fin L → ℝ)) : QKInputs n d →ₗ[ℝ] (Fin L → ℝ)))
        ≤ finrank ℝ (LinearMap.range (fderiv ℝ F (embedQK t y) :
          (Coord n d → ℝ) →ₗ[ℝ] (Fin L → ℝ))) :=
          Submodule.finrank_mono (range_smul_comp_le _ _ _)
      _ ≤ r := hglob _

namespace ScoreExp

theorem ratioExponent_eq_scoreSubst {m d : ℕ} (i j : Fin (m + 1)) :
    ratioExponent (d := d) i j =
      scoreSubst (m + 1) d (X (i, j) - X (i, Fin.last m)) := by
  simp [ratioExponent, scoreSubst, scorePoly, mul_sub, Finset.sum_sub_distrib]

theorem linCoeff_X_sub_X {m : ℕ} (i j : Fin (m + 1)) :
    linCoeff (X (i, j) - X (i, Fin.last m) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℝ) =
      Matrix.single i j 1 - Matrix.single i (Fin.last m) 1 := by
  ext a b
  simp only [linCoeff_apply, coeff_sub, coeff_X, Finsupp.single_left_inj one_ne_zero,
    Prod.mk.injEq, Matrix.sub_apply, Matrix.single_apply]

theorem constantCoeff_scoreSubst {n d : ℕ} (p : MvPolynomial (Fin n × Fin n) ℝ) :
    constantCoeff (scoreSubst n d p) = constantCoeff p := by
  rw [← eval_zero, eval_scoreSubst, ← eval_zero]
  congr 2
  funext ij
  simp [scorePoly]

end ScoreExp

open ScoreExp

/-- The linear parts in the proof of `thm:score-exp` (Polynomial score arguments), the step that
takes the coefficient of `t` after replacing `Q` by `tQ`. If the centred score polynomial
`q_i · (k_j - k_n)` is a linear combination `∑ c_ℓ P_ℓ(q · k)` of substituted score polynomials,
then the centred coefficient matrix `E_{ij} - E_{in}` is the same combination of the linear-part
matrices `linCoeff P_ℓ`. The integer coefficients produced by `lem:character` are a special case.
No condition on the constant terms is needed, since constant terms do not affect `linCoeff`. -/
theorem centred_eq_sum_linCoeff {m d L : ℕ} (hd : 0 < d)
    (P : Fin L → MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℝ) (c : Fin L → ℝ) (i j : Fin (m + 1))
    (h : ratioExponent (d := d) i j = ∑ ℓ, c ℓ • scoreSubst (m + 1) d (P ℓ)) :
    Matrix.single i j 1 - Matrix.single i (Fin.last m) 1 = ∑ ℓ, c ℓ • linCoeff (P ℓ) := by
  rw [← linCoeff_X_sub_X, ← linCoeff_sum]
  apply linCoeff_eq_of_scoreSubst_eq hd
  rw [← ratioExponent_eq_scoreSubst, h, map_sum]
  simp only [map_smul]

/-- The centred matrices of `thm:score-exp` lie in the span of the linear parts: if every centred
score polynomial `q_i · (k_j - k_n)` lies in the real span of the substituted score polynomials,
then every `E_{ij} - E_{in}` lies in the span of the matrices `linCoeff P_ℓ`. -/
theorem centred_mem_span_linCoeff {m d L : ℕ} (hd : 0 < d)
    (P : Fin L → MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℝ) (i j : Fin (m + 1))
    (h : ratioExponent (d := d) i j ∈
      Submodule.span ℝ (Set.range fun ℓ => scoreSubst (m + 1) d (P ℓ))) :
    Matrix.single i j 1 - Matrix.single i (Fin.last m) 1 ∈
      Submodule.span ℝ (Set.range fun ℓ => linCoeff (P ℓ)) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp h
  rw [centred_eq_sum_linCoeff hd P c i j hc.symm]
  exact (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨c, rfl⟩

namespace ScoreExp

/-- The `n(n-1)` centred matrices `E_{ij} - E_{in}` (`j < n`) are linearly independent. -/
theorem linearIndependent_centred {m : ℕ} :
    LinearIndependent ℝ (fun ij : Fin (m + 1) × Fin m =>
      (Matrix.single ij.1 ij.2.castSucc 1 - Matrix.single ij.1 (Fin.last m) 1 :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  rintro g hg ⟨a, b⟩
  have h := congrFun (congrFun hg a) b.castSucc
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply,
    Fin.castSucc_inj, smul_eq_mul, Matrix.zero_apply] at h
  rw [Finset.sum_eq_single (a, b)] at h
  · simpa [(Fin.castSucc_lt_last b).ne'] using h
  · rintro ⟨i, j⟩ _ hij
    have hl : ¬ (Fin.last m = b.castSucc) := (Fin.castSucc_lt_last b).ne'
    by_cases hi : i = a
    · subst hi
      have hj : ¬ j = b := fun h => hij (by rw [h])
      simp [hj, hl]
    · simp [hi]
  · simp

theorem scoreForm_sum_smul {n d L : ℕ} (a : Fin L → ℝ) (C : Fin L → Matrix (Fin n) (Fin n) ℝ)
    (y : QKInputs n d) : scoreForm (∑ ℓ, a ℓ • C ℓ) y = ∑ ℓ, a ℓ * scoreForm (C ℓ) y := by
  let f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun C => scoreForm C y
      map_add' := fun C C' => by simp [scoreForm, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c C => by simp [scoreForm, Finset.mul_sum, mul_assoc] }
  have h := map_sum f (fun ℓ => a ℓ • C ℓ) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h

theorem differentiable_scoreForms {n d L : ℕ} (C : Fin L → Matrix (Fin n) (Fin n) ℝ) :
    Differentiable ℝ (fun (y : QKInputs n d) (ℓ : Fin L) => scoreForm (C ℓ) y) := by
  unfold scoreForm
  fun_prop

/-- Passing to matrices in the span of a family cannot raise the Jacobian rank of the score
forms. -/
theorem finrank_range_fderiv_scoreForms_le {n d B L : ℕ} (C : Fin B → Matrix (Fin n) (Fin n) ℝ)
    (C' : Fin L → Matrix (Fin n) (Fin n) ℝ) (hC : ∀ b, C b ∈ Submodule.span ℝ (Set.range C'))
    (y : QKInputs n d) :
    finrank ℝ (LinearMap.range (fderiv ℝ (fun y (b : Fin B) => scoreForm (C b) y) y :
        QKInputs n d →ₗ[ℝ] (Fin B → ℝ))) ≤
      finrank ℝ (LinearMap.range (fderiv ℝ (fun y (ℓ : Fin L) => scoreForm (C' ℓ) y) y :
        QKInputs n d →ₗ[ℝ] (Fin L → ℝ))) := by
  have hC' : ∀ b, ∃ a : Fin L → ℝ, ∑ ℓ, a ℓ • C' ℓ = C b := fun b =>
    (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hC b)
  choose a ha using hC'
  let A : (Fin L → ℝ) →L[ℝ] (Fin B → ℝ) :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin (Matrix.of a))
  set g : QKInputs n d → Fin L → ℝ := fun y ℓ => scoreForm (C' ℓ) y
  have hfun : (fun y (b : Fin B) => scoreForm (C b) y) = fun y => A (g y) := by
    funext y b
    simp only [A, g, LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, Matrix.of_apply, ← ha b, scoreForm_sum_smul]
  have hd : fderiv ℝ (fun y => A (g y)) y = A.comp (fderiv ℝ g y) :=
    (A.hasFDerivAt.comp y (differentiable_scoreForms C' y).hasFDerivAt).fderiv
  rw [hfun, hd, ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp]
  exact Submodule.finrank_map_le _ _

/-- The dimension of a finite supremum of subspaces is at most the sum of their dimensions. -/
theorem finrank_iSup_le_sum {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {e : ℕ} (W : Fin e → Submodule ℝ V) :
    finrank ℝ (⨆ t, W t : Submodule ℝ V) ≤ ∑ t, finrank ℝ (W t) := by
  let b : (Σ t, Fin (finrank ℝ (W t))) → V := fun x => (Module.finBasis ℝ (W x.1) x.2 : V)
  have hle : (⨆ t, W t : Submodule ℝ V) ≤ Submodule.span ℝ (Set.range b) := by
    refine iSup_le fun t v hv => ?_
    have h1 := (Module.finBasis ℝ (W t)).mem_span (⟨v, hv⟩ : W t)
    have h2 := Submodule.apply_mem_span_image_of_mem_span (W t).subtype h1
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨⟨t, k⟩, rfl⟩
  calc finrank ℝ (⨆ t, W t : Submodule ℝ V) ≤ finrank ℝ (Submodule.span ℝ (Set.range b)) :=
        Submodule.finrank_mono hle
    _ ≤ Fintype.card (Σ t, Fin (finrank ℝ (W t))) := finrank_range_le_card b
    _ = ∑ t, finrank ℝ (W t) := by simp

/-- The counting at the end of `cor:pair-cover`, with the per-epoch dimension bound `3M²/d²`:
from `n(n-1) ≤ e · 3M²/d²`, `e ≤ I/M + 1` and `nd ≤ I`, it follows that
`(nd + n²d²/M)/16 ≤ I`. -/
theorem count_arith {N D M e I : ℝ} (hD : 1 ≤ D) (hM : D ^ 2 ≤ M) (hN : 2 ≤ N)
    (hcov : N * (N - 1) ≤ e * (3 * M ^ 2 / D ^ 2)) (he : e ≤ I / M + 1) (hI : N * D ≤ I) :
    (N * D + N ^ 2 * D ^ 2 / M) / 16 ≤ I := by
  have hD0 : 0 < D := by linarith
  have hM0 : 0 < M := by nlinarith
  have hND : 0 < N * D := by positivity
  -- `eq:span-io`: `I ≥ n(n-1)d²/(3M) - M`.
  have hcov' : N * (N - 1) * D ^ 2 ≤ 3 * (e * M ^ 2) := by
    have := mul_le_mul_of_nonneg_right hcov (sq_nonneg D)
    rwa [show e * (3 * M ^ 2 / D ^ 2) * D ^ 2 = 3 * (e * M ^ 2) by field_simp] at this
  have heM : e * M ^ 2 ≤ I * M + M ^ 2 := by
    have := mul_le_mul_of_nonneg_right he (sq_nonneg M)
    rwa [show (I / M + 1) * M ^ 2 = I * M + M ^ 2 by field_simp] at this
  have hspan : N * (N - 1) * D ^ 2 ≤ 3 * (I * M) + 3 * M ^ 2 := by linarith
  have hhalf : N ^ 2 * D ^ 2 ≤ 2 * (N * (N - 1) * D ^ 2) := by
    have : N ^ 2 ≤ 2 * (N * (N - 1)) := by nlinarith
    nlinarith [sq_nonneg D]
  have hA : N ^ 2 * D ^ 2 / M ≤ 15 * I := by
    rw [div_le_iff₀ hM0]
    rcases le_or_gt (8 * M) (N * D) with h8 | h8
    · -- `M ≤ nd/8`, so `M² ≤ n²d²/64`.
      have hM2 : 64 * M ^ 2 ≤ N ^ 2 * D ^ 2 := by nlinarith
      nlinarith
    · -- `M > nd/8`, so `n²d²/M < 8nd ≤ 8I`.
      nlinarith
  linarith

end ScoreExp

open ScoreExp

/-- **Polynomial score arguments** (`thm:score-exp`), the counting part. Let `n = m + 1 ≥ 2`,
`d ≥ 2` and `d² ≤ M`, and let `U` be a nonempty connected open set of inputs. Take `e` epochs.
In epoch `t` the exponential arguments, with their constant terms removed, are `p t ℓ (q · k)`
for score polynomials `p t ℓ` with zero constant coefficient. Assume:

* (a) in each epoch, the Jacobian of `x ↦ (p t ℓ (q · k))_ℓ` has rank at most `2M` on `U`;
* (b) each centred ratio `R_{ij} = e^{q_i · (k_j - k_n)}` with `j < n` lies in the field
  generated over `F = ℝ(Q, K, V)` by all the exponentials `e^{p t ℓ (q · k)}`, inside the field
  of analytic functions on `U`;
* (c) `e ≤ I/M + 1` (`eq:epochs`) and `nd ≤ I` (the output stores).

Then `(nd + n²d²/M)/16 ≤ I`.

Facts (a) and (b) are derived in the paper's proof from the program on its open execution path:
the arguments of an epoch are computed from at most `2M` incoming values, and every computed value
lies in `F₀(e^{p_1}, …, e^{p_L})`, so the output derivatives lie there and hence so do the
`R_{ij}`. Here they are hypotheses. -/
theorem score_exp_io_lower_bound {m d M e I : ℕ} (hm : 1 ≤ m) (hd : 2 ≤ d) (hM : d ^ 2 ≤ M)
    (U : Set (Coord (m + 1) d → ℝ)) [Fact (IsOpen U)] [Fact (IsConnected U)]
    {L : Fin e → ℕ} (p : ∀ t, Fin (L t) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℝ)
    (hp : ∀ t ℓ, constantCoeff (p t ℓ) = 0)
    (hrank : ∀ t, ∀ x ∈ U, finrank ℝ (LinearMap.range
      (fderiv ℝ (fun x (ℓ : Fin (L t)) => eval x (scoreSubst (m + 1) d (p t ℓ))) x :
        (Coord (m + 1) d → ℝ) →ₗ[ℝ] (Fin (L t) → ℝ))) ≤ 2 * M)
    (hratio : ∀ (i : Fin (m + 1)) (j : Fin m), Main.ratioElem U i j.castSucc ∈
      IntermediateField.adjoin (FractionRing (MvPolynomial (Coord (m + 1) d) ℝ))
        (⋃ t, Set.range fun ℓ => expElem U (scoreSubst (m + 1) d (p t ℓ))))
    (he : (e : ℝ) ≤ I / M + 1) (hI : (m + 1) * d ≤ I) :
    (((m + 1 : ℝ) * d) + (m + 1 : ℝ) ^ 2 * (d : ℝ) ^ 2 / M) / 16 ≤ I := by
  classical
  have hd0 : 0 < d := by omega
  set F := FractionRing (MvPolynomial (Coord (m + 1) d) ℝ)
  -- Collect the exponential arguments of all epochs into one family.
  let eqv : (Σ t, Fin (L t)) ≃ Fin (∑ t, L t) := finSigmaFinEquiv
  let q' : (Σ t, Fin (L t)) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℝ := fun x => p x.1 x.2
  let q : Fin (∑ t, L t) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℝ := fun k => q' (eqv.symm k)
  have hrange : (⋃ t, Set.range fun ℓ => expElem U (scoreSubst (m + 1) d (p t ℓ))) =
      Set.range fun k => expElem U (scoreSubst (m + 1) d (q k)) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_range]
    constructor
    · rintro ⟨t, ℓ, rfl⟩
      refine ⟨eqv ⟨t, ℓ⟩, ?_⟩
      change expElem U (scoreSubst (m + 1) d (q' (eqv.symm (eqv ⟨t, ℓ⟩)))) = _
      rw [Equiv.symm_apply_apply]
    · rintro ⟨k, rfl⟩
      exact ⟨(eqv.symm k).1, (eqv.symm k).2, rfl⟩
  -- The span of the linear parts of one epoch.
  let W : Fin e → Submodule ℝ (Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :=
    fun t => Submodule.span ℝ (Set.range fun ℓ => linCoeff (p t ℓ))
  -- `lem:character` and the linear parts: every centred matrix lies in the combined span.
  have hcent : ∀ ij : Fin (m + 1) × Fin m,
      (Matrix.single ij.1 ij.2.castSucc 1 - Matrix.single ij.1 (Fin.last m) 1 :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∈ ⨆ t, W t := by
    rintro ⟨i, j⟩
    have hmem : expElem U (ratioExponent i j.castSucc) ∈ IntermediateField.adjoin F
        (Set.range fun k => expElem U (scoreSubst (m + 1) d (q k))) := by
      rw [← ratioElem_eq_expElem, ← hrange]
      exact hratio i j
    obtain ⟨z, hz⟩ := exp_mem_adjoin_exp U (fun k => scoreSubst (m + 1) d (q k))
      (ratioExponent i j.castSucc)
      (fun k => by rw [constantCoeff_scoreSubst]; exact hp _ _)
      (by rw [ratioExponent_eq_scoreSubst, constantCoeff_scoreSubst]; simp) hmem
    rw [centred_eq_sum_linCoeff hd0 q (fun k => (z k : ℝ)) i j.castSucc hz]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    exact Submodule.mem_iSup_of_mem (eqv.symm k).1
      (Submodule.subset_span ⟨(eqv.symm k).2, rfl⟩)
  have hlow : (m + 1) * m ≤ finrank ℝ (⨆ t, W t : Submodule ℝ _) := by
    have h1 := finrank_span_eq_card (linearIndependent_centred (m := m))
    have h2 := Submodule.finrank_mono (Submodule.span_le.mpr (by
      rintro _ ⟨ij, rfl⟩
      exact hcent ij) : Submodule.span ℝ (Set.range fun ij : Fin (m + 1) × Fin m =>
        (Matrix.single ij.1 ij.2.castSucc 1 - Matrix.single ij.1 (Fin.last m) 1 :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) ≤ ⨆ t, W t)
    simp only [Fintype.card_prod, Fintype.card_fin] at h1
    omega
  -- `lem:pair-rank` and the rank limit bound the dimension of each epoch's span.
  have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  have hM' : (d : ℝ) ^ 2 ≤ M := by exact_mod_cast hM
  have hepoch : ∀ t, (finrank ℝ (W t) : ℝ) ≤ 3 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2 := by
    intro t
    let b := Module.finBasis ℝ (W t)
    let C : Fin (finrank ℝ (W t)) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
      fun k => (b k : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    have hC : LinearIndependent ℝ C := b.linearIndependent.map' (W t).subtype (W t).ker_subtype
    have hrank' : ∀ y ∈ (Set.univ : Set (QKInputs (m + 1) d)), finrank ℝ (LinearMap.range
        (fderiv ℝ (fun y (k : Fin (finrank ℝ (W t))) => scoreForm (C k) y) y :
          QKInputs (m + 1) d →ₗ[ℝ] (Fin (finrank ℝ (W t)) → ℝ))) ≤ 2 * M := by
      intro y _
      refine (finrank_range_fderiv_scoreForms_le C _ (fun k => (b k).2) y).trans ?_
      exact linCoeff_rank_le (p t) (Fact.out : IsOpen U) (Fact.out : IsConnected U).nonempty
        (hrank t) y
    have hB := linearScore_rank_bound hd0 C hC isOpen_univ Set.univ_nonempty hrank'
    have h2M : 2 * (M : ℝ) ≤ 2 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2 := by
      rw [le_div_iff₀ hd2]
      nlinarith
    calc (finrank ℝ (W t) : ℝ) ≤ ((2 * M : ℕ) : ℝ) + ((2 * M : ℕ) : ℝ) ^ 2 / (4 * (d : ℝ) ^ 2) :=
          hB
      _ = 2 * M + (M : ℝ) ^ 2 / (d : ℝ) ^ 2 := by
          push_cast
          field_simp
          ring
      _ ≤ 3 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2 := by
          have : 3 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2 =
              2 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2 + (M : ℝ) ^ 2 / (d : ℝ) ^ 2 := by ring
          linarith
  -- Summing over epochs.
  have hcov : (m + 1 : ℝ) * ((m + 1 : ℝ) - 1) ≤ e * (3 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2) := by
    have h1 : ((m + 1 : ℝ) * m) ≤ ((∑ t, finrank ℝ (W t) : ℕ) : ℝ) := by
      exact_mod_cast hlow.trans (finrank_iSup_le_sum W)
    have h2 : ((∑ t, finrank ℝ (W t) : ℕ) : ℝ) ≤ ∑ _t : Fin e, 3 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2 := by
      push_cast
      exact Finset.sum_le_sum fun t _ => hepoch t
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  have hm2 : (2 : ℝ) ≤ m + 1 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  exact count_arith hd1 hM' hm2 hcov he (by exact_mod_cast hI)

end ExactAttention
