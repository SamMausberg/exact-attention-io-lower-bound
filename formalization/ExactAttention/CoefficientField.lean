import ExactAttention.ExpPoly

/-!
# The coefficient field

This file covers `prop:attention-field`. Exact attention (`eq:attention`) is defined for real
matrices `Q K V : Fin n → Fin d → ℝ`, with rows indexed by `Fin n`. We write `n = m + 1`, so the
last key is `Fin.last m` and the indices `j < n` of `eq:target` are `Fin.castSucc j` with
`j : Fin m`. The ratio `R i j = exp (q_i · (k_j - k_n))` is defined for every `j : Fin (m + 1)`,
and equals `1` for the last index.

For the statements about polynomials, an input is a point `x : Coord n d → ℝ` with one coordinate
for each entry of `Q`, `K` and `V`. Polynomial coefficients therefore range over `ℝ[Q, K, V]`,
whose fraction field is the field `F₀` of the paper.

We prove that `Y` is linear in `V` with `∂Y_{il}/∂V_{jl} = A_{ij}`, that `A_{ij}/A_{in} = R_{ij}`,
that `Y` is the stated rational expression in `R` and `V`, that every input partial derivative of
`R_{ij}` is a polynomial times `R_{ij}`, and that the `n(n-1)` ratios are algebraically
independent over `ℝ[Q, K, V]` on every nonempty open set of inputs.

The equality `F₀(DY) = 𝒯` is stated in the paper inside a field of analytic functions, which we do
not construct. We prove its two inclusions as statements about functions: each `R_{ij}` is a
quotient of two entries of `DY`, and each entry of `DY` equals `N / D` for fixed polynomials `N`
and `D` in the inputs and the ratios, with `D` nowhere zero. The second inclusion rests on the
fact that polynomials in the inputs and in exponentials of polynomials are closed under input
differentiation (`CoefficientField.hasDerivAt_eval_expEval`). The value `τ₁(Y) = n(n-1)`, which
needs transcendence degrees of function fields, is not formalized.
-/

open MvPolynomial Filter Topology

namespace ExactAttention

namespace CoefficientField

variable {n m d : ℕ}

/-- The kernel `W_{ij} = exp (q_i · k_j)` of `eq:attention`. -/
noncomputable def attnKernel (Q K : Fin n → Fin d → ℝ) (i j : Fin n) : ℝ :=
  Real.exp (∑ l, Q i l * K j l)

/-- The attention weights `A_{ij} = W_{ij} / ∑_h W_{ih}` of `eq:attention`. -/
noncomputable def attnWeight (Q K : Fin n → Fin d → ℝ) (i j : Fin n) : ℝ :=
  attnKernel Q K i j / ∑ h, attnKernel Q K i h

/-- The output `Y = A V` of exact attention, `eq:attention`. -/
noncomputable def attnOutput (Q K V : Fin n → Fin d → ℝ) (i : Fin n) (l : Fin d) : ℝ :=
  ∑ j, attnWeight Q K i j * V j l

/-- The centred ratio `R_{ij} = exp (q_i · (k_j - k_n))` of `eq:target`. It is defined for every
`j`, and `R_{in} = 1`. -/
noncomputable def attnRatio (Q K : Fin (m + 1) → Fin d → ℝ) (i j : Fin (m + 1)) : ℝ :=
  Real.exp (∑ l, Q i l * (K j l - K (Fin.last m) l))

/-- The input coordinates: the entries `Q i l`, `K j l` and `V j l`. -/
inductive Coord (n d : ℕ) : Type
  | q (i : Fin n) (l : Fin d)
  | k (j : Fin n) (l : Fin d)
  | v (j : Fin n) (l : Fin d)
  deriving DecidableEq, Fintype

/-- The query matrix of an input point. -/
def qMat (x : Coord n d → ℝ) : Fin n → Fin d → ℝ := fun i l => x (.q i l)

/-- The key matrix of an input point. -/
def kMat (x : Coord n d → ℝ) : Fin n → Fin d → ℝ := fun j l => x (.k j l)

/-- The value matrix of an input point. -/
def vMat (x : Coord n d → ℝ) : Fin n → Fin d → ℝ := fun j l => x (.v j l)

/-- The exponent `q_i · (k_j - k_n)` of `R_{ij}` as a polynomial in the inputs. -/
noncomputable def ratioExponent (i j : Fin (m + 1)) : MvPolynomial (Coord (m + 1) d) ℝ :=
  ∑ l, X (.q i l) * (X (.k j l) - X (.k (Fin.last m) l))

theorem attnRatio_eq_exp_eval (x : Coord (m + 1) d → ℝ) (i j : Fin (m + 1)) :
    attnRatio (qMat x) (kMat x) i j = Real.exp (eval x (ratioExponent i j)) := by
  simp [attnRatio, ratioExponent, qMat, kMat]

theorem attnRatio_last (Q K : Fin (m + 1) → Fin d → ℝ) (i : Fin (m + 1)) :
    attnRatio Q K i (Fin.last m) = 1 := by
  simp [attnRatio]

theorem attnKernel_pos (Q K : Fin n → Fin d → ℝ) (i j : Fin n) : 0 < attnKernel Q K i j :=
  Real.exp_pos _

theorem attnKernel_eq_ratio_mul (Q K : Fin (m + 1) → Fin d → ℝ) (i j : Fin (m + 1)) :
    attnKernel Q K i j = attnRatio Q K i j * attnKernel Q K i (Fin.last m) := by
  rw [attnKernel, attnRatio, attnKernel, ← Real.exp_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- Partial derivative of a polynomial along one coordinate. -/
theorem hasDerivAt_eval_update {σ : Type*} [DecidableEq σ] (x : σ → ℝ) (v : σ)
    (f : MvPolynomial σ ℝ) :
    HasDerivAt (fun t => eval (Function.update x v t) f) (eval x (pderiv v f)) (x v) := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const (x v) a
  | add f g hf hg =>
    simp only [map_add]
    exact hf.add hg
  | mul_X f w hf =>
    have hw : HasDerivAt (fun t => Function.update x v t w) ((Pi.single v (1 : ℝ) : σ → ℝ) w)
        (x v) := by
      by_cases h : w = v
      · subst h
        simpa using hasDerivAt_id' (x w)
      · simpa [Function.update_of_ne h, Pi.single_apply, h] using hasDerivAt_const (x v) (x w)
    have := hf.mul hw
    simp only [Function.update_eq_self] at this
    convert this using 1
    · ext t
      simp
    · by_cases h : w = v <;> simp [Derivation.leibniz, pderiv_X, h] <;> ring

section Closure

variable {ι σ : Type*} [DecidableEq σ] (s : ι → MvPolynomial σ ℝ)

/-- The values of the exponentials `e^{s a}` and of the inputs at the point `x`. -/
noncomputable def expEval (x : σ → ℝ) : ι ⊕ σ → ℝ :=
  Sum.elim (fun a => Real.exp (eval x (s a))) x

/-- Differentiation along the input coordinate `v`, acting on polynomials in the exponentials
`e^{s a}` and the inputs. It sends `e^{s a}` to `e^{s a} ∂s_a/∂x_v`. -/
noncomputable def expDeriv (v : σ) :
    Derivation ℝ (MvPolynomial (ι ⊕ σ) ℝ) (MvPolynomial (ι ⊕ σ) ℝ) :=
  mkDerivation ℝ (Sum.elim (fun a => X (Sum.inl a) * rename Sum.inr (pderiv v (s a)))
    (fun c => if c = v then 1 else 0))

/-- Polynomials in the inputs and in the exponentials `e^{s a}` are closed under input
differentiation: the partial derivative is computed by `expDeriv`. -/
theorem hasDerivAt_eval_expEval (x : σ → ℝ) (v : σ) (G : MvPolynomial (ι ⊕ σ) ℝ) :
    HasDerivAt (fun t => eval (expEval s (Function.update x v t)) G)
      (eval (expEval s x) (expDeriv s v G)) (x v) := by
  induction G using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const (x v) a
  | add f g hf hg =>
    simp only [map_add]
    exact hf.add hg
  | mul_X f c hf =>
    have hc : HasDerivAt (fun t => expEval s (Function.update x v t) c)
        (eval (expEval s x) (expDeriv s v (X c))) (x v) := by
      rcases c with a | w
      · have := (hasDerivAt_eval_update x v (s a)).exp
        rw [Function.update_eq_self] at this
        simpa [expEval, expDeriv, mkDerivation_X, eval_rename] using this
      · by_cases h : w = v
        · subst h
          simpa [expEval, expDeriv, mkDerivation_X] using hasDerivAt_id' (x w)
        · simpa [expEval, expDeriv, mkDerivation_X, h, Function.update_of_ne h] using
            hasDerivAt_const (x v) (x w)
    have := hf.mul hc
    simp only [Function.update_eq_self] at this
    convert this using 1
    · ext t
      simp
    · simp only [Derivation.leibniz, map_add, smul_eq_mul, map_mul, eval_X]
      ring

end Closure

/-- The polynomial exponents of the ratios `R_{ij}`, `j < n`. -/
noncomputable abbrev ratioExponents :
    Fin (m + 1) × Fin m → MvPolynomial (Coord (m + 1) d) ℝ :=
  fun ij => ratioExponent ij.1 ij.2.castSucc

/-- The numerator `∑_{j<n} R_{ij} V_{jl} + V_{nl}` as a polynomial in the ratios and inputs. -/
noncomputable def outputNum (i : Fin (m + 1)) (l : Fin d) :
    MvPolynomial (Fin (m + 1) × Fin m ⊕ Coord (m + 1) d) ℝ :=
  ∑ j : Fin m, X (Sum.inl (i, j)) * X (Sum.inr (.v j.castSucc l)) +
    X (Sum.inr (.v (Fin.last m) l))

/-- The denominator `1 + ∑_{j<n} R_{ij}` as a polynomial in the ratios. -/
noncomputable def outputDen (i : Fin (m + 1)) :
    MvPolynomial (Fin (m + 1) × Fin m ⊕ Coord (m + 1) d) ℝ :=
  1 + ∑ j : Fin m, X (Sum.inl (i, j))

/-- The ratios `R_{ij}` (`j < n`) and the inputs at the point `x`. -/
noncomputable def ratiosAndInputs (x : Coord (m + 1) d → ℝ) :
    Fin (m + 1) × Fin m ⊕ Coord (m + 1) d → ℝ :=
  Sum.elim (fun ij => attnRatio (qMat x) (kMat x) ij.1 ij.2.castSucc) x

theorem expEval_ratioExponents (x : Coord (m + 1) d → ℝ) :
    expEval ratioExponents x = ratiosAndInputs x := by
  ext (ij | c)
  · simp [expEval, ratiosAndInputs, attnRatio_eq_exp_eval]
  · rfl

theorem eval_outputDen_pos (x : Coord (m + 1) d → ℝ) (i : Fin (m + 1)) :
    0 < eval (ratiosAndInputs x) (outputDen (d := d) i) := by
  simp only [outputDen, map_add, map_one, map_sum, eval_X, ratiosAndInputs, Sum.elim_inl]
  exact add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun j _ => (Real.exp_pos _).le)

end CoefficientField

open CoefficientField

variable {n m d : ℕ}

/-- `prop:attention-field` (The coefficient field): the output `Y` of exact attention is linear
in `V`. -/
theorem attnOutput_isLinearMap (Q K : Fin n → Fin d → ℝ) : IsLinearMap ℝ (attnOutput Q K) where
  map_add V V' := by
    ext i l
    simp [attnOutput, mul_add, Finset.sum_add_distrib]
  map_smul c V := by
    ext i l
    simp only [attnOutput, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- `prop:attention-field` (The coefficient field): the partial derivative of `Y_{il}` with
respect to `V_{jl'}` is `A_{ij}` when `l' = l` and `0` otherwise. -/
theorem hasDerivAt_attnOutput_value (Q K V : Fin n → Fin d → ℝ) (i j : Fin n) (l l' : Fin d) :
    HasDerivAt (fun t => attnOutput Q K (Function.update V j (Function.update (V j) l' t)) i l)
      (if l' = l then attnWeight Q K i j else 0) (V j l') := by
  have h : ∀ j' ∈ (Finset.univ : Finset (Fin n)), HasDerivAt
      (fun t => attnWeight Q K i j' * Function.update V j (Function.update (V j) l' t) j' l)
      (if j' = j ∧ l' = l then attnWeight Q K i j' else 0) (V j l') := by
    intro j' _
    by_cases hj : j' = j
    · subst hj
      by_cases hl : l' = l
      · subst hl
        simpa using (hasDerivAt_id' (V j' l')).const_mul (attnWeight Q K i j')
      · simpa [hl, Function.update_of_ne (Ne.symm hl)] using
          hasDerivAt_const (V j' l') (attnWeight Q K i j' * V j' l)
    · simpa [hj, Function.update_of_ne hj] using
        hasDerivAt_const (V j l') (attnWeight Q K i j' * V j' l)
  convert HasDerivAt.fun_sum h using 1
  · rfl
  · by_cases hl : l' = l
    · simp [hl]
    · simp [hl]

/-- `prop:attention-field` (The coefficient field): `A_{ij} / A_{in} = R_{ij}`. -/
theorem attnWeight_div_last (Q K : Fin (m + 1) → Fin d → ℝ) (i j : Fin (m + 1)) :
    attnWeight Q K i j / attnWeight Q K i (Fin.last m) = attnRatio Q K i j := by
  have hS : (∑ h, attnKernel Q K i h) ≠ 0 :=
    (Finset.sum_pos (fun h _ => Real.exp_pos _) Finset.univ_nonempty).ne'
  rw [attnWeight, attnWeight, div_div_div_cancel_right₀ hS, attnKernel_eq_ratio_mul Q K i j,
    mul_div_assoc, div_self (attnKernel_pos Q K i _).ne', mul_one]

/-- `prop:attention-field` (The coefficient field): the output is a rational function of the
ratios `R_{ij}` (`j < n`) and of `V`, with denominator `1 + ∑_{j<n} R_{ij}`. -/
theorem attnOutput_eq_ratio (Q K V : Fin (m + 1) → Fin d → ℝ) (i : Fin (m + 1)) (l : Fin d) :
    attnOutput Q K V i l =
      (∑ j : Fin m, attnRatio Q K i j.castSucc * V j.castSucc l + V (Fin.last m) l) /
        (1 + ∑ j : Fin m, attnRatio Q K i j.castSucc) := by
  have hw := attnKernel_pos Q K i (Fin.last m)
  have hsum : ∑ h, attnKernel Q K i h =
      (∑ h, attnRatio Q K i h) * attnKernel Q K i (Fin.last m) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun h _ => attnKernel_eq_ratio_mul Q K i h
  have hpos : 0 < ∑ h, attnRatio Q K i h :=
    Finset.sum_pos (fun h _ => Real.exp_pos _) Finset.univ_nonempty
  have key : attnOutput Q K V i l = (∑ j, attnRatio Q K i j * V j l) / ∑ h, attnRatio Q K i h := by
    simp only [attnOutput, attnWeight, hsum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [attnKernel_eq_ratio_mul Q K i j]
    field_simp
  rw [key, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, attnRatio_last]
  ring

/-- `prop:attention-field` (The coefficient field): each partial derivative of `R_{ij}` with
respect to an input coordinate is a polynomial in the inputs times `R_{ij}`. The polynomial is the
partial derivative of the exponent `q_i · (k_j - k_n)`. -/
theorem hasDerivAt_attnRatio (x : Coord (m + 1) d → ℝ) (c : Coord (m + 1) d)
    (i j : Fin (m + 1)) :
    HasDerivAt
      (fun t => attnRatio (qMat (Function.update x c t)) (kMat (Function.update x c t)) i j)
      (eval x (pderiv c (ratioExponent i j)) * attnRatio (qMat x) (kMat x) i j) (x c) := by
  simp only [attnRatio_eq_exp_eval]
  rw [mul_comm]
  have := (hasDerivAt_eval_update x c (ratioExponent i j)).exp
  rwa [Function.update_eq_self] at this

/-- The exponents `q_i · (k_j - k_n)`, `j < n`, satisfy the hypothesis of `lem:independence`: the
monomial `Q_{i0} K_{j0}` occurs only in the exponent indexed by `(i, j)`. This is the first step of
the proof of `prop:attention-field`. -/
theorem ratioExponent_intCombNonconst (hd : 0 < d) :
    IntCombNonconst
      (fun ij : Fin (m + 1) × Fin m => ratioExponent (d := d) ij.1 ij.2.castSucc) := by
  intro c hc r h
  obtain ⟨⟨i, j⟩, hij⟩ : ∃ ij, c ij ≠ 0 := by
    by_contra! h'
    exact hc (funext h')
  set l₀ : Fin d := ⟨0, hd⟩
  -- Evaluate at the point where `Q_{i l₀} = K_{j l₀} = 1` and all other inputs vanish.
  let x : Coord (m + 1) d → ℝ := fun w => match w with
    | .q i' l => if i' = i ∧ l = l₀ then 1 else 0
    | .k j' l => if j' = j.castSucc ∧ l = l₀ then 1 else 0
    | .v _ _ => 0
  have hx : ∀ ij : Fin (m + 1) × Fin m,
      eval x (ratioExponent ij.1 ij.2.castSucc) = if ij = (i, j) then 1 else 0 := by
    rintro ⟨i', j'⟩
    have hlast : (Fin.last m : Fin (m + 1)) ≠ j.castSucc := (Fin.castSucc_lt_last j).ne'
    simp only [ratioExponent, map_sum, map_mul, map_sub, eval_X, x, hlast, false_and,
      ite_false, sub_zero, Fin.castSucc_inj, Prod.mk.injEq]
    rw [Finset.sum_eq_single l₀]
    · by_cases hi : i' = i <;> by_cases hj : j' = j <;> simp [hi, hj]
    · intro l _ hl
      simp [hl]
    · simp
  have hzero : ∀ ij : Fin (m + 1) × Fin m,
      eval 0 (ratioExponent (d := d) ij.1 ij.2.castSucc) = 0 := by
    intro ij
    simp [ratioExponent]
  have h0 := congrArg (eval 0) h
  have h1 := congrArg (eval x) h
  simp only [map_sum, smul_eval, eval_C, hzero, mul_zero, Finset.sum_const_zero] at h0
  simp only [map_sum, smul_eval, eval_C, hx, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h1
  rw [← h0] at h1
  exact hij (by exact_mod_cast h1)

/-- `prop:attention-field` (The coefficient field), independence of the ratios: for `d ≥ 1`, no
nonzero polynomial in the `n(n-1)` ratios `R_{ij}` (`j < n`), with coefficients in `ℝ[Q, K, V]`,
vanishes on a nonempty open set of inputs. -/
theorem attnRatio_relation_eq_zero (hd : 0 < d) {U : Set (Coord (m + 1) d → ℝ)}
    (hU : IsOpen U) (hne : U.Nonempty)
    (P : MvPolynomial (Fin (m + 1) × Fin m) (MvPolynomial (Coord (m + 1) d) ℝ))
    (hP : ∀ x ∈ U, eval (fun ij : Fin (m + 1) × Fin m => attnRatio (qMat x) (kMat x) ij.1
        ij.2.castSucc) (MvPolynomial.map (eval x) P) = 0) :
    P = 0 := by
  refine exp_poly_relation_eq_zero _ (ratioExponent_intCombNonconst hd) hU hne P fun x hx => ?_
  simpa only [attnRatio_eq_exp_eval] using hP x hx

/-- `prop:attention-field` (The coefficient field), independence of the ratios in the language of
`AlgebraicIndependent`: on a nonempty open set `U` of inputs, the ratios `R_{ij}` (`j < n`)
together with all input coordinates are algebraically independent over `ℝ` in the ring of real
functions on `U`. Hence the ratios are algebraically independent over `F₀ = ℝ(Q, K, V)`. -/
theorem attnRatio_algebraicIndependent (hd : 0 < d) {U : Set (Coord (m + 1) d → ℝ)}
    (hU : IsOpen U) (hne : U.Nonempty) :
    AlgebraicIndependent ℝ (Sum.elim
      (fun (ij : Fin (m + 1) × Fin m) (x : U) => attnRatio (qMat (x : Coord (m + 1) d → ℝ))
        (kMat (x : Coord (m + 1) d → ℝ)) ij.1 ij.2.castSucc)
      (fun c (x : U) => (x : Coord (m + 1) d → ℝ) c)) := by
  convert algebraicIndependent_exp_poly _ (ratioExponent_intCombNonconst hd) hU hne using 1
  ext (ij | c) x
  · simp [attnRatio_eq_exp_eval]
  · rfl

namespace CoefficientField

theorem attnOutput_eq_eval (x : Coord (m + 1) d → ℝ) (i : Fin (m + 1)) (l : Fin d) :
    attnOutput (qMat x) (kMat x) (vMat x) i l =
      eval (ratiosAndInputs x) (outputNum i l) / eval (ratiosAndInputs x) (outputDen i) := by
  rw [attnOutput_eq_ratio]
  simp [outputNum, outputDen, ratiosAndInputs, vMat]

end CoefficientField

/-- `prop:attention-field` (The coefficient field), the containment `𝒯 ⊆ F₀(DY)`: each ratio
`R_{ij}` is the quotient of the output derivatives `∂Y_{il}/∂V_{jl}` and `∂Y_{il}/∂V_{nl}`. -/
theorem attnRatio_eq_deriv_div_deriv (Q K V : Fin (m + 1) → Fin d → ℝ) (i j : Fin (m + 1))
    (l : Fin d) :
    attnRatio Q K i j =
      deriv (fun t => attnOutput Q K (Function.update V j (Function.update (V j) l t)) i l)
          (V j l) /
        deriv (fun t => attnOutput Q K (Function.update V (Fin.last m)
          (Function.update (V (Fin.last m)) l t)) i l) (V (Fin.last m) l) := by
  rw [(hasDerivAt_attnOutput_value Q K V i j l l).deriv,
    (hasDerivAt_attnOutput_value Q K V i (Fin.last m) l l).deriv]
  simp [attnWeight_div_last]

/-- `prop:attention-field` (The coefficient field), the containment `F₀(DY) ⊆ 𝒯`: the partial
derivative of each output entry with respect to each entry of `Q`, `K` or `V` is a rational
function of the inputs and of the ratios `R_{ij}` (`j < n`). The polynomials `N` and `D` do not
depend on the point, and the denominator never vanishes. -/
theorem attnOutput_deriv_mem_ratioField (i : Fin (m + 1)) (l : Fin d) (c : Coord (m + 1) d) :
    ∃ N D : MvPolynomial (Fin (m + 1) × Fin m ⊕ Coord (m + 1) d) ℝ, ∀ x : Coord (m + 1) d → ℝ,
      eval (ratiosAndInputs x) D ≠ 0 ∧
      HasDerivAt (fun t => attnOutput (qMat (Function.update x c t)) (kMat (Function.update x c t))
          (vMat (Function.update x c t)) i l)
        (eval (ratiosAndInputs x) N / eval (ratiosAndInputs x) D) (x c) := by
  refine ⟨expDeriv ratioExponents c (outputNum i l) * outputDen i -
      outputNum i l * expDeriv ratioExponents c (outputDen i), outputDen i ^ 2, fun x => ?_⟩
  have hden := eval_outputDen_pos x i
  refine ⟨by simp [hden.ne'], ?_⟩
  have hfun : (fun t => attnOutput (qMat (Function.update x c t)) (kMat (Function.update x c t))
      (vMat (Function.update x c t)) i l) = fun t =>
        eval (ratiosAndInputs (Function.update x c t)) (outputNum i l) /
          eval (ratiosAndInputs (Function.update x c t)) (outputDen i) := by
    funext t
    rw [attnOutput_eq_eval]
  rw [hfun]
  have hd :
      eval (expEval ratioExponents (Function.update x c (x c))) (outputDen (d := d) i) ≠ 0 := by
    rw [Function.update_eq_self, expEval_ratioExponents]
    exact hden.ne'
  have := (hasDerivAt_eval_expEval ratioExponents x c (outputNum i l)).fun_div
    (hasDerivAt_eval_expEval ratioExponents x c (outputDen i)) hd
  simp only [Function.update_eq_self, expEval_ratioExponents] at this
  convert this using 1
  rw [map_sub, map_mul, map_mul, map_pow]

end ExactAttention
