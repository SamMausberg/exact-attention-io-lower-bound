import ExactAttention.Defs
import ExactAttention.ExpPoly
import ExactAttention.Strassen

/-!
# The auxiliary vector of the bilinear prefix

This file covers the algebraic parts of `thm:bilinear-prefix` in `sec:bilinear`: the kernel
product `eq:kernel-product`, the leaf extraction `eq:extract-leaf`, and the hypothesis of
`lem:independence` for the exponent polynomials `u_{ar} z_{br}`, which gives the algebraic
independence behind `τ₁(g) = B² R` in the variables `Q, K`. The I/O and work bounds of
`eq:aux-io`, the field statements of `eq:aux-field`, and the containment of `𝒯` in the history
of an epoch partition are not formalized.

We take `d = 2 ^ k` and `n = B d`. The matrices `Q, K, V` have rows indexed by `Fin (B * 2 ^ k)`
and columns by `Fin (2 ^ k)`. Row `α` of block `a` is the global row `a d + α`, the zero-based
form of `(a - 1) d + α`, given by `finProdFinEquiv`. The forms `ℓ_r, m_r` and the coefficients
`c_{αβr}` are those of `ExactAttention.Strassen`. The exponent polynomials live in
`MvPolynomial` over the variables `inl (i, γ) = Q i γ` and `inr (j, γ) = K j γ`.
-/

namespace ExactAttention

open MvPolynomial Strassen

namespace BilinearPrefix

variable {k B : ℕ}

/-- Row `α` of block `a`, that is, the global row `a d + α`. -/
def row (a : Fin B) (α : Fin (2 ^ k)) : Fin (B * 2 ^ k) := finProdFinEquiv (a, α)

lemma row_eq_row_iff {a a' : Fin B} {α α' : Fin (2 ^ k)} :
    row a α = row a' α' ↔ a = a' ∧ α = α' := by
  rw [row, row, finProdFinEquiv.injective.eq_iff, Prod.mk.injEq]

/-- The `a`-th `d × d` block of rows of a `B d × d` matrix. -/
def block (Q : Matrix (Fin (B * 2 ^ k)) (Fin (2 ^ k)) ℝ) (a : Fin B) :
    Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ :=
  Matrix.of fun α γ => Q (row a α) γ

/-- The query form `u_{ar} = ℓ_r(Q^{(a)})` of `eq:forms`. -/
def qForm (Q : Matrix (Fin (B * 2 ^ k)) (Fin (2 ^ k)) ℝ) (a : Fin B) (r : Fin (7 ^ k)) : ℝ :=
  form (ellForm k r) (block Q a)

/-- The key form `z_{br} = m_r(K^{(b)})` of `eq:forms`. -/
def kForm (K : Matrix (Fin (B * 2 ^ k)) (Fin (2 ^ k)) ℝ) (b : Fin B) (r : Fin (7 ^ k)) : ℝ :=
  form (emForm k r) (block K b)

/-- The leaf exponential `E_{abr} = exp(u_{ar} z_{br})` of `eq:forms`. -/
noncomputable def leafExp (Q K : Matrix (Fin (B * 2 ^ k)) (Fin (2 ^ k)) ℝ) (a b : Fin B)
    (r : Fin (7 ^ k)) : ℝ :=
  Real.exp (qForm Q a r * kForm K b r)

/-- The marker `t_b`, the first entry of the first row of block `b` of `V`. -/
def marker (V : Matrix (Fin (B * 2 ^ k)) (Fin (2 ^ k)) ℝ) (b : Fin B) : ℝ := V (row b 0) 0

/-- The auxiliary vector `g_{ar} = ∑_b E_{abr} t_b` of `eq:aux-vector`. -/
noncomputable def aux (Q K V : Matrix (Fin (B * 2 ^ k)) (Fin (2 ^ k)) ℝ) (a : Fin B)
    (r : Fin (7 ^ k)) : ℝ :=
  ∑ b, leafExp Q K a b r * marker V b

private lemma exp_mul_intCast (x : ℝ) (n : ℤ) : Real.exp (n * x) = Real.exp x ^ n := by
  rw [mul_comm, Real.exp_mul, Real.rpow_intCast]

end BilinearPrefix

open BilinearPrefix

/-- Part of `thm:bilinear-prefix`, the kernel
product `eq:kernel-product`: for the query row `i = a d + α` and the key row `j = b d + β`, the
kernel `W_ij = exp(q_i · k_j)` is the product of the leaf exponentials `E_{abr}` raised to the
integer powers `c_{αβr}`. -/
theorem bilinearPrefix_kernel_product (Q K : Matrix (Fin (B * 2 ^ k)) (Fin (2 ^ k)) ℝ) (a b : Fin B)
    (α β : Fin (2 ^ k)) :
    Real.exp (Q (row a α) ⬝ᵥ K (row b β)) = ∏ r, leafExp Q K a b r ^ coef k α β r := by
  have hq : Q (row a α) ⬝ᵥ K (row b β) = (block Q a * (block K b).transpose) α β := by
    simp [dotProduct, Matrix.mul_apply, block]
  rw [hq, strassen_bilinear, Real.exp_sum]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [mul_assoc, exp_mul_intCast]
  rfl

namespace BilinearPrefix

private lemma form_add_smul {I : Type*} [Fintype I] (f : Matrix I I ℤ)
    (A C : Matrix I I ℝ) (s : ℝ) : form f (A + s • C) = form f A + s * form f C := by
  simp only [form, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma kForm_single (r : Fin (7 ^ k)) (b b' : Fin B) (κ : Fin (2 ^ k) × Fin (2 ^ k)) :
    kForm (Matrix.single (row b κ.1) κ.2 (1 : ℝ)) b' r =
      if b' = b then (emForm k r κ.1 κ.2 : ℝ) else 0 := by
  split_ifs with h
  · subst h
    have : block (Matrix.single (row b' κ.1) κ.2 (1 : ℝ)) b' = Matrix.single κ.1 κ.2 1 := by
      ext α γ
      simp [block, Matrix.single_apply, row_eq_row_iff]
    rw [kForm, this, form_single]
  · have : block (Matrix.single (row b κ.1) κ.2 (1 : ℝ)) b' = 0 := by
      ext α γ
      simp only [block, Matrix.of_apply, Matrix.single_apply, row_eq_row_iff, Matrix.zero_apply]
      refine ite_eq_right ?_
      rintro ⟨⟨h', -⟩, -⟩
      exact h h'.symm
    simp [kForm, this, form]

private lemma kForm_add_smul_single (K : Matrix (Fin (B * 2 ^ k)) (Fin (2 ^ k)) ℝ)
    (r : Fin (7 ^ k)) (b b' : Fin B) (κ : Fin (2 ^ k) × Fin (2 ^ k)) (s : ℝ) :
    kForm (K + s • Matrix.single (row b κ.1) κ.2 1) b' r =
      kForm K b' r + s * (if b' = b then (emForm k r κ.1 κ.2 : ℝ) else 0) := by
  rw [← kForm_single]
  have : block (K + s • Matrix.single (row b κ.1) κ.2 (1 : ℝ)) b' =
      block K b' + s • block (Matrix.single (row b κ.1) κ.2 1) b' := by
    ext α γ
    simp only [block, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply]
  rw [kForm, this, form_add_smul]
  rfl

end BilinearPrefix

/-- Part of `thm:bilinear-prefix`, leaf extraction
`eq:extract-leaf`: the partial derivative of `g_{ar}` along the key coordinate `K^{(b)}_κ` is
`u_{ar} β_r E_{abr} t_b`, where `β_r` is the coefficient of `κ` in `m_r`. The markers `t_b`
depend only on `V`. -/
theorem bilinearPrefix_hasDerivAt_aux (Q K V : Matrix (Fin (B * 2 ^ k)) (Fin (2 ^ k)) ℝ) (a b : Fin B)
    (r : Fin (7 ^ k)) (κ : Fin (2 ^ k) × Fin (2 ^ k)) :
    HasDerivAt (fun s : ℝ => aux Q (K + s • Matrix.single (row b κ.1) κ.2 1) V a r)
      (qForm Q a r * emForm k r κ.1 κ.2 * leafExp Q K a b r * marker V b) 0 := by
  set β : Fin B → ℝ := fun b' => if b' = b then (emForm k r κ.1 κ.2 : ℝ) else 0
  have hfun : (fun s : ℝ => aux Q (K + s • Matrix.single (row b κ.1) κ.2 1) V a r) =
      fun s => ∑ b', Real.exp (qForm Q a r * (kForm K b' r + s * β b')) * marker V b' := by
    funext s
    simp only [aux, leafExp, kForm_add_smul_single, β]
  rw [hfun]
  have hterm : ∀ b' ∈ (Finset.univ : Finset (Fin B)),
      HasDerivAt (fun s => Real.exp (qForm Q a r * (kForm K b' r + s * β b')) * marker V b')
        (Real.exp (qForm Q a r * (kForm K b' r + 0 * β b')) * (qForm Q a r * (1 * β b')) *
          marker V b') 0 := fun b' _ =>
    ((((hasDerivAt_id (0 : ℝ)).mul_const (β b')).const_add (kForm K b' r)).const_mul
      (qForm Q a r)).exp.mul_const (marker V b')
  refine (HasDerivAt.fun_sum hterm).congr_deriv ?_
  simp only [zero_mul, add_zero, one_mul, β, mul_ite, mul_zero, ite_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, leafExp]
  ring

/-- Part of `thm:bilinear-prefix`, the second half
of `eq:extract-leaf`: some key coordinate `κ` has a nonzero coefficient `β_r` in `m_r`, and
wherever `u_{ar} t_b ≠ 0` the leaf exponential `E_{abr}` is the partial derivative of `g_{ar}`
along `K^{(b)}_κ` divided by `u_{ar} β_r t_b`. -/
theorem bilinearPrefix_leaf_recovery (r : Fin (7 ^ k)) :
    ∃ κ : Fin (2 ^ k) × Fin (2 ^ k), emForm k r κ.1 κ.2 ≠ 0 ∧
      ∀ (Q K V : Matrix (Fin (B * 2 ^ k)) (Fin (2 ^ k)) ℝ) (a b : Fin B),
        qForm Q a r ≠ 0 → marker V b ≠ 0 →
        leafExp Q K a b r =
          deriv (fun s : ℝ => aux Q (K + s • Matrix.single (row b κ.1) κ.2 1) V a r) 0 /
            (qForm Q a r * emForm k r κ.1 κ.2 * marker V b) := by
  have hm := (strassen_forms_ne_zero k r).2
  obtain ⟨i, j, hij⟩ : ∃ i j, emForm k r i j ≠ 0 := by
    by_contra h
    refine hm (Matrix.ext fun i j => ?_)
    by_contra hij
    exact h ⟨i, j, hij⟩
  refine ⟨(i, j), hij, fun Q K V a b hu ht => ?_⟩
  rw [(bilinearPrefix_hasDerivAt_aux Q K V a b r (i, j)).deriv]
  have hβ : (emForm k r i j : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hij
  field_simp

namespace BilinearPrefix

/-- Variables of the exponent polynomials: `inl (i, γ)` is `Q i γ` and `inr (j, γ)` is `K j γ`. -/
abbrev QKVar (k B : ℕ) := (Fin (B * 2 ^ k) × Fin (2 ^ k)) ⊕ (Fin (B * 2 ^ k) × Fin (2 ^ k))

/-- The exponent polynomial `u_{ar} z_{br}` of the leaf exponential `E_{abr}`, indexed by
`(a, b, r)`. -/
noncomputable def expPoly (k B : ℕ) (x : Fin B × Fin B × Fin (7 ^ k)) :
    MvPolynomial (QKVar k B) ℝ :=
  form (ellForm k x.2.2) (Matrix.of fun α γ => X (Sum.inl (row x.1 α, γ))) *
    form (emForm k x.2.2) (Matrix.of fun β γ => X (Sum.inr (row x.2.1 β, γ)))

/-- The point of `QKVar` given by the matrices `Q` and `K`. -/
def qkPoint (Q K : Matrix (Fin (B * 2 ^ k)) (Fin (2 ^ k)) ℝ) : QKVar k B → ℝ :=
  Sum.elim (fun p => Q p.1 p.2) (fun p => K p.1 p.2)

lemma eval_expPoly (Q K : Matrix (Fin (B * 2 ^ k)) (Fin (2 ^ k)) ℝ)
    (x : Fin B × Fin B × Fin (7 ^ k)) :
    eval (qkPoint Q K) (expPoly k B x) = qForm Q x.1 x.2.2 * kForm K x.2.1 x.2.2 := by
  rw [expPoly, map_mul, eval_form (v := fun α γ => Sum.inl (row x.1 α, γ)),
    eval_form (v := fun β γ => Sum.inr (row x.2.1 β, γ))]
  rfl

/-- The exponential of `expPoly k B (a, b, r)` at `(Q, K)` is the leaf exponential `E_{abr}`. -/
lemma exp_eval_expPoly (Q K : Matrix (Fin (B * 2 ^ k)) (Fin (2 ^ k)) ℝ) (a b : Fin B)
    (r : Fin (7 ^ k)) :
    Real.exp (eval (qkPoint Q K) (expPoly k B (a, b, r))) = leafExp Q K a b r := by
  rw [eval_expPoly]
  rfl

private lemma isHomogeneous_form {σ : Type*} {I : Type*} [Fintype I] (f : Matrix I I ℤ)
    (v : I → I → σ) :
    (form f (Matrix.of fun i j => (X (v i j) : MvPolynomial σ ℝ))).IsHomogeneous 1 := by
  refine IsHomogeneous.sum _ _ _ fun i _ => IsHomogeneous.sum _ _ _ fun j _ => ?_
  rw [Matrix.of_apply, ← map_intCast (C : ℝ →+* MvPolynomial σ ℝ)]
  exact (isHomogeneous_X ℝ (v i j)).C_mul _

/-- A point that is one at the `Q` entry `(a d + p.1, p.2)` and at the `K` entry
`(b d + q.1, q.2)`, and zero elsewhere. -/
private def testPoint (a b : Fin B) (p q : Fin (2 ^ k) × Fin (2 ^ k)) : QKVar k B → ℝ :=
  Sum.elim (fun v => if v = (row a p.1, p.2) then 1 else 0)
    (fun v => if v = (row b q.1, q.2) then 1 else 0)

private lemma form_indicator (f : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℤ) (a a' : Fin B)
    (p : Fin (2 ^ k) × Fin (2 ^ k)) :
    form f (Matrix.of fun α γ => if (row a α, γ) = (row a' p.1, p.2) then (1 : ℝ) else 0) =
      if a = a' then (f p.1 p.2 : ℝ) else 0 := by
  split_ifs with h
  · subst h
    have : (Matrix.of fun α γ => if (row a α, γ) = (row a p.1, p.2) then (1 : ℝ) else 0) =
        Matrix.single p.1 p.2 1 := by
      ext α γ
      simp only [Matrix.of_apply, Prod.mk.injEq, row_eq_row_iff, true_and,
        Matrix.single_apply]
      exact if_congr ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩ rfl rfl
    rw [this, form_single]
  · have : (Matrix.of fun α γ => if (row a α, γ) = (row a' p.1, p.2) then (1 : ℝ) else 0) =
        0 := by
      ext α γ
      simp only [Matrix.of_apply, Prod.mk.injEq, row_eq_row_iff, Matrix.zero_apply]
      refine ite_eq_right ?_
      rintro ⟨⟨h', -⟩, -⟩
      exact h h'
    rw [this]
    simp [form]

private lemma eval_testPoint (a b a' b' : Fin B) (p q : Fin (2 ^ k) × Fin (2 ^ k))
    (r : Fin (7 ^ k)) :
    eval (testPoint a' b' p q) (expPoly k B (a, b, r)) =
      (if a = a' then (ellForm k r p.1 p.2 : ℝ) else 0) *
        (if b = b' then (emForm k r q.1 q.2 : ℝ) else 0) := by
  rw [expPoly, map_mul, eval_form (v := fun α γ => Sum.inl (row a α, γ)),
    eval_form (v := fun β γ => Sum.inr (row b β, γ))]
  simp only [testPoint, Sum.elim_inl, Sum.elim_inr]
  rw [form_indicator, form_indicator]

end BilinearPrefix

/-- Part of `thm:bilinear-prefix`: each exponent
polynomial `u_{ar} z_{br}` is homogeneous of degree two. -/
theorem bilinearPrefix_expPoly_isHomogeneous (x : Fin B × Fin B × Fin (7 ^ k)) :
    (expPoly k B x).IsHomogeneous 2 :=
  (isHomogeneous_form _ _).mul (isHomogeneous_form _ _)

/-- Part of `thm:bilinear-prefix`: the `B² R`
exponent polynomials `u_{ar} z_{br}` are linearly independent over `ℝ`. Within a block pair this
is `lem:strassen`, and different block pairs use disjoint monomials. -/
theorem bilinearPrefix_expPoly_linearIndependent : LinearIndependent ℝ (expPoly k B) := by
  classical
  refine linearIndependent_of_eval (expPoly k B)
    (fun s (τ : (Fin (2 ^ k) × Fin (2 ^ k)) × (Fin (2 ^ k) × Fin (2 ^ k))) =>
      testPoint s.1 s.2.1 τ.1 τ.2)
    (fun s τ => (dual k s.2.2 τ.1.1 τ.1.2 τ.2.1 τ.2.2 : ℝ)) fun x s => ?_
  obtain ⟨a, b, r⟩ := x
  obtain ⟨a₀, b₀, s₀⟩ := s
  simp only [eval_testPoint, Fintype.sum_prod_type]
  by_cases ha : a = a₀
  · by_cases hb : b = b₀
    · subst ha hb
      have h := congrArg (Int.cast : ℤ → ℝ) (biorth k r s₀)
      push_cast at h
      simp only [ite_true, Prod.mk.injEq, true_and]
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => ?_
      ring
    · have hne : (a, b, r) ≠ (a₀, b₀, s₀) := fun h => hb (Prod.mk.inj (Prod.mk.inj h).2).1
      simp [hb, hne]
  · have hne : (a, b, r) ≠ (a₀, b₀, s₀) := fun h => ha (Prod.mk.inj h).1
    simp [ha, hne]

namespace BilinearPrefix

/-- Linear independence over `ℝ` together with vanishing constant terms gives the hypothesis of
`lem:independence`. -/
lemma intCombNonconst_of_linearIndependent {ι σ : Type*} [Fintype ι]
    (p : ι → MvPolynomial σ ℝ) (hli : LinearIndependent ℝ p)
    (h0 : ∀ j, constantCoeff (p j) = 0) : IntCombNonconst p := by
  intro c hc r h
  have hr : r = 0 := by
    have := congrArg constantCoeff h
    simp only [map_sum, smul_eq_C_mul, map_mul, h0, mul_zero, Finset.sum_const_zero,
      constantCoeff_C] at this
    exact this.symm
  subst hr
  rw [map_zero] at h
  apply hc
  funext j
  have := Fintype.linearIndependent_iff.mp hli (fun j => (c j : ℝ)) h j
  exact_mod_cast this

/-- `IntCombNonconst` is preserved by an injective renaming of the variables, for instance when
the variables of `V` are added. -/
lemma intCombNonconst_rename {ι σ τ : Type*} [Fintype ι] {p : ι → MvPolynomial σ ℝ}
    (hp : IntCombNonconst p) {f : σ → τ} (hf : Function.Injective f) :
    IntCombNonconst fun j => rename f (p j) := by
  intro c hc r h
  apply hp c hc r
  apply rename_injective f hf
  simpa only [map_sum, map_smul, rename_C] using h

end BilinearPrefix

/-- Part of `thm:bilinear-prefix`: the exponent
polynomials `u_{ar} z_{br}`, for `a, b ∈ [B]` and `r ∈ [R]`, satisfy the hypothesis of
"Exponentials of polynomials" (`lem:independence`), that is, every nonzero integer combination
of them is nonconstant. -/
theorem bilinearPrefix_intCombNonconst : IntCombNonconst (expPoly k B) := by
  refine intCombNonconst_of_linearIndependent _ bilinearPrefix_expPoly_linearIndependent fun x => ?_
  rw [expPoly, map_mul]
  simp [form]

namespace BilinearPrefix

/-- The query matrix read off from a point of `QKVar k B`. -/
def pointQ (y : QKVar k B → ℝ) : Matrix (Fin (B * 2 ^ k)) (Fin (2 ^ k)) ℝ :=
  Matrix.of fun i γ => y (Sum.inl (i, γ))

/-- The key matrix read off from a point of `QKVar k B`. -/
def pointK (y : QKVar k B → ℝ) : Matrix (Fin (B * 2 ^ k)) (Fin (2 ^ k)) ℝ :=
  Matrix.of fun j γ => y (Sum.inr (j, γ))

lemma qkPoint_pointQ_pointK (y : QKVar k B → ℝ) : qkPoint (pointQ y) (pointK y) = y := by
  funext v
  rcases v with ⟨i, γ⟩ | ⟨j, γ⟩ <;> rfl

end BilinearPrefix

/-- Part of `thm:bilinear-prefix`, the independence
behind `eq:aux-field` and `τ₁(g) = B² R`: on every nonempty open set `U` of inputs `(Q, K)`, the
`B² R` leaf exponentials `E_{abr}` together with the input coordinates are algebraically
independent over `ℝ` as functions on `U`. This is `lem:independence` applied to the exponent
polynomials `u_{ar} z_{br}`. -/
theorem bilinearPrefix_leafExp_algebraicIndependent {U : Set (QKVar k B → ℝ)} (hU : IsOpen U)
    (hne : U.Nonempty) :
    AlgebraicIndependent ℝ (Sum.elim
      (fun (x : Fin B × Fin B × Fin (7 ^ k)) (y : U) =>
        leafExp (pointQ (y : QKVar k B → ℝ)) (pointK (y : QKVar k B → ℝ)) x.1 x.2.1 x.2.2)
      (fun v (y : U) => (y : QKVar k B → ℝ) v)) := by
  have hfam : (fun (x : Fin B × Fin B × Fin (7 ^ k)) (y : U) =>
      leafExp (pointQ (y : QKVar k B → ℝ)) (pointK (y : QKVar k B → ℝ)) x.1 x.2.1 x.2.2) =
      fun x (y : U) => Real.exp (eval (y : QKVar k B → ℝ) (expPoly k B x)) := by
    funext x y
    obtain ⟨a, b, r⟩ := x
    rw [← exp_eval_expPoly, qkPoint_pointQ_pointK]
  rw [hfam]
  exact algebraicIndependent_exp_poly (expPoly k B) bilinearPrefix_intCombNonconst hU hne

end ExactAttention
