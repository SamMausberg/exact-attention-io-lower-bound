import Mathlib

/-!
# Strassen's seven products and the recursive bilinear decomposition

This file formalizes `lem:strassen` and `app:strassen`.

* The seven products `p₁, …, p₇` are written as in `app:strassen`, and Strassen's identity
  `eq:strassen-base` is proved over every commutative ring.
* The coefficient matrix of `p₁, …, p₇` is read off from the polynomials, with the sixteen
  monomials `u_x b_y` ordered by the `U` entry and then by the `B` entry, each row by row. Its
  minor on the columns `0, 1, 3, 6, 8, 9, 12` is the matrix of `eq:minor-seven`, which has
  determinant one. This gives the independence of the seven bilinear polynomials.
* For `d = 2 ^ k` the recursion is described through digits. A row or column index of a `d × d`
  matrix is a string in `Fin k → Fin 2`, a leaf is a string in `Fin k → Fin 7`, and each
  coefficient of a leaf is the product over the `k` levels of the base coefficients. This
  matches the recursion on `2 × 2` blocks, with digit `t` selecting the block at level `t`.
  That identification is not proved, and the identities below do not depend on it. The results are then transported to `Fin (2 ^ k)`-indexed matrices and `Fin (7 ^ k)`
  leaves through `finFunctionFinEquiv`.
* Independence at depth `k` is proved with dual functionals. At the base they come from the
  adjugate of the minor, and at depth `k` they are products of base functionals.

The instruction and transfer bounds of `lem:strassen` are not formalized.
-/

namespace ExactAttention

open MvPolynomial Matrix Finset

namespace Strassen

/-! ### The seven products -/

/-- The seven products of `app:strassen`, for `U = (u_ij)` and `B = (b_ij)` with zero-based
indices. -/
def products {S : Type*} [CommRing S] (U B : Matrix (Fin 2) (Fin 2) S) : Fin 7 → S :=
  ![(U 0 0 + U 1 1) * (B 0 0 + B 1 1),
    (U 1 0 + U 1 1) * B 0 0,
    U 0 0 * (B 0 1 - B 1 1),
    U 1 1 * (B 1 0 - B 0 0),
    (U 0 0 + U 0 1) * B 1 1,
    (U 1 0 - U 0 0) * (B 0 0 + B 0 1),
    (U 0 1 - U 1 1) * (B 1 0 + B 1 1)]

/-- An integer linear form on square matrices, given by its coefficient matrix. -/
def form {I S : Type*} [Fintype I] [CommRing S] (f : Matrix I I ℤ) (U : Matrix I I S) : S :=
  ∑ i, ∑ j, (f i j : S) * U i j

/-- Coefficients of the left factors of `p₁, …, p₇`. -/
def lBase : Fin 7 → Matrix (Fin 2) (Fin 2) ℤ :=
  ![!![1, 0; 0, 1], !![0, 0; 1, 1], !![1, 0; 0, 0], !![0, 0; 0, 1],
    !![1, 1; 0, 0], !![-1, 0; 1, 0], !![0, 1; 0, -1]]

/-- Coefficients of the right factors of `p₁, …, p₇`, as forms in the entries of `B`. -/
def rBase : Fin 7 → Matrix (Fin 2) (Fin 2) ℤ :=
  ![!![1, 0; 0, 1], !![1, 0; 0, 0], !![0, 1; 0, -1], !![-1, 0; 1, 0],
    !![0, 0; 0, 1], !![1, 1; 0, 0], !![0, 0; 1, 1]]

/-- The right factors as forms in the entries of `Z = Bᵀ`. -/
def zBase (r : Fin 7) : Matrix (Fin 2) (Fin 2) ℤ := (rBase r)ᵀ

/-- Coefficient of `p_r` in the entry `(α, β)` of `eq:strassen-base`. -/
def cBase : Fin 2 → Fin 2 → Fin 7 → ℤ :=
  ![![![1, 0, 0, 1, -1, 0, 1], ![0, 0, 1, 0, 1, 0, 0]],
    ![![0, 1, 0, 1, 0, 0, 0], ![1, -1, 1, 0, 0, 1, 0]]]

lemma products_eq {S : Type*} [CommRing S] (U B : Matrix (Fin 2) (Fin 2) S) (r : Fin 7) :
    products U B r = form (lBase r) U * form (rBase r) B := by
  fin_cases r <;>
    simp [products, form, lBase, rBase, Fin.sum_univ_two] <;> ring

end Strassen

open Strassen

/-- Strassen's identity `eq:strassen-base`, from "The bilinear identity and its independent
factors" (`app:strassen`). The seven products are written as in the paper. -/
theorem strassen_mul {S : Type*} [CommRing S] (U B : Matrix (Fin 2) (Fin 2) S) :
    U * B =
      !![products U B 0 + products U B 3 - products U B 4 + products U B 6,
          products U B 2 + products U B 4;
         products U B 1 + products U B 3,
          products U B 0 - products U B 1 + products U B 2 + products U B 5] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [products, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

namespace Strassen

/-- Each entry of `U B` is the integer combination `∑ r, cBase α β r * p_r` of the products. -/
lemma mul_apply_eq_sum_products {S : Type*} [CommRing S] (U B : Matrix (Fin 2) (Fin 2) S)
    (α β : Fin 2) : (U * B) α β = ∑ r, (cBase α β r : S) * products U B r := by
  rw [strassen_mul]
  fin_cases α <;> fin_cases β <;> simp [cBase, Fin.sum_univ_succ] <;> ring

/-! ### The coefficient matrix and the minor of `eq:minor-seven` -/

/-- The variables: `inl (i, j)` is `u_ij` and `inr (i, j)` is `b_ij`. -/
abbrev Var := (Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2)

/-- The products `p₁, …, p₇` as polynomials in the eight entries of `U` and `B`. -/
noncomputable def prodPoly (S : Type*) [CommRing S] (r : Fin 7) : MvPolynomial Var S :=
  products (Matrix.of fun i j => X (Sum.inl (i, j))) (Matrix.of fun i j => X (Sum.inr (i, j))) r

/-- Entries of a `2 × 2` matrix in row-by-row order. -/
def entry (e : Fin 4) : Fin 2 × Fin 2 := finProdFinEquiv.symm e

/-- The monomial `u_x b_y` in column `c = 4 x + y`, where `x` and `y` are entry indices. -/
noncomputable def colMono (c : Fin 16) : Var →₀ ℕ :=
  Finsupp.single (Sum.inl (entry (finProdFinEquiv.symm c : Fin 4 × Fin 4).1)) 1 +
    Finsupp.single (Sum.inr (entry (finProdFinEquiv.symm c : Fin 4 × Fin 4).2)) 1

/-- The `7 × 16` coefficient matrix of `(p₁, …, p₇)`, computed from the polynomials. -/
noncomputable def coeffMatrix : Matrix (Fin 7) (Fin 16) ℤ :=
  Matrix.of fun r c => (prodPoly ℤ r).coeff (colMono c)

/-- The columns of the minor in `eq:minor-seven`. -/
def minorCols : Fin 7 → Fin 16 := ![0, 1, 3, 6, 8, 9, 12]

/-- The matrix displayed in `eq:minor-seven`. -/
def minorSeven : Matrix (Fin 7) (Fin 7) ℤ :=
  !![1, 0, 1, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 0, 1;
     0, 1, -1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, -1;
     0, 0, 1, 0, 0, 0, 0;
     -1, -1, 0, 0, 1, 1, 0;
     0, 0, 0, 1, 0, 0, 0]

private lemma single_add_single_eq_iff {P Q : Type*} {p x : P} {q y : Q} :
    (Finsupp.single (Sum.inl p : P ⊕ Q) 1 + Finsupp.single (Sum.inr q) 1 =
      Finsupp.single (Sum.inl x) 1 + Finsupp.single (Sum.inr y) 1) ↔ p = x ∧ q = y := by
  classical
  constructor
  · intro h
    have h1 := DFunLike.congr_fun h (Sum.inl x)
    have h2 := DFunLike.congr_fun h (Sum.inr y)
    simp only [Finsupp.add_apply, Finsupp.single_apply, Sum.inl.injEq, reduceCtorEq,
      ite_false, add_zero, zero_add, ite_true, Sum.inr.injEq] at h1 h2
    exact ⟨by by_contra hp; simp [hp] at h1, by by_contra hq; simp [hq] at h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The coefficient of `x_p y_q` in a product of a linear form in the `x` variables and a linear
form in the `y` variables. -/
lemma coeff_sum_mul_sum {P Q S : Type*} [Fintype P] [Fintype Q] [CommRing S]
    (a : P → S) (b : Q → S) (x : P) (y : Q) :
    ((∑ p, C (a p) * X (Sum.inl p)) * (∑ q, C (b q) * X (Sum.inr q))).coeff
        (Finsupp.single (Sum.inl x) 1 + Finsupp.single (Sum.inr y) 1) = a x * b y := by
  classical
  simp_rw [Finset.sum_mul_sum, coeff_sum]
  have key : ∀ p q, (C (a p) * X (Sum.inl p) * (C (b q) * X (Sum.inr q)) :
      MvPolynomial (P ⊕ Q) S).coeff (Finsupp.single (Sum.inl x) 1 + Finsupp.single (Sum.inr y) 1) =
      if p = x ∧ q = y then a p * b q else 0 := by
    intro p q
    have : (C (a p) * X (Sum.inl p) * (C (b q) * X (Sum.inr q)) : MvPolynomial (P ⊕ Q) S) =
        monomial (Finsupp.single (Sum.inl p) 1 + Finsupp.single (Sum.inr q) 1) (a p * b q) := by
      rw [X, X, C_mul_monomial, C_mul_monomial, monomial_mul_monomial]
      simp
    rw [this, coeff_monomial]
    exact if_congr single_add_single_eq_iff rfl rfl
  simp_rw [key, ite_and]
  simp

/-- A form applied to a matrix of variables, written as a sum over pairs. -/
private lemma form_X_eq {I S T : Type*} [Fintype I] [CommRing S] (f : Matrix I I ℤ)
    (v : I × I → T) :
    form f (Matrix.of fun i j => (X (v (i, j)) : MvPolynomial T S)) =
      ∑ p : I × I, C (f p.1 p.2 : S) * X (v p) := by
  rw [form, Fintype.sum_prod_type]
  simp [map_intCast]

lemma coeff_prodPoly (S : Type*) [CommRing S] (r : Fin 7) (x y : Fin 2 × Fin 2) :
    (prodPoly S r).coeff (Finsupp.single (Sum.inl x) 1 + Finsupp.single (Sum.inr y) 1) =
      ((lBase r x.1 x.2 * rBase r y.1 y.2 : ℤ) : S) := by
  rw [prodPoly, products_eq, form_X_eq (v := Sum.inl), form_X_eq (v := Sum.inr),
    coeff_sum_mul_sum]
  push_cast
  rfl

lemma coeffMatrix_apply (r : Fin 7) (c : Fin 16) :
    coeffMatrix r c =
      lBase r (entry (finProdFinEquiv.symm c : Fin 4 × Fin 4).1).1
          (entry (finProdFinEquiv.symm c : Fin 4 × Fin 4).1).2 *
        rBase r (entry (finProdFinEquiv.symm c : Fin 4 × Fin 4).2).1
          (entry (finProdFinEquiv.symm c : Fin 4 × Fin 4).2).2 := by
  rw [coeffMatrix, Matrix.of_apply, colMono, coeff_prodPoly, Int.cast_id]

end Strassen

/-- The bilinear identity and its independent factors (`app:strassen`): the minor of the
coefficient matrix of `p₁, …, p₇` on the columns `0, 1, 3, 6, 8, 9, 12` is the matrix of
`eq:minor-seven`. -/
theorem strassen_minor_eq :
    coeffMatrix.submatrix id minorCols = minorSeven := by
  ext r c
  rw [Matrix.submatrix_apply, id, coeffMatrix_apply]
  fin_cases r <;> fin_cases c <;> decide

/-- The bilinear identity and its independent factors (`app:strassen`): the minor of
`eq:minor-seven` has determinant one. -/
theorem strassen_minor_det : minorSeven.det = 1 := by
  simp [minorSeven, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  decide

namespace Strassen

/-- The entry of `U` in the minor column `c`. -/
def colU (c : Fin 7) : Fin 2 × Fin 2 := entry (finProdFinEquiv.symm (minorCols c) : Fin 4 × Fin 4).1

/-- The entry of `B` in the minor column `c`. -/
def colB (c : Fin 7) : Fin 2 × Fin 2 := entry (finProdFinEquiv.symm (minorCols c) : Fin 4 × Fin 4).2

lemma minorSeven_apply (r c : Fin 7) :
    minorSeven r c = lBase r (colU c).1 (colU c).2 * rBase r (colB c).1 (colB c).2 := by
  rw [← strassen_minor_eq, Matrix.submatrix_apply, id, coeffMatrix_apply]
  rfl

lemma det_minorSeven_map (S : Type*) [CommRing S] :
    (minorSeven.map (Int.cast : ℤ → S)).det = 1 := by
  have h := RingHom.map_det (Int.castRingHom S) minorSeven
  rw [strassen_minor_det, map_one] at h
  exact h.symm

end Strassen

/-- The seven-product decomposition (`lem:strassen`) at the base: the bilinear polynomials
`p₁, …, p₇` are linearly independent over every commutative ring, since the minor of
`eq:minor-seven` has determinant one (`app:strassen`). -/
theorem strassen_base_linearIndependent (S : Type*) [CommRing S] :
    LinearIndependent S (prodPoly S) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set M := minorSeven.map (Int.cast : ℤ → S)
  have hv : g ᵥ* M = 0 := by
    funext c
    have h := congrArg (fun p : MvPolynomial Var S => p.coeff (colMono (minorCols c))) hg
    simp only [coeff_sum, coeff_smul, smul_eq_mul, AddMonoidAlgebra.coeff_zero,
      Finsupp.coe_zero, Pi.zero_apply] at h
    simp only [Matrix.vecMul, dotProduct, M, Matrix.map_apply, minorSeven_apply, Pi.zero_apply]
    rw [← h]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [colMono, coeff_prodPoly]
    rfl
  have hM : M * M.adjugate = 1 := by
    rw [Matrix.mul_adjugate, det_minorSeven_map, one_smul]
  intro r
  have : g = 0 := by
    calc g = g ᵥ* (M * M.adjugate) := by rw [hM, Matrix.vecMul_one]
      _ = 0 := by rw [← Matrix.vecMul_vecMul, hv, Matrix.zero_vecMul]
  rw [this, Pi.zero_apply]

namespace Strassen

/-! ### Dual functionals at the base -/

/-- Dual functionals on the sixteen monomials `u_x b_y`, built from the adjugate of the minor. -/
noncomputable def baseDualB (s : Fin 7) (x y : Fin 2 × Fin 2) : ℤ :=
  ∑ c, if colU c = x ∧ colB c = y then minorSeven.adjugate c s else 0

lemma baseDualB_biorth (r s : Fin 7) :
    ∑ x : Fin 2 × Fin 2, ∑ y : Fin 2 × Fin 2,
      baseDualB s x y * lBase r x.1 x.2 * rBase r y.1 y.2 = if r = s then 1 else 0 := by
  have h1 : ∀ x y : Fin 2 × Fin 2, baseDualB s x y * lBase r x.1 x.2 * rBase r y.1 y.2 =
      ∑ c, if colU c = x ∧ colB c = y then
        minorSeven.adjugate c s * lBase r x.1 x.2 * rBase r y.1 y.2 else 0 := by
    intro x y
    rw [baseDualB, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs <;> ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 2 × Fin 2)))
    (t := (Finset.univ : Finset (Fin 7)))]
  simp_rw [ite_and]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have h2 : ∀ c, minorSeven.adjugate c s * lBase r (colU c).1 (colU c).2 *
      rBase r (colB c).1 (colB c).2 = minorSeven r c * minorSeven.adjugate c s := by
    intro c; rw [minorSeven_apply]; ring
  simp_rw [h2]
  have h3 := congrFun (congrFun (Matrix.mul_adjugate minorSeven) r) s
  rw [strassen_minor_det, one_smul, Matrix.mul_apply, Matrix.one_apply] at h3
  exact h3

/-- The base dual functionals, with the right variables read as entries of `Z = Bᵀ`. -/
noncomputable def baseDual (s : Fin 7) (i j i' j' : Fin 2) : ℤ := baseDualB s (i, j) (j', i')

lemma baseDual_biorth (r s : Fin 7) :
    ∑ i, ∑ j, ∑ i', ∑ j', baseDual s i j i' j' * lBase r i j * zBase r i' j' =
      if r = s then 1 else 0 := by
  rw [← baseDualB_biorth r s, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- The coefficient form of Strassen's identity: the matrix multiplication tensor. -/
lemma tensor_base (α β i j i' j' : Fin 2) :
    ∑ r, cBase α β r * lBase r i j * zBase r i' j' =
      if α = i ∧ β = i' ∧ j = j' then 1 else 0 := by
  revert α β i j i' j'
  decide

/-! ### The recursive decomposition through digit strings -/

/-- Coefficient of `U i j` in the left form of the leaf `r` at depth `k`. -/
def lCoef (k : ℕ) (r : Fin k → Fin 7) (i j : Fin k → Fin 2) : ℤ :=
  ∏ t, lBase (r t) (i t) (j t)

/-- Coefficient of `Z i j` in the right form of the leaf `r` at depth `k`. -/
def zCoef (k : ℕ) (r : Fin k → Fin 7) (i j : Fin k → Fin 2) : ℤ :=
  ∏ t, zBase (r t) (i t) (j t)

/-- Coefficient of the leaf `r` in the output entry `(α, β)` at depth `k`. -/
def cCoef (k : ℕ) (α β : Fin k → Fin 2) (r : Fin k → Fin 7) : ℤ :=
  ∏ t, cBase (α t) (β t) (r t)

/-- Product dual functionals at depth `k`. -/
noncomputable def dualCoef (k : ℕ) (s : Fin k → Fin 7) (i j i' j' : Fin k → Fin 2) : ℤ :=
  ∏ t, baseDual (s t) (i t) (j t) (i' t) (j' t)

private lemma sum4_prod {k : ℕ} {S : Type*} [CommRing S]
    (f : Fin k → Fin 2 → Fin 2 → Fin 2 → Fin 2 → S) :
    ∑ i : Fin k → Fin 2, ∑ j : Fin k → Fin 2, ∑ i' : Fin k → Fin 2, ∑ j' : Fin k → Fin 2,
      ∏ t, f t (i t) (j t) (i' t) (j' t) = ∏ t, ∑ a, ∑ b, ∑ c, ∑ e, f t a b c e := by
  simp only [Fintype.prod_sum]

lemma tensor_pi (k : ℕ) (α β i j i' j' : Fin k → Fin 2) :
    ∑ r, cCoef k α β r * lCoef k r i j * zCoef k r i' j' =
      if α = i ∧ β = i' ∧ j = j' then 1 else 0 := by
  simp only [cCoef, lCoef, zCoef, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun t x => cBase (α t) (β t) x * lBase x (i t) (j t) *
    zBase x (i' t) (j' t))]
  simp only [tensor_base, Fintype.prod_boole]
  congr 1
  simp only [funext_iff, forall_and]

lemma biorth_pi (k : ℕ) (r s : Fin k → Fin 7) :
    ∑ i, ∑ j, ∑ i', ∑ j', dualCoef k s i j i' j' * lCoef k r i j * zCoef k r i' j' =
      if r = s then 1 else 0 := by
  simp only [dualCoef, lCoef, zCoef, ← Finset.prod_mul_distrib]
  rw [sum4_prod (fun t a b c e => baseDual (s t) a b c e * lBase (r t) a b * zBase (r t) c e)]
  simp only [baseDual_biorth, Fintype.prod_boole]
  congr 1
  simp only [funext_iff]

/-! ### Generic consequences of the tensor identity and of dual functionals -/

section Generic

variable {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L]

omit [DecidableEq I] [Fintype L] in
private lemma form_eq_sum_pair {S : Type*} [CommRing S] (f : Matrix I I ℤ) (U : Matrix I I S) :
    form f U = ∑ p : I × I, (f p.1 p.2 : S) * U p.1 p.2 := by
  rw [form, Fintype.sum_prod_type]

/-- If the coefficients satisfy the matrix multiplication tensor identity, the bilinear formula
`eq:bilinear` holds over every commutative ring. -/
lemma mul_transpose_apply_of_tensor (c : I → I → L → ℤ) (l m : L → Matrix I I ℤ)
    (h : ∀ α β i j i' j', ∑ r, c α β r * l r i j * m r i' j' =
      if α = i ∧ β = i' ∧ j = j' then 1 else 0)
    {S : Type*} [CommRing S] (U Z : Matrix I I S) (α β : I) :
    (U * Zᵀ) α β = ∑ r, (c α β r : S) * form (l r) U * form (m r) Z := by
  have key : ∀ r, (c α β r : S) * form (l r) U * form (m r) Z =
      ∑ p : I × I, ∑ q : I × I,
        ((c α β r * l r p.1 p.2 * m r q.1 q.2 : ℤ) : S) * (U p.1 p.2 * Z q.1 q.2) := by
    intro r
    rw [form_eq_sum_pair, form_eq_sum_pair, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    push_cast
    ring
  calc (U * Zᵀ) α β
    _ = ∑ p : I × I, ∑ q : I × I,
        (if α = p.1 ∧ β = q.1 ∧ p.2 = q.2 then U p.1 p.2 * Z q.1 q.2 else 0) := by
      rw [Matrix.mul_apply]
      simp only [Fintype.sum_prod_type, Matrix.transpose_apply, ite_and, Finset.sum_ite_irrel,
        Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    _ = ∑ p : I × I, ∑ q : I × I, ∑ r,
          ((c α β r * l r p.1 p.2 * m r q.1 q.2 : ℤ) : S) * (U p.1 p.2 * Z q.1 q.2) := by
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      rw [← Finset.sum_mul, ← Int.cast_sum, h]
      split_ifs <;> simp
    _ = ∑ p : I × I, ∑ r, ∑ q : I × I,
          ((c α β r * l r p.1 p.2 * m r q.1 q.2 : ℤ) : S) * (U p.1 p.2 * Z q.1 q.2) :=
      Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ r, ∑ p : I × I, ∑ q : I × I,
          ((c α β r * l r p.1 p.2 * m r q.1 q.2 : ℤ) : S) * (U p.1 p.2 * Z q.1 q.2) :=
      Finset.sum_comm
    _ = ∑ r, (c α β r : S) * form (l r) U * form (m r) Z :=
      Finset.sum_congr rfl fun r _ => (key r).symm

/-- A form applied to the matrix with a single entry one picks out that coefficient. -/
lemma form_single {S : Type*} [CommRing S] (f : Matrix I I ℤ) (i j : I) :
    form f (Matrix.single i j (1 : S)) = f i j := by
  simp [form, Matrix.single_apply, ite_and]

/-- The bilinear polynomial `ℓ_r(U) m_r(Z)` in the variables `inl (i, j) = U i j` and
`inr (i, j) = Z i j`. -/
noncomputable def bilinPoly (S : Type*) [CommRing S] (l m : L → Matrix I I ℤ) (r : L) :
    MvPolynomial ((I × I) ⊕ (I × I)) S :=
  form (l r) (Matrix.of fun i j => X (Sum.inl (i, j))) *
    form (m r) (Matrix.of fun i j => X (Sum.inr (i, j)))

omit [DecidableEq I] [Fintype L] in
lemma eval_form {σ S : Type*} [CommRing S] (f : Matrix I I ℤ) (v : I → I → σ) (x : σ → S) :
    eval x (form f (Matrix.of fun i j => (X (v i j) : MvPolynomial σ S))) =
      form f (Matrix.of fun i j => x (v i j)) := by
  simp [form]

omit [DecidableEq I] [Fintype L] in
lemma eval_bilinPoly {S : Type*} [CommRing S] (l m : L → Matrix I I ℤ) (r : L)
    (x : (I × I) ⊕ (I × I) → S) :
    eval x (bilinPoly S l m r) =
      form (l r) (Matrix.of fun i j => x (Sum.inl (i, j))) *
        form (m r) (Matrix.of fun i j => x (Sum.inr (i, j))) := by
  rw [bilinPoly, map_mul, eval_form (v := fun i j => Sum.inl (i, j)),
    eval_form (v := fun i j => Sum.inr (i, j))]

end Generic

/-- A family of polynomials is linearly independent as soon as there are biorthogonal linear
functionals, each a weighted sum of evaluations. -/
lemma linearIndependent_of_eval {ι σ T S : Type*} [Fintype ι] [DecidableEq ι] [Fintype T]
    [CommRing S] (P : ι → MvPolynomial σ S) (x : ι → T → σ → S) (w : ι → T → S)
    (h : ∀ r s, ∑ τ, w s τ * eval (x s τ) (P r) = if r = s then 1 else 0) :
    LinearIndependent S P := by
  rw [Fintype.linearIndependent_iff]
  intro g hg s
  have h1 := congrArg (fun F => ∑ τ, w s τ * eval (x s τ) F) hg
  simp only [map_sum, smul_eval, map_zero, mul_zero, Finset.sum_const_zero, Finset.mul_sum] at h1
  rw [Finset.sum_comm] at h1
  have h2 : ∀ r, ∑ τ, w s τ * (g r * eval (x s τ) (P r)) = g r * if r = s then 1 else 0 := by
    intro r
    rw [← h r, Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => by ring
  simp_rw [h2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
  exact h1

section Generic

variable {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]

/-- Bilinear polynomials with biorthogonal dual functionals are linearly independent over every
commutative ring. -/
lemma linearIndependent_bilinPoly (S : Type*) [CommRing S] (l m : L → Matrix I I ℤ)
    (Φ : L → I → I → I → I → ℤ)
    (h : ∀ r s, ∑ i, ∑ j, ∑ i', ∑ j', Φ s i j i' j' * l r i j * m r i' j' =
      if r = s then 1 else 0) :
    LinearIndependent S (bilinPoly S l m) := by
  refine linearIndependent_of_eval (bilinPoly S l m)
    (fun _ (τ : I × I × I × I) => Sum.elim
      (fun p => Matrix.single τ.1 τ.2.1 (1 : S) p.1 p.2)
      (fun q => Matrix.single τ.2.2.1 τ.2.2.2 (1 : S) q.1 q.2))
    (fun s τ => (Φ s τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 : S)) fun r s => ?_
  simp only [eval_bilinPoly, Sum.elim_inl, Sum.elim_inr]
  have hU : ∀ i j : I, (Matrix.of fun a b => Matrix.single i j (1 : S) a b) =
      Matrix.single i j 1 := fun _ _ => rfl
  simp only [hU, form_single]
  simp only [Fintype.sum_prod_type]
  have := congrArg (Int.cast : ℤ → S) (h r s)
  push_cast at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => ?_
  ring

/-- A form as a linear functional on matrices. -/
def formLin (S : Type*) [CommRing S] (f : Matrix I I ℤ) : Module.Dual S (Matrix I I S) where
  toFun := form f
  map_add' U V := by simp [form, mul_add, Finset.sum_add_distrib]
  map_smul' a U := by simp [form, Finset.mul_sum, mul_left_comm]

omit [DecidableEq L] in
/-- Under the tensor identity, the left forms span the dual space over every commutative
ring: each coordinate functional `U ↦ U α γ` is an integer combination of them. -/
lemma span_formLin_of_tensor (c : I → I → L → ℤ) (l m : L → Matrix I I ℤ)
    (h : ∀ α β i j i' j', ∑ r, c α β r * l r i j * m r i' j' =
      if α = i ∧ β = i' ∧ j = j' then 1 else 0)
    (S : Type*) [CommRing S] :
    Submodule.span S (Set.range fun r => formLin S (l r)) = ⊤ := by
  rw [eq_top_iff]
  rintro φ -
  have hφ : φ = ∑ α, ∑ γ, ∑ r, (φ (Matrix.single α γ 1) *
      ((c α α r : S) * form (m r) (Matrix.single α γ (1 : S)))) • formLin S (l r) := by
    refine LinearMap.ext fun U => ?_
    conv_lhs => rw [Matrix.matrix_eq_sum_single U]
    simp only [map_sum, LinearMap.sum_apply, LinearMap.smul_apply]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun γ _ => ?_
    have hc := mul_transpose_apply_of_tensor c l m h U (Matrix.single α γ (1 : S)) α α
    have hs : (U * (Matrix.single α γ (1 : S))ᵀ) α α = U α γ := by
      simp [Matrix.mul_apply, Matrix.single_apply]
    rw [hs] at hc
    have h1 : Matrix.single α γ (U α γ) = U α γ • Matrix.single α γ (1 : S) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [h1, map_smul, smul_eq_mul, hc, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [smul_eq_mul]
    change _ = _ * form (l r) U
    ring
  rw [hφ]
  exact Submodule.sum_mem _ fun α _ => Submodule.sum_mem _ fun γ _ => Submodule.sum_mem _
    fun r _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)

end Generic

/-! ### Transport to `Fin (2 ^ k)` indices and `Fin (7 ^ k)` leaves -/

/-- Binary digit strings of length `k` and indices in `Fin (2 ^ k)`. -/
abbrev e2 (k : ℕ) : (Fin k → Fin 2) ≃ Fin (2 ^ k) := finFunctionFinEquiv

/-- Base-seven digit strings of length `k` and leaves in `Fin (7 ^ k)`. -/
abbrev e7 (k : ℕ) : (Fin k → Fin 7) ≃ Fin (7 ^ k) := finFunctionFinEquiv

/-- The left form `ℓ_r` of the leaf `r` at depth `k`, on `d × d` matrices with `d = 2 ^ k`. -/
def ellForm (k : ℕ) (r : Fin (7 ^ k)) : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℤ :=
  Matrix.of fun i j => lCoef k ((e7 k).symm r) ((e2 k).symm i) ((e2 k).symm j)

/-- The right form `m_r` of the leaf `r` at depth `k`. -/
def emForm (k : ℕ) (r : Fin (7 ^ k)) : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℤ :=
  Matrix.of fun i j => zCoef k ((e7 k).symm r) ((e2 k).symm i) ((e2 k).symm j)

/-- The output coefficients `c_{αβr}` at depth `k`. -/
def coef (k : ℕ) (α β : Fin (2 ^ k)) (r : Fin (7 ^ k)) : ℤ :=
  cCoef k ((e2 k).symm α) ((e2 k).symm β) ((e7 k).symm r)

/-- Dual functionals for the depth `k` bilinear polynomials. -/
noncomputable def dual (k : ℕ) (s : Fin (7 ^ k)) (i j i' j' : Fin (2 ^ k)) : ℤ :=
  dualCoef k ((e7 k).symm s) ((e2 k).symm i) ((e2 k).symm j) ((e2 k).symm i') ((e2 k).symm j')

lemma tensor (k : ℕ) (α β i j i' j' : Fin (2 ^ k)) :
    ∑ r, coef k α β r * ellForm k r i j * emForm k r i' j' =
      if α = i ∧ β = i' ∧ j = j' then 1 else 0 := by
  have := (e7 k).symm.sum_comp (fun r => cCoef k ((e2 k).symm α) ((e2 k).symm β) r *
    lCoef k r ((e2 k).symm i) ((e2 k).symm j) * zCoef k r ((e2 k).symm i') ((e2 k).symm j'))
  simp only [coef, ellForm, emForm, Matrix.of_apply]
  rw [this, tensor_pi]
  simp only [(e2 k).symm.injective.eq_iff]

lemma biorth (k : ℕ) (r s : Fin (7 ^ k)) :
    ∑ i, ∑ j, ∑ i', ∑ j', dual k s i j i' j' * ellForm k r i j * emForm k r i' j' =
      if r = s then 1 else 0 := by
  have h := biorth_pi k ((e7 k).symm r) ((e7 k).symm s)
  simp only [EmbeddingLike.apply_eq_iff_eq] at h
  rw [← h]
  simp only [dual, ellForm, emForm, Matrix.of_apply]
  rw [← (e2 k).sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← (e2 k).sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← (e2 k).sum_comp]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [← (e2 k).sum_comp]
  simp only [Equiv.symm_apply_apply]

private lemma exists_lBase_ne_zero : ∀ x : Fin 7, ∃ p : Fin 2 × Fin 2, lBase x p.1 p.2 ≠ 0 := by
  decide

private lemma exists_zBase_ne_zero : ∀ x : Fin 7, ∃ p : Fin 2 × Fin 2, zBase x p.1 p.2 ≠ 0 := by
  decide

end Strassen

open Strassen

/-- The seven-product decomposition (`lem:strassen`), identity `eq:bilinear`: for `d = 2 ^ k`
and `R = 7 ^ k`, each entry of `U Zᵀ` equals `∑ r, c_{αβr} ℓ_r(U) m_r(Z)`, with integer forms and
integer coefficients, over every commutative ring. -/
theorem strassen_bilinear (k : ℕ) {S : Type*} [CommRing S]
    (U Z : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) S) (α β : Fin (2 ^ k)) :
    (U * Zᵀ) α β = ∑ r, (coef k α β r : S) * form (ellForm k r) U * form (emForm k r) Z :=
  mul_transpose_apply_of_tensor (coef k) (ellForm k) (emForm k) (tensor k) U Z α β

/-- The seven-product decomposition (`lem:strassen`): the `R = 7 ^ k` bilinear polynomials
`ℓ_r(U) m_r(Z)` are linearly independent over every commutative ring. -/
theorem strassen_bilinear_linearIndependent (k : ℕ) (S : Type*) [CommRing S] :
    LinearIndependent S (bilinPoly S (ellForm k) (emForm k)) :=
  linearIndependent_bilinPoly S (ellForm k) (emForm k) (dual k) (biorth k)

/-- The seven-product decomposition (`lem:strassen`): the forms `ℓ_r` span the dual of the
space of `d × d` matrices, over every commutative ring. -/
theorem strassen_forms_span (k : ℕ) (S : Type*) [CommRing S] :
    Submodule.span S (Set.range fun r => formLin S (ellForm k r)) = ⊤ :=
  span_formLin_of_tensor (coef k) (ellForm k) (emForm k) (tensor k) S

/-- The seven-product decomposition (`lem:strassen`): if every form `ℓ_r` vanishes at `U`, then
`U = 0`. As in the paper, the proof takes `Z` to be the identity in `eq:bilinear`. -/
theorem strassen_eq_zero_of_forms (k : ℕ) {S : Type*} [CommRing S]
    (U : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) S) (hU : ∀ r, form (ellForm k r) U = 0) : U = 0 := by
  ext α γ
  have h := strassen_bilinear k U 1 α γ
  simp only [hU, mul_zero, zero_mul, Finset.sum_const_zero, Matrix.transpose_one,
    Matrix.mul_one] at h
  exact h

/-- The seven-product decomposition (`lem:strassen`): every form `ℓ_r` and every form `m_r` is
nonzero. -/
theorem strassen_forms_ne_zero (k : ℕ) (r : Fin (7 ^ k)) : ellForm k r ≠ 0 ∧ emForm k r ≠ 0 := by
  choose p hp using exists_lBase_ne_zero
  choose q hq using exists_zBase_ne_zero
  set r' := (e7 k).symm r
  constructor
  · intro h
    have h1 := congrFun (congrFun h ((e2 k) fun t => (p (r' t)).1)) ((e2 k) fun t => (p (r' t)).2)
    simp only [ellForm, Matrix.of_apply, Equiv.symm_apply_apply, Matrix.zero_apply, lCoef] at h1
    exact Finset.prod_ne_zero_iff.mpr (fun t _ => hp (r' t)) h1
  · intro h
    have h1 := congrFun (congrFun h ((e2 k) fun t => (q (r' t)).1)) ((e2 k) fun t => (q (r' t)).2)
    simp only [emForm, Matrix.of_apply, Equiv.symm_apply_apply, Matrix.zero_apply,
      zCoef] at h1
    exact Finset.prod_ne_zero_iff.mpr (fun t _ => hq (r' t)) h1

/-- The seven-product decomposition (`lem:strassen`), in one statement: for `d = 2 ^ k` and
`R = 7 ^ k` there are nonzero integer forms `ℓ_r, m_r` on `d × d` matrices and integers
`c_{αβr}` such that `eq:bilinear` holds, the `R` bilinear polynomials `ℓ_r(U) m_r(Z)` are linearly
independent, and the forms `ℓ_r` span the dual space. -/
theorem strassen_decomposition (k : ℕ) :
    ∃ (ℓ m : Fin (7 ^ k) → Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℤ)
      (c : Fin (2 ^ k) → Fin (2 ^ k) → Fin (7 ^ k) → ℤ),
      (∀ r, ℓ r ≠ 0 ∧ m r ≠ 0) ∧
      (∀ (S : Type) [CommRing S] (U Z : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) S) (α β),
        (U * Zᵀ) α β = ∑ r, (c α β r : S) * form (ℓ r) U * form (m r) Z) ∧
      (∀ (S : Type) [CommRing S], LinearIndependent S (bilinPoly S ℓ m)) ∧
      (∀ (S : Type) [CommRing S],
        Submodule.span S (Set.range fun r => formLin S (ℓ r)) = ⊤) :=
  ⟨ellForm k, emForm k, coef k, strassen_forms_ne_zero k, fun _ _ U Z α β => strassen_bilinear k U Z α β,
    fun S _ => strassen_bilinear_linearIndependent k S, fun S _ => strassen_forms_span k S⟩

end ExactAttention
