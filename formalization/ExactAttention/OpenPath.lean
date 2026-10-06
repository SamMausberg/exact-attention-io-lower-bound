import Mathlib

/-!
# An open execution path (`lem:open`)

The paper unrolls a bounded program at a fixed parameter triple into a finite decision tree.
We model that tree directly.

* `OpenPath.Expr σ` is an expression over `+`, `-`, `*`, `/`, `exp`, the input coordinates
  `x i` (`i : σ`) and arbitrary real constants. Every register value of a straight-line block is
  such an expression in the inputs, obtained by unfolding the block. `Expr.eval` uses Lean's real
  division, and `Expr.Safe e x` says that every division inside `e` has a nonzero denominator at
  `x`.
* `OpenPath.Tree σ α` is a finite decision tree. An internal node carries discrete data of type
  `α` (register names, slow addresses, which instructions are loads and stores), the list of
  values computed in its block, and a test value `c`. The input `x` then continues in the branch
  `SignType.sign (c.eval x)`, so a test has three outcomes: negative, zero, positive. A sign
  comparison of two values is the test of their difference. A leaf carries its discrete data and
  its final values (outputs included).
* `Tree.path T x` is the list of test outcomes followed by `x`, and `Tree.valuesAlong T π` lists
  the values computed along a path `π`. The division condition of the model is `Tree.SafeOn T U`:
  for every input `x ∈ U`, every value computed along the path of `x` has nonzero denominators
  at `x`.

Since the discrete data of each node is a function of the path, a fixed path also fixes the
accessed addresses. `exists_open_path` is `lem:open`: a nonempty open input set contains a
nonempty connected open set on which all inputs follow one path to a leaf, and on which every
value computed along that path is analytic. `OpenPath.Expr.analyticAt_eval` shows that an
expression is analytic wherever its denominators are nonzero. Only continuity of the test values
is needed to find the path; analyticity is part of the conclusion. `Expr.subst` substitutes
expressions for variables; `ExactAttention.boundary_factorization` uses it for `lem:boundary`.
-/

namespace ExactAttention

namespace OpenPath

/-- Expressions over `+`, `-`, `*`, `/`, `exp`, input coordinates and real constants. -/
inductive Expr (σ : Type*) : Type _
  | const (r : ℝ)
  | var (i : σ)
  | add (e₁ e₂ : Expr σ)
  | sub (e₁ e₂ : Expr σ)
  | mul (e₁ e₂ : Expr σ)
  | div (e₁ e₂ : Expr σ)
  | exp (e : Expr σ)

namespace Expr

variable {σ τ : Type*}

/-- The value of an expression at an input. -/
noncomputable def eval : Expr σ → (σ → ℝ) → ℝ
  | const r, _ => r
  | var i, x => x i
  | add e₁ e₂, x => e₁.eval x + e₂.eval x
  | sub e₁ e₂, x => e₁.eval x - e₂.eval x
  | mul e₁ e₂, x => e₁.eval x * e₂.eval x
  | div e₁ e₂, x => e₁.eval x / e₂.eval x
  | exp e, x => Real.exp (e.eval x)

/-- Every division inside the expression has a nonzero denominator at `x`. -/
def Safe : Expr σ → (σ → ℝ) → Prop
  | const _, _ => True
  | var _, _ => True
  | add e₁ e₂, x => e₁.Safe x ∧ e₂.Safe x
  | sub e₁ e₂, x => e₁.Safe x ∧ e₂.Safe x
  | mul e₁ e₂, x => e₁.Safe x ∧ e₂.Safe x
  | div e₁ e₂, x => e₁.Safe x ∧ e₂.Safe x ∧ e₂.eval x ≠ 0
  | exp e, x => e.Safe x

/-- Substitution of expressions for the variables. This is how an epoch's values become
expressions in its incoming arguments. -/
def subst : Expr τ → (τ → Expr σ) → Expr σ
  | const r, _ => const r
  | var i, g => g i
  | add e₁ e₂, g => add (e₁.subst g) (e₂.subst g)
  | sub e₁ e₂, g => sub (e₁.subst g) (e₂.subst g)
  | mul e₁ e₂, g => mul (e₁.subst g) (e₂.subst g)
  | div e₁ e₂, g => div (e₁.subst g) (e₂.subst g)
  | exp e, g => exp (e.subst g)

theorem eval_subst (e : Expr τ) (g : τ → Expr σ) (x : σ → ℝ) :
    (e.subst g).eval x = e.eval (fun i => (g i).eval x) := by
  induction e with
  | const r => rfl
  | var i => rfl
  | add e₁ e₂ ih₁ ih₂ => simp only [subst, eval, ih₁, ih₂]
  | sub e₁ e₂ ih₁ ih₂ => simp only [subst, eval, ih₁, ih₂]
  | mul e₁ e₂ ih₁ ih₂ => simp only [subst, eval, ih₁, ih₂]
  | div e₁ e₂ ih₁ ih₂ => simp only [subst, eval, ih₁, ih₂]
  | exp e ih => simp only [subst, eval, ih]

/-- If a substituted expression is division safe at `x`, then the outer expression is division
safe at the values of the substituted arguments. -/
theorem safe_of_safe_subst (e : Expr τ) (g : τ → Expr σ) {x : σ → ℝ}
    (h : (e.subst g).Safe x) : e.Safe (fun i => (g i).eval x) := by
  induction e with
  | const r => trivial
  | var i => trivial
  | add e₁ e₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | sub e₁ e₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | mul e₁ e₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | div e₁ e₂ ih₁ ih₂ =>
    refine ⟨ih₁ h.1, ih₂ h.2.1, ?_⟩
    have := h.2.2
    rwa [eval_subst] at this
  | exp e ih => exact ih h

variable [Fintype σ]

/-- A straight-line expression is analytic at every point where the denominators of its
divisions are nonzero. This is the arithmetic step in the proof of `lem:open`. -/
theorem analyticAt_eval (e : Expr σ) {x : σ → ℝ} (h : e.Safe x) :
    AnalyticAt ℝ e.eval x := by
  induction e with
  | const r => exact analyticAt_const
  | var i => exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ => ℝ) i).analyticAt x
  | add e₁ e₂ ih₁ ih₂ => exact (ih₁ h.1).add (ih₂ h.2)
  | sub e₁ e₂ ih₁ ih₂ => exact (ih₁ h.1).sub (ih₂ h.2)
  | mul e₁ e₂ ih₁ ih₂ => exact (ih₁ h.1).mul (ih₂ h.2)
  | div e₁ e₂ ih₁ ih₂ => exact (ih₁ h.1).div (ih₂ h.2.1) h.2.2
  | exp e ih => exact (ih h).rexp

theorem continuousAt_eval (e : Expr σ) {x : σ → ℝ} (h : e.Safe x) :
    ContinuousAt e.eval x :=
  (e.analyticAt_eval h).continuousAt

/-- The set where an expression is division safe is open: nonzero denominators stay nonzero
nearby. -/
theorem isOpen_setOf_safe (e : Expr σ) : IsOpen {x | e.Safe x} := by
  induction e with
  | const r => exact isOpen_univ
  | var i => exact isOpen_univ
  | add e₁ e₂ ih₁ ih₂ => exact ih₁.inter ih₂
  | sub e₁ e₂ ih₁ ih₂ => exact ih₁.inter ih₂
  | mul e₁ e₂ ih₁ ih₂ => exact ih₁.inter ih₂
  | div e₁ e₂ ih₁ ih₂ =>
    have hc : ContinuousOn e₂.eval {x | e₂.Safe x} := fun x hx =>
      (e₂.continuousAt_eval hx).continuousWithinAt
    have h₂ := hc.isOpen_inter_preimage ih₂ (isOpen_ne (x := (0 : ℝ)))
    exact ih₁.inter h₂
  | exp e ih => exact ih

end Expr

/-- A finite decision tree with three-way sign tests. A node carries discrete data, the values
computed in its block, a test value and one subtree for each sign of the test value. -/
inductive Tree (σ : Type*) (α : Type*) : Type _
  | leaf (info : α) (vals : List (Expr σ))
  | test (info : α) (vals : List (Expr σ)) (c : Expr σ) (next : SignType → Tree σ α)

namespace Tree

variable {σ α : Type*}

/-- The test outcomes along the path followed by the input `x`. -/
noncomputable def path : Tree σ α → (σ → ℝ) → List SignType
  | leaf _ _, _ => []
  | test _ _ c next, x => SignType.sign (c.eval x) :: (next (SignType.sign (c.eval x))).path x

/-- The subtree reached by following a list of test outcomes. -/
def follow : Tree σ α → List SignType → Tree σ α
  | T, [] => T
  | leaf a vs, _ :: _ => leaf a vs
  | test _ _ _ next, s :: π => (next s).follow π

/-- The values computed along a list of test outcomes: the block values and test value of each
node passed, and the values of the leaf reached. -/
def valuesAlong : Tree σ α → List SignType → List (Expr σ)
  | leaf _ vs, _ => vs
  | test _ vs c _, [] => vs ++ [c]
  | test _ vs c next, s :: π => vs ++ c :: (next s).valuesAlong π

/-- The division condition of the machine model: on every input of `U`, every value computed
along the path of that input has nonzero denominators. -/
def SafeOn (T : Tree σ α) (U : Set (σ → ℝ)) : Prop :=
  ∀ x ∈ U, ∀ e ∈ T.valuesAlong (T.path x), e.Safe x

theorem follow_path_eq_leaf (T : Tree σ α) (x : σ → ℝ) :
    ∃ a vs, T.follow (T.path x) = leaf a vs := by
  induction T with
  | leaf a vs => exact ⟨a, vs, rfl⟩
  | test a vs c next ih => exact ih _

private theorem safeOn_next {a : α} {vs : List (Expr σ)} {c : Expr σ}
    {next : SignType → Tree σ α} {U : Set (σ → ℝ)} (h : (test a vs c next).SafeOn U)
    (s : SignType) :
    (next s).SafeOn {x | x ∈ U ∧ SignType.sign (c.eval x) = s} := by
  rintro x ⟨hxU, hxs⟩ e he
  apply h x hxU e
  simp only [path, valuesAlong, hxs]
  exact List.mem_append_right _ (List.mem_cons_of_mem _ he)

private theorem safe_test {a : α} {vs : List (Expr σ)} {c : Expr σ}
    {next : SignType → Tree σ α} {U : Set (σ → ℝ)} (h : (test a vs c next).SafeOn U) :
    ∀ x ∈ U, c.Safe x := by
  intro x hx
  apply h x hx c
  simp only [path, valuesAlong]
  exact List.mem_append_right _ List.mem_cons_self

private theorem isOpen_setOf_sign_eq {s : SignType} (hs : s ≠ 0) :
    IsOpen {r : ℝ | SignType.sign r = s} := by
  cases s with
  | zero => exact absurd rfl hs
  | neg =>
    have : {r : ℝ | SignType.sign r = SignType.neg} = Set.Iio 0 := by
      ext r; exact sign_eq_neg_one_iff
    rw [this]; exact isOpen_Iio
  | pos =>
    have : {r : ℝ | SignType.sign r = SignType.pos} = Set.Ioi 0 := by
      ext r; exact sign_eq_one_iff
    rw [this]; exact isOpen_Ioi

variable [Fintype σ]

private theorem exists_open_path_aux (T : Tree σ α) :
    ∀ {U : Set (σ → ℝ)}, IsOpen U → U.Nonempty → T.SafeOn U →
      ∃ π : List SignType, ∃ V ⊆ U, IsOpen V ∧ V.Nonempty ∧ ∀ x ∈ V, T.path x = π := by
  induction T with
  | leaf a vs => exact fun {U} hU hne _ => ⟨[], U, subset_rfl, hU, hne, fun _ _ => rfl⟩
  | test a vs c next ih =>
    intro U hU hne hT
    have hc := safe_test hT
    by_cases h0 : ∀ x ∈ U, c.eval x = 0
    · have hU' : {x | x ∈ U ∧ SignType.sign (c.eval x) = 0} = U := by
        ext x
        simp only [Set.mem_ofPred_eq, and_iff_left_iff_imp]
        intro hx
        rw [h0 x hx, sign_zero]
      have hnext := safeOn_next hT 0
      rw [hU'] at hnext
      obtain ⟨π, V, hVU, hV, hVne, hπ⟩ := ih 0 hU hne hnext
      refine ⟨0 :: π, V, hVU, hV, hVne, fun x hx => ?_⟩
      have hs : SignType.sign (c.eval x) = 0 := by rw [h0 x (hVU hx), sign_zero]
      simp only [path, hs, hπ x hx]
    · push Not at h0
      obtain ⟨x₀, hx₀U, hx₀⟩ := h0
      set s := SignType.sign (c.eval x₀) with hs_def
      have hs : s ≠ 0 := by rwa [hs_def, Ne, sign_eq_zero_iff]
      have hcont : ContinuousOn c.eval U := fun x hx =>
        (c.continuousAt_eval (hc x hx)).continuousWithinAt
      have hU' : IsOpen {x | x ∈ U ∧ SignType.sign (c.eval x) = s} :=
        hcont.isOpen_inter_preimage hU (isOpen_setOf_sign_eq hs)
      obtain ⟨π, V, hVU, hV, hVne, hπ⟩ :=
        ih s hU' ⟨x₀, hx₀U, hs_def.symm⟩ (safeOn_next hT s)
      refine ⟨s :: π, V, fun x hx => (hVU hx).1, hV, hVne, fun x hx => ?_⟩
      have hxs : SignType.sign (c.eval x) = s := (hVU hx).2
      simp only [path, hxs, hπ x hx]

end Tree

end OpenPath

open OpenPath

/-- **An open execution path** (`lem:open`). A finite decision tree that is division safe on a
nonempty open input set `U` has a path to a leaf that is followed by every input of a nonempty
connected open set `V ⊆ U`. Every value computed along that path is division safe and analytic
on `V`. -/
theorem exists_open_path {σ α : Type*} [Fintype σ] (T : Tree σ α) {U : Set (σ → ℝ)}
    (hU : IsOpen U) (hne : U.Nonempty) (hT : T.SafeOn U) :
    ∃ π : List SignType, (∃ a vs, T.follow π = .leaf a vs) ∧
      ∃ V ⊆ U, IsOpen V ∧ IsConnected V ∧ (∀ x ∈ V, T.path x = π) ∧
        ∀ e ∈ T.valuesAlong π, (∀ x ∈ V, e.Safe x) ∧ AnalyticOnNhd ℝ e.eval V := by
  obtain ⟨π, V, hVU, hV, ⟨x₀, hx₀⟩, hπ⟩ := Tree.exists_open_path_aux T hU hne hT
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV x₀ hx₀
  refine ⟨π, hπ x₀ hx₀ ▸ T.follow_path_eq_leaf x₀, Metric.ball x₀ ε, hball.trans hVU,
    Metric.isOpen_ball, (convex_ball x₀ ε).isConnected (Metric.nonempty_ball.mpr hε),
    fun x hx => hπ x (hball hx), fun e he => ?_⟩
  have hsafe : ∀ x ∈ Metric.ball x₀ ε, e.Safe x := fun x hx =>
    hT x (hVU (hball hx)) e (by rwa [hπ x (hball hx)])
  exact ⟨hsafe, fun x hx => e.analyticAt_eval (hsafe x hx)⟩

end ExactAttention
