import Mathlib

/-!
# Shared definitions

The hypothesis of the lemma on exponentials of polynomials (`lem:independence`), and the fact
that a real polynomial vanishing on a nonempty open set is zero. The second fact is used in
`sec:model` to embed the rational function field in the field of analytic functions on an open
execution set.
-/

namespace ExactAttention

open MvPolynomial

/-- Every nonzero integer linear combination of the polynomials `p j` is nonconstant. This is the
hypothesis of `lem:independence`. -/
def IntCombNonconst {ι σ : Type*} [Fintype ι] (p : ι → MvPolynomial σ ℝ) : Prop :=
  ∀ c : ι → ℤ, c ≠ 0 → ∀ r : ℝ, ∑ j, (c j : ℝ) • p j ≠ C r

/-- A real polynomial that vanishes on a nonempty open set is the zero polynomial. -/
theorem mvPolynomial_eq_zero_of_isOpen {σ : Type*} [Fintype σ] {U : Set (σ → ℝ)}
    (hU : IsOpen U) (hne : U.Nonempty) {p : MvPolynomial σ ℝ}
    (h : ∀ x ∈ U, eval x p = 0) : p = 0 := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  refine MvPolynomial.funext_set (s := fun i => Metric.ball (x₀ i) ε) (fun i => ?_) ?_
  · rw [Real.ball_eq_Ioo]
    exact Set.Ioo_infinite (by linarith)
  · intro x hx
    rw [map_zero]
    apply h
    apply hball
    rw [ball_pi _ hε]
    exact hx

end ExactAttention
