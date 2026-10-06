import Mathlib

/-!
# Linear score forms

The objects of `app:recovery`: query and key inputs, and the linear score form
`p_C(Q, K) = ∑_{ij} C_{ij} (q_i · k_j)` of a real coefficient matrix `C`.
-/

namespace ExactAttention

/-- Query and key inputs `(Q, K)`, each with `n` rows of length `d`. -/
abbrev QKInputs (n d : ℕ) := (Fin n → Fin d → ℝ) × (Fin n → Fin d → ℝ)

/-- The linear score form `p_C(Q, K) = ∑_{ij} C_{ij} (q_i · k_j)` of `app:recovery`. -/
noncomputable def scoreForm {n d : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (x : QKInputs n d) : ℝ :=
  ∑ i, ∑ j, C i j * ∑ l, x.1 i l * x.2 j l

end ExactAttention
