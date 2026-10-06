import ExactAttention.Defs

/-!
# Numerical factorisation

This file proves the numerical factorisation lemma `lem:factor-rank` of `sec:model`. If
`F = D ∘ C` on an open set `U`, where `C` takes values in `ℝ^m`, then the derivative of `F` has
rank at most `m` at every point of `U`. The rank of a derivative is the dimension of its range.

The paper asks for continuously differentiable maps, with `D` defined on a neighbourhood of
`C(U)`. The chain rule only needs differentiability of `C` on `U` and of `D` at the points of
`C(U)`, so both statements below assume just that. They therefore cover the paper's setting.
-/

namespace ExactAttention

open Module Filter Topology

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Numerical factorisation (`lem:factor-rank`). Let `U` be open and let `F = D ∘ C` on `U`, with
`C : E → ℝ^m` differentiable on `U` and `D` differentiable at every point of `C(U)`. Then the
derivative of `F` has rank at most `m` at every point of `U`. -/
theorem finrank_range_fderiv_le_of_eqOn_comp {m : ℕ} {U : Set E} (hU : IsOpen U)
    {F : E → G} {C : E → Fin m → ℝ} {D : (Fin m → ℝ) → G}
    (hC : DifferentiableOn ℝ C U) (hD : ∀ x ∈ U, DifferentiableAt ℝ D (C x))
    (hF : Set.EqOn F (D ∘ C) U) {x : E} (hx : x ∈ U) :
    finrank ℝ (LinearMap.range (fderiv ℝ F x : E →ₗ[ℝ] G)) ≤ m := by
  have hev : F =ᶠ[𝓝 x] D ∘ C := eventuallyEq_of_mem (hU.mem_nhds hx) hF
  rw [hev.fderiv_eq, fderiv_comp x (hD x hx) (hC.differentiableAt (hU.mem_nhds hx)),
    ContinuousLinearMap.toLinearMap_comp]
  calc finrank ℝ (LinearMap.range ((fderiv ℝ D (C x) : (Fin m → ℝ) →ₗ[ℝ] G).comp
          (fderiv ℝ C x : E →ₗ[ℝ] Fin m → ℝ)))
      ≤ finrank ℝ (LinearMap.range (fderiv ℝ D (C x) : (Fin m → ℝ) →ₗ[ℝ] G)) :=
        Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
    _ ≤ finrank ℝ (Fin m → ℝ) := LinearMap.finrank_range_le _
    _ = m := by simp

/-- The last statement of `lem:factor-rank`: if `m` differentiable summaries of `p` real
coordinates can be decoded back to all `p` coordinates on a nonempty open set, then `p ≤ m`. -/
theorem le_of_eqOn_comp_id {p m : ℕ} {U : Set (Fin p → ℝ)} (hU : IsOpen U) (hne : U.Nonempty)
    {C : (Fin p → ℝ) → Fin m → ℝ} {D : (Fin m → ℝ) → Fin p → ℝ}
    (hC : DifferentiableOn ℝ C U) (hD : ∀ x ∈ U, DifferentiableAt ℝ D (C x))
    (hDC : ∀ x ∈ U, D (C x) = x) : p ≤ m := by
  obtain ⟨x, hx⟩ := hne
  have h := finrank_range_fderiv_le_of_eqOn_comp hU (F := id) hC hD
    (fun y hy => (hDC y hy).symm) hx
  rw [fderiv_id, ContinuousLinearMap.coe_id, LinearMap.range_id, finrank_top] at h
  simpa using h

end ExactAttention
