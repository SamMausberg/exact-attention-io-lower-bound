import ExactAttention.ScoreDefs

/-!
# Rank of linear score information

This file proves `lem:pair-rank` of `app:recovery` as `linearScore_rank_bound`. If `C_1, …, C_B`
are linearly independent real `n × n` matrices and the Jacobian of `(p_{C_1}, …, p_{C_B})` has
rank at most `ρ` on a nonempty open set of inputs `(Q, K)`, then `B ≤ ρ + ρ² / (4 d²)`.

The paper applies the constant-rank theorem at a point of maximal rank. The proof here uses first
derivatives only. The Jacobian `J_x` at `x = (Q, K)` sends `(a, b)` to
`(p_{C_ℓ}(a, K) + p_{C_ℓ}(Q, b))_ℓ`, which is linear in `x`. Fix a point `x₀` of maximal rank
`ρ₀` in the open set. Since `rank (J_{x₀} + ε J_h) ≤ ρ₀` for small `ε`, the map `J_h` sends
`ker J_{x₀}` into the range of `J_{x₀}`, for every direction `h`. Let `N` be the space of
coefficient combinations `D = ∑ λ_ℓ C_ℓ` with `λ` orthogonal to that range; it has dimension at
least `B - ρ₀`. Let `Z₁` (resp. `Z₂`) be the vectors `z` with `zᵀ D = 0` (resp. `D z = 0`) for
all `D ∈ N`, of codimensions `u` and `v`. Perturbing the keys and the queries shows that every
column of `a` lies in `Z₁` and every column of `b` lies in `Z₂` when `(a, b) ∈ ker J_{x₀}`, so
`d (u + v) ≤ ρ₀`. The forms `(z, w) ↦ zᵀ D w` with `D ∈ N` vanish when `z ∈ Z₁` or
`w ∈ Z₂`, so they span at most `u v` dimensions, and `B - ρ₀ ≤ u v ≤ (u + v)² / 4`.

The file also contains `spanIO` and `spanIO_bound`, the counting step at the end of
`cor:pair-cover`. The same count closes the proof of `thm:score-exp`.
-/

namespace ExactAttention

namespace PairRank

open Finset Module Filter Topology

variable {n d B : ℕ}

/-- The family `(p_{C_ℓ}(Q, K))_ℓ` as a bilinear map of the queries and the keys. -/
noncomputable def famBilin (C : Fin B → Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → Fin d → ℝ) →ₗ[ℝ] (Fin n → Fin d → ℝ) →ₗ[ℝ] (Fin B → ℝ) :=
  LinearMap.mk₂ ℝ (fun Q K ℓ => scoreForm (C ℓ) (Q, K))
    (fun Q Q' K => by
      funext ℓ
      simp [scoreForm, add_mul, mul_add, Finset.sum_add_distrib])
    (fun c Q K => by
      funext ℓ
      simp [scoreForm, Finset.mul_sum, mul_assoc, mul_left_comm])
    (fun Q K K' => by
      funext ℓ
      simp [scoreForm, mul_add, Finset.sum_add_distrib])
    (fun c Q K => by
      funext ℓ
      simp [scoreForm, Finset.mul_sum, mul_left_comm])

lemma famBilin_apply (C : Fin B → Matrix (Fin n) (Fin n) ℝ) (Q K : Fin n → Fin d → ℝ)
    (ℓ : Fin B) : famBilin C Q K ℓ = scoreForm (C ℓ) (Q, K) := rfl

/-- The Jacobian of `x ↦ (p_{C_ℓ}(x))_ℓ` at `x = (Q, K)`:
`(a, b) ↦ (p_{C_ℓ}(Q, b) + p_{C_ℓ}(a, K))_ℓ`. -/
noncomputable def jac (C : Fin B → Matrix (Fin n) (Fin n) ℝ) (x : QKInputs n d) :
    QKInputs n d →ₗ[ℝ] (Fin B → ℝ) :=
  famBilin C x.1 ∘ₗ LinearMap.snd ℝ _ _ + (famBilin C).flip x.2 ∘ₗ LinearMap.fst ℝ _ _

lemma jac_apply (C : Fin B → Matrix (Fin n) (Fin n) ℝ) (x y : QKInputs n d) :
    jac C x y = famBilin C x.1 y.2 + famBilin C y.1 x.2 := rfl

/-- The Jacobian is linear in the base point. -/
lemma jac_add_smul (C : Fin B → Matrix (Fin n) (Fin n) ℝ) (x h : QKInputs n d) (ε : ℝ) :
    jac C (x + ε • h) = jac C x + ε • jac C h := by
  refine LinearMap.ext fun y => ?_
  simp only [jac_apply, LinearMap.add_apply, LinearMap.smul_apply, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, map_add, map_smul, smul_add]
  abel

/-- `famBilin` as a continuous bilinear map. -/
private noncomputable def famCLM (C : Fin B → Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → Fin d → ℝ) →L[ℝ] (Fin n → Fin d → ℝ) →L[ℝ] (Fin B → ℝ) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      ((Fin n → Fin d → ℝ) →ₗ[ℝ] (Fin B → ℝ)) ≃ₗ[ℝ] ((Fin n → Fin d → ℝ) →L[ℝ] (Fin B → ℝ))) ∘ₗ
        famBilin C)

lemma hasFDerivAt_scoreForms (C : Fin B → Matrix (Fin n) (Fin n) ℝ) (x : QKInputs n d) :
    HasFDerivAt (fun y (ℓ : Fin B) => scoreForm (C ℓ) y)
      (LinearMap.toContinuousLinearMap (jac C x)) x := by
  have h := (famCLM C).isBoundedBilinearMap.hasFDerivAt x
  refine h.congr_fderiv (ContinuousLinearMap.ext fun y => ?_)
  rw [IsBoundedBilinearMap.deriv_apply]
  rfl

lemma finrank_range_fderiv_scoreForms (C : Fin B → Matrix (Fin n) (Fin n) ℝ)
    (x : QKInputs n d) :
    finrank ℝ (LinearMap.range (fderiv ℝ (fun y (ℓ : Fin B) => scoreForm (C ℓ) y) x :
      QKInputs n d →ₗ[ℝ] (Fin B → ℝ))) =
      finrank ℝ (LinearMap.range (jac C x)) := by
  rw [(hasFDerivAt_scoreForms C x).fderiv]
  rfl

/-- `p_C(x)` as a linear function of the coefficient matrix `C`. -/
private noncomputable def scoreFormLin (x : QKInputs n d) : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ where
  toFun C := scoreForm C x
  map_add' C C' := by simp [scoreForm, add_mul, Finset.sum_add_distrib]
  map_smul' c C := by simp [scoreForm, Finset.mul_sum, mul_assoc]

lemma dotProduct_famBilin (C : Fin B → Matrix (Fin n) (Fin n) ℝ) (lam : Fin B → ℝ)
    (Q K : Fin n → Fin d → ℝ) :
    lam ⬝ᵥ famBilin C Q K = scoreForm (Fintype.linearCombination ℝ C lam) (Q, K) := by
  have h := map_sum (scoreFormLin (Q, K)) (fun ℓ => lam ℓ • C ℓ) univ
  simp only [map_smul, smul_eq_mul] at h
  simp only [dotProduct, famBilin_apply, Fintype.linearCombination_apply]
  exact h.symm

/-- The bilinear form `(z, w) ↦ zᵀ D w` on `ℝⁿ`. -/
noncomputable def bil (D : Matrix (Fin n) (Fin n) ℝ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  Matrix.toLinearMap₂' ℝ D

lemma bil_injective : Function.Injective (bil (n := n)) :=
  (Matrix.toLinearMap₂' ℝ : Matrix (Fin n) (Fin n) ℝ ≃ₗ[ℝ]
    (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) →ₗ[ℝ] ℝ).injective

/-- The keys with column `l` equal to `w` and all other columns zero. -/
def colEmbed (l : Fin d) (w : Fin n → ℝ) : Fin n → Fin d → ℝ :=
  fun j l' => if l' = l then w j else 0

lemma scoreForm_colEmbed_right (D : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → Fin d → ℝ)
    (l : Fin d) (w : Fin n → ℝ) :
    scoreForm D (a, colEmbed l w) = bil D (fun i => a i l) w := by
  simp only [bil, scoreForm, colEmbed, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Matrix.toLinearMap₂'_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma scoreForm_colEmbed_left (D : Matrix (Fin n) (Fin n) ℝ) (l : Fin d) (z : Fin n → ℝ)
    (b : Fin n → Fin d → ℝ) :
    scoreForm D (colEmbed l z, b) = bil D z (fun j => b j l) := by
  simp only [bil, scoreForm, colEmbed, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Matrix.toLinearMap₂'_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Perturbation of rank. If `rank (A + ε H) ≤ rank A` for all small `ε`, then `H` maps the
kernel of `A` into the range of `A`. -/
lemma mem_range_of_eventually_finrank_le {E W : Type*} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (A H : E →ₗ[ℝ] W)
    (h : ∀ᶠ ε : ℝ in 𝓝 0,
      finrank ℝ (LinearMap.range (A + ε • H)) ≤ finrank ℝ (LinearMap.range A))
    {y : E} (hy : A y = 0) : H y ∈ LinearMap.range A := by
  by_contra hHy
  set r := finrank ℝ (LinearMap.range A) with hr
  let b := Module.finBasis ℝ (LinearMap.range A)
  choose u hu using fun i => LinearMap.mem_range.1 (b i).2
  let f : ℝ → Option (Fin r) → W := fun ε o =>
    Option.casesOn' o (H y) fun i => (A + ε • H) (u i)
  have hf0 : LinearIndependent ℝ (f 0) := by
    rw [linearIndependent_option]
    have hcomp : (f 0 ∘ (↑) : Fin r → W) = (LinearMap.range A).subtype ∘ b := by
      funext i
      simp [f, hu]
    rw [hcomp]
    refine ⟨b.linearIndependent.map' _ (Submodule.ker_subtype _), fun hmem => hHy ?_⟩
    have hle : Submodule.span ℝ (Set.range ((LinearMap.range A).subtype ∘ b)) ≤
        LinearMap.range A :=
      Submodule.span_le.2 (Set.range_subset_iff.2 fun i => (b i).2)
    exact hle hmem
  have hcont : Continuous f := by
    refine continuous_pi fun o => ?_
    cases o with
    | none => exact continuous_const
    | some i =>
      simp only [f, Option.casesOn'_some, LinearMap.add_apply, LinearMap.smul_apply]
      fun_prop
  have hli : ∀ᶠ ε in 𝓝 (0 : ℝ), LinearIndependent ℝ (f ε) :=
    (hcont.tendsto 0).eventually hf0.eventually
  obtain ⟨ε, ⟨hεli, hεr⟩, hε0⟩ :=
    (((hli.and h).filter_mono nhdsWithin_le_nhds).and
      (eventually_mem_nhdsWithin (s := {0}ᶜ) (a := (0 : ℝ)))).exists
  have hε0' : ε ≠ 0 := hε0
  have hsub : Set.range (f ε) ⊆ LinearMap.range (A + ε • H) := by
    rintro _ ⟨o, rfl⟩
    cases o with
    | none =>
      refine ⟨ε⁻¹ • y, ?_⟩
      simp [f, hy, smul_smul, hε0']
    | some i => exact ⟨u i, rfl⟩
  have h1 := finrank_span_eq_card hεli
  have h2 := Submodule.finrank_mono (Submodule.span_le.2 hsub)
  simp only [Fintype.card_option, Fintype.card_fin] at h1
  omega

end PairRank

open Finset Module Filter Topology PairRank

/-- Rank of linear score information (`lem:pair-rank`). Let `C_1, …, C_B` be linearly independent
real `n × n` matrices, with `d > 0`. If the Jacobian of `(p_{C_1}, …, p_{C_B})` with respect to
`(Q, K)` has rank at most `ρ` at every point of a nonempty open set, then
`B ≤ ρ + ρ² / (4 d²)`. The generic rank is the largest rank attained, so the paper's statement is
the case where `ρ` is that rank and the open set is the whole input space. -/
theorem linearScore_rank_bound {n d B : ℕ} (hd : 0 < d)
    (C : Fin B → Matrix (Fin n) (Fin n) ℝ) (hC : LinearIndependent ℝ C)
    {U : Set (QKInputs n d)} (hU : IsOpen U) (hne : U.Nonempty) {ρ : ℕ}
    (hρ : ∀ x ∈ U, Module.finrank ℝ
      (LinearMap.range (fderiv ℝ (fun y (ℓ : Fin B) => scoreForm (C ℓ) y) x :
        QKInputs n d →ₗ[ℝ] (Fin B → ℝ))) ≤ ρ) :
    (B : ℝ) ≤ ρ + ρ ^ 2 / (4 * d ^ 2) := by
  classical
  set r : QKInputs n d → ℕ := fun x => finrank ℝ (LinearMap.range (jac C x)) with hr
  have hρ' : ∀ x ∈ U, r x ≤ ρ := fun x hx => by
    simpa only [hr, finrank_range_fderiv_scoreForms] using hρ x hx
  -- A point of maximal rank.
  obtain ⟨x₀, hx₀, hmax⟩ : ∃ x₀ ∈ U, ∀ x ∈ U, r x ≤ r x₀ := by
    have hbdd : BddAbove (r '' U) := ⟨ρ, by rintro _ ⟨x, hx, rfl⟩; exact hρ' x hx⟩
    obtain ⟨x₀, hx₀, hx₀eq⟩ := Nat.sSup_mem (hne.image r) hbdd
    exact ⟨x₀, hx₀, fun x hx => hx₀eq ▸ le_csSup hbdd ⟨x, hx, rfl⟩⟩
  set A := jac C x₀ with hA
  -- Every Jacobian `J_h` maps `ker A` into the range of `A`.
  have hpert : ∀ h : QKInputs n d, ∀ y, A y = 0 → jac C h y ∈ LinearMap.range A := by
    intro h y hy
    refine mem_range_of_eventually_finrank_le A (jac C h) ?_ hy
    have hmem : ∀ᶠ ε : ℝ in 𝓝 0, x₀ + ε • h ∈ U := by
      have hc : Continuous fun ε : ℝ => x₀ + ε • h := by fun_prop
      exact (hc.tendsto' 0 x₀ (by simp)).eventually (hU.mem_nhds hx₀)
    filter_upwards [hmem] with ε hε
    rw [hA, ← jac_add_smul]
    exact hmax _ hε
  -- The coefficient vectors orthogonal to the range of `A`.
  let e : (Fin B → ℝ) →ₗ[ℝ] Module.Dual ℝ (Fin B → ℝ) :=
    LinearMap.mk₂ ℝ (fun lam z => lam ⬝ᵥ z) add_dotProduct smul_dotProduct dotProduct_add
      dotProduct_smul
  let Λ := A.dualMap ∘ₗ e
  set N := LinearMap.ker Λ with hNdef
  have hNdim : B ≤ r x₀ + finrank ℝ N := by
    have h1 : finrank ℝ (LinearMap.range Λ) + finrank ℝ N = B := by
      rw [hNdef, LinearMap.finrank_range_add_finrank_ker, Module.finrank_fin_fun]
    have h2 : finrank ℝ (LinearMap.range Λ) ≤ r x₀ :=
      (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)).trans
        (LinearMap.finrank_range_dualMap_eq_finrank_range A).le
    omega
  have hN : ∀ lam ∈ N, ∀ y, lam ⬝ᵥ A y = 0 := fun lam hlam y =>
    LinearMap.congr_fun (LinearMap.mem_ker.1 hlam) y
  let G : (Fin B → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ := Fintype.linearCombination ℝ C
  have hG : ∀ lam, G lam = 0 → lam = 0 := fun lam h0 =>
    funext (Fintype.linearIndependent_iff.1 hC lam (by
      simpa [G, Fintype.linearCombination_apply] using h0))
  -- The common left and right kernels of the bilinear forms `zᵀ D w`, `D ∈ N`.
  let Z₁ : Submodule ℝ (Fin n → ℝ) := ⨅ lam ∈ N, LinearMap.ker (bil (G lam))
  let Z₂ : Submodule ℝ (Fin n → ℝ) := ⨅ lam ∈ N, LinearMap.ker (bil (G lam)).flip
  have hker : ∀ y, A y = 0 → ∀ l, (fun i => y.1 i l) ∈ Z₁ ∧ (fun j => y.2 j l) ∈ Z₂ := by
    intro y hy l
    simp only [Z₁, Z₂, Submodule.mem_iInf, LinearMap.mem_ker]
    refine ⟨fun lam hlam => LinearMap.ext fun w => ?_, fun lam hlam => LinearMap.ext fun z => ?_⟩
    · obtain ⟨y', hy'⟩ := hpert (0, colEmbed l w) y hy
      have h0 := hN lam hlam y'
      rw [hy', jac_apply, map_zero, LinearMap.zero_apply, zero_add, dotProduct_famBilin,
        scoreForm_colEmbed_right] at h0
      exact h0
    · obtain ⟨y', hy'⟩ := hpert (colEmbed l z, 0) y hy
      have h0 := hN lam hlam y'
      rw [hy', jac_apply, map_zero, add_zero, dotProduct_famBilin, scoreForm_colEmbed_left] at h0
      exact h0
  obtain ⟨P₁, hP₁⟩ := Z₁.exists_isCompl
  obtain ⟨P₂, hP₂⟩ := Z₂.exists_isCompl
  -- Rank: `d (u + v) ≤ ρ₀`.
  have h6 : d * (finrank ℝ P₁ + finrank ℝ P₂) ≤ r x₀ := by
    let J : ((Fin d → P₁) × (Fin d → P₂)) →ₗ[ℝ] QKInputs n d :=
      { toFun := fun αβ => (fun i l => (αβ.1 l : Fin n → ℝ) i, fun j l => (αβ.2 l : Fin n → ℝ) j)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective (A ∘ₗ J) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro αβ h0
      have hk := hker (J αβ) h0
      refine Prod.ext (funext fun l => ?_) (funext fun l => ?_)
      · exact Subtype.ext (Submodule.disjoint_def.1 hP₁.disjoint _ (hk l).1 (αβ.1 l).2)
      · exact Subtype.ext (Submodule.disjoint_def.1 hP₂.disjoint _ (hk l).2 (αβ.2 l).2)
    calc d * (finrank ℝ P₁ + finrank ℝ P₂) = finrank ℝ ((Fin d → P₁) × (Fin d → P₂)) := by
          rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_pi_fintype]
          simp [mul_add]
      _ = finrank ℝ (LinearMap.range (A ∘ₗ J)) := (LinearMap.finrank_range_of_inj hinj).symm
      _ ≤ r x₀ := Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  -- Dimension: `dim N ≤ u v`.
  have h7 : finrank ℝ N ≤ finrank ℝ P₁ * finrank ℝ P₂ := by
    let Φ : (Fin B → ℝ) →ₗ[ℝ] (P₁ →ₗ[ℝ] P₂ →ₗ[ℝ] ℝ) :=
      { toFun := fun lam => (bil (G lam)).compl₁₂ P₁.subtype P₂.subtype
        map_add' := fun _ _ => by ext; simp [bil]
        map_smul' := fun _ _ => by ext; simp [bil] }
    have hinj : Function.Injective (Φ ∘ₗ N.subtype) := by
      refine (injective_iff_map_eq_zero (Φ ∘ₗ N.subtype)).2 ?_
      rintro ⟨lam, hlam⟩ h0
      refine Subtype.ext (hG lam (bil_injective ?_))
      rw [show bil (0 : Matrix (Fin n) (Fin n) ℝ) = 0 from map_zero _]
      refine LinearMap.ext fun z => LinearMap.ext fun w => ?_
      obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ :=
        Submodule.mem_sup.1 (hP₁.sup_eq_top ▸ Submodule.mem_top : z ∈ Z₁ ⊔ P₁)
      obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ :=
        Submodule.mem_sup.1 (hP₂.sup_eq_top ▸ Submodule.mem_top : w ∈ Z₂ ⊔ P₂)
      have a1 : bil (G lam) z₁ = 0 := by
        simp only [Z₁, Submodule.mem_iInf, LinearMap.mem_ker] at hz₁
        exact hz₁ lam hlam
      have a2 : (bil (G lam)).flip w₁ = 0 := by
        simp only [Z₂, Submodule.mem_iInf, LinearMap.mem_ker] at hw₁
        exact hw₁ lam hlam
      have a3 : bil (G lam) z₂ w₂ = 0 :=
        LinearMap.congr_fun (LinearMap.congr_fun h0 ⟨z₂, hz₂⟩) ⟨w₂, hw₂⟩
      have a2' : bil (G lam) z₂ w₁ = 0 := LinearMap.congr_fun a2 z₂
      have b1 : ∀ w, bil (G lam) z₁ w = 0 := fun w => by rw [a1]; rfl
      simp only [map_add, LinearMap.add_apply, b1, a2', a3, add_zero,
        LinearMap.zero_apply]
    calc finrank ℝ N ≤ finrank ℝ (P₁ →ₗ[ℝ] P₂ →ₗ[ℝ] ℝ) :=
          LinearMap.finrank_le_finrank_of_injective hinj
      _ = finrank ℝ P₁ * finrank ℝ P₂ := by
          rw [Module.finrank_linearMap, Module.finrank_linearMap_self]
  -- Arithmetic.
  have hρ₀ : r x₀ ≤ ρ := hρ' x₀ hx₀
  set u := finrank ℝ P₁
  set v := finrank ℝ P₂
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have e1 : (B : ℝ) ≤ ρ + u * v := by exact_mod_cast (by omega : B ≤ ρ + u * v)
  have e2 : (d : ℝ) * (u + v) ≤ ρ := by exact_mod_cast h6.trans hρ₀
  have e3 : (u * v : ℝ) ≤ ρ ^ 2 / (4 * d ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    have h0 : (0 : ℝ) ≤ d * (u + v) := by positivity
    nlinarith [mul_self_le_mul_self h0 e2, mul_nonneg (sq_nonneg (d : ℝ)) (sq_nonneg ((u : ℝ) - v))]
  linarith

/-- The bound `eq:span-io` in the proof of `cor:pair-cover`. Suppose `e` epochs each contribute a
coefficient space of dimension at most `3M² / d²`, these spaces together span at least
`n (n - 1)` dimensions, and `e ≤ I / M + 1` (`eq:epochs`). Then
`I ≥ n (n - 1) d² / (3M) - M`. -/
theorem spanIO {n d M e I : ℕ} (hd : 0 < d) (hM : 0 < M)
    (hcov : (n : ℝ) * (n - 1) ≤ e * (3 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2))
    (he : (e : ℝ) ≤ I / M + 1) :
    (n : ℝ) * (n - 1) * (d : ℝ) ^ 2 / (3 * M) - M ≤ I := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : (n : ℝ) * (n - 1) ≤ (I / M + 1) * (3 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2) :=
    hcov.trans (mul_le_mul_of_nonneg_right he (by positivity))
  have h2 : ((I : ℝ) / M + 1) * (3 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2) =
      3 * M * (I + M) / (d : ℝ) ^ 2 := by
    field_simp
  rw [h2, le_div_iff₀ (by positivity)] at h1
  rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
  linarith

/-- The counting step at the end of `cor:pair-cover`. The proof of `thm:score-exp` ends with the
same count. Suppose
`e` epochs each contribute a coefficient space of dimension at most `3M² / d²`, these spaces
together span at least `n (n - 1)` dimensions, `e ≤ I / M + 1` (`eq:epochs`), and the `I`
transfers include the `n d` output stores. If `d ≥ 1` and `d² ≤ M`, then
`I ≥ (n d + n² d² / M) / 16`. -/
theorem spanIO_bound {n d M e I : ℕ} (hd : 0 < d) (hM : d ^ 2 ≤ M)
    (hcov : (n : ℝ) * (n - 1) ≤ e * (3 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2))
    (he : (e : ℝ) ≤ I / M + 1) (hI : n * d ≤ I) :
    ((n : ℝ) * d + (n : ℝ) ^ 2 * (d : ℝ) ^ 2 / M) / 16 ≤ I := by
  have hM0 : 0 < M := lt_of_lt_of_le (pow_pos hd 2) hM
  have hs := spanIO hd hM0 hcov he
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM0
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : (d : ℝ) ^ 2 ≤ M := by exact_mod_cast hM
  have hdM : (d : ℝ) ≤ M := by nlinarith
  have hXI : (n : ℝ) * d ≤ I := by exact_mod_cast hI
  have hX0 : (0 : ℝ) ≤ n * d := by positivity
  set X : ℝ := n * d with hX
  set Y : ℝ := X ^ 2 / M with hY
  have hYM : Y * M = X ^ 2 := by rw [hY]; field_simp
  have hnY : (n : ℝ) ^ 2 * (d : ℝ) ^ 2 / M = Y := by rw [hY, hX]; ring
  rw [hnY]
  rcases lt_or_ge X (8 * M) with h | h
  · have hY8 : Y ≤ 8 * X := by nlinarith
    linarith
  · have h8 : 8 * (d : ℝ) ≤ n * d := by linarith
    have hn : (8 : ℝ) ≤ n := le_of_mul_le_mul_right h8 (by linarith)
    have hs' : Y / 6 - M ≤ I := by
      have : Y / 6 ≤ (n : ℝ) * (n - 1) * (d : ℝ) ^ 2 / (3 * M) := by
        rw [hY, hX, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have hn2 : (0 : ℝ) ≤ ((n : ℝ) - 2) * ((n : ℝ) * (d : ℝ) ^ 2) * M :=
          mul_nonneg (mul_nonneg (by linarith) (by positivity)) hM'.le
        nlinarith
      linarith
    have hMY : 64 * M ≤ Y := by nlinarith
    linarith

end ExactAttention
