import ExactAttention.CoefficientField
import ExactAttention.AnalyticField
import ExactAttention.History

/-!
# The attention lower bound from a derivative trace (`thm:attention`)

This file joins the coefficient field results of `prop:attention-field` to the derivative
history of `thm:history`. Fix a nonempty connected open set `U` of inputs `x : Coord n d → ℝ`.
The ambient field is `K = AnalyticFunctionField U`, and the base field is the rational function
field `F = ℝ(Q, K, V)`, which acts on `K` through `ratFuncToAnalytic`.

* `Main.attnJacobian U i l c` is the class in `K` of the analytic function
  `x ↦ ∂Y_{il}/∂x_c`, defined with `fderiv`. As `c` varies it is the Jacobian row of `Y_{il}`.
* `Main.ratioElem U i j` is the class in `K` of `R_{ij} = exp (q_i · (k_j - k_n))`.

`ratio_algebraicIndependent` shows that the `n(n-1)` ratios `R_{ij}` (`j < n`) are
algebraically independent over `F` in `K`. `ratio_eq_jacobian_div` shows
`R_{ij} = (∂Y_{il}/∂V_{jl}) / (∂Y_{il}/∂V_{nl})` in `K`. Together with
`attention_bound_of_trace` they give `attention_io_lower_bound`: every derivative trace over `F`
in `K` whose output words carry the Jacobian rows of `Y`, and which makes at least `nd`
transfers, satisfies `eq:main-lower`.

The step from a program in the machine model to such a trace (choosing the open execution path
by `lem:open` and reading off local Jacobians by `lem:boundary`) is not formalized, so the trace
and the `nd` output stores are hypotheses. The local Jacobians of the trace are arbitrary
matrices over `K`. The results proved in `OpenPath.lean` and `History.lean` for the step from a
program to a trace are not used here.
-/

open MvPolynomial

namespace ExactAttention

open CoefficientField History

namespace Main

section Field

variable {σ : Type*} [Fintype σ] (U : Set (σ → ℝ)) [Fact (IsOpen U)] [Fact (IsConnected U)]

/-- The rational function field `ℝ(x)` acts on the analytic function field through
`ratFuncToAnalytic`. -/
noncomputable instance ratFuncAlgebra :
    Algebra (FractionRing (MvPolynomial σ ℝ)) (AnalyticFunctionField U) :=
  (ratFuncToAnalytic U).toRingHom.toAlgebra

theorem algebraMap_ratFunc (z : FractionRing (MvPolynomial σ ℝ)) :
    algebraMap (FractionRing (MvPolynomial σ ℝ)) (AnalyticFunctionField U) z =
      ratFuncToAnalytic U z :=
  rfl

/-- The coordinate functions as elements of the analytic function field. -/
noncomputable def coordK (c : σ) : AnalyticFunctionField U :=
  algebraMap (analyticRing U) _ (AnalyticField.coord U c)

/-- The image of `ℝ(x)` lies in the field generated over `ℝ` by the coordinates. -/
theorem ratFunc_mem_adjoin (z : FractionRing (MvPolynomial σ ℝ)) :
    algebraMap _ (AnalyticFunctionField U) z ∈
      IntermediateField.adjoin ℝ (Set.range (coordK U)) := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial σ ℝ) z
  have key : ∀ a : MvPolynomial σ ℝ,
      algebraMap _ (AnalyticFunctionField U) (algebraMap _ (FractionRing (MvPolynomial σ ℝ)) a) ∈
        IntermediateField.adjoin ℝ (Set.range (coordK U)) := by
    intro a
    rw [algebraMap_ratFunc, ratFuncToAnalytic_algebraMap]
    apply IntermediateField.algebra_adjoin_le_adjoin
    rw [Algebra.adjoin_range_eq_range_aeval]
    refine ⟨a, ?_⟩
    rw [show coordK U = fun c => algebraMap (analyticRing U) _ (AnalyticField.coord U c) from rfl]
    have := congrArg (fun φ : MvPolynomial σ ℝ →ₐ[ℝ] AnalyticFunctionField U => φ a)
      (comp_aeval (R := ℝ) (AnalyticField.coord U)
        (IsScalarTower.toAlgHom ℝ (analyticRing U) (AnalyticFunctionField U)))
    simpa [polyToAnalytic] using this.symm
  rw [map_div₀]
  exact IntermediateField.div_mem _ (key a) (key b)

/-- The partial derivative `x ↦ ∂f/∂x_c` of a function analytic on `U`, as an element of the
analytic ring. -/
noncomputable def partialElem [DecidableEq σ] (f : (σ → ℝ) → ℝ) (hf : AnalyticOnNhd ℝ f U)
    (c : σ) : analyticRing U :=
  ⟨fun x : U => fderiv ℝ f x (Pi.single c 1),
    AnalyticField.restrict_mem (f := fun x => fderiv ℝ f x (Pi.single c 1)) fun x hx => by
      have h := ((ContinuousLinearMap.apply ℝ ℝ (Pi.single c (1 : ℝ))).analyticAt
        (fderiv ℝ f x)).comp (hf.fderiv x hx)
      exact h⟩

end Field

variable {n m d : ℕ}

private theorem analyticAt_coord (c : Coord n d) (x : Coord n d → ℝ) :
    AnalyticAt ℝ (fun x : Coord n d → ℝ => x c) x :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Coord n d => ℝ) c).analyticAt x

private theorem analyticAt_kernel (i j : Fin n) (x : Coord n d → ℝ) :
    AnalyticAt ℝ (fun x : Coord n d → ℝ => attnKernel (qMat x) (kMat x) i j) x := by
  simp only [attnKernel, qMat, kMat]
  exact (Finset.analyticAt_fun_sum _ fun l _ =>
    (analyticAt_coord _ x).mul (analyticAt_coord _ x)).rexp'

private theorem attnWeight_pos (Q K : Fin n → Fin d → ℝ) (i j : Fin n) :
    0 < attnWeight Q K i j :=
  div_pos (attnKernel_pos Q K i j)
    (Finset.sum_pos (fun h _ => attnKernel_pos Q K i h) ⟨j, Finset.mem_univ j⟩)

private theorem analyticAt_weight (i j : Fin n) (x : Coord n d → ℝ) :
    AnalyticAt ℝ (fun x : Coord n d → ℝ => attnWeight (qMat x) (kMat x) i j) x := by
  simp only [attnWeight]
  exact (analyticAt_kernel i j x).fun_div
    (Finset.analyticAt_fun_sum _ fun h _ => analyticAt_kernel i h x)
    (Finset.sum_pos (fun h _ => attnKernel_pos _ _ i h) ⟨j, Finset.mem_univ j⟩).ne'

/-- The output entry `Y_{il}` as a function of the input point. -/
noncomputable def outFun (i : Fin n) (l : Fin d) (x : Coord n d → ℝ) : ℝ :=
  attnOutput (qMat x) (kMat x) (vMat x) i l

theorem analyticAt_outFun (i : Fin n) (l : Fin d) (x : Coord n d → ℝ) :
    AnalyticAt ℝ (outFun i l) x := by
  unfold outFun
  simp only [attnOutput, vMat]
  exact Finset.analyticAt_fun_sum _ fun j _ =>
    (analyticAt_weight i j x).mul (analyticAt_coord _ x)

/-- The ratio `R_{ij}` as a function of the input point. -/
noncomputable def ratioFun (i j : Fin (m + 1)) (x : Coord (m + 1) d → ℝ) : ℝ :=
  attnRatio (qMat x) (kMat x) i j

theorem analyticAt_ratioFun (i j : Fin (m + 1)) (x : Coord (m + 1) d → ℝ) :
    AnalyticAt ℝ (ratioFun i j) x := by
  have : ratioFun (d := d) i j = fun x => Real.exp (eval x (ratioExponent i j)) := by
    funext x
    exact attnRatio_eq_exp_eval x i j
  rw [this]
  exact (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℝ) (ratioExponent i j) x (Set.mem_univ x)).rexp'

/-- `∂Y_{il}/∂V_{jl} = A_{ij}` at every input point, computed with `fderiv`. -/
theorem fderiv_outFun_v (i j : Fin n) (l : Fin d) (x : Coord n d → ℝ) :
    fderiv ℝ (outFun i l) x (Pi.single (Coord.v j l) 1) = attnWeight (qMat x) (kMat x) i j := by
  have hY : HasFDerivAt (outFun i l) (fderiv ℝ (outFun i l) x)
      (Function.update x (Coord.v j l) (x (Coord.v j l))) := by
    rw [Function.update_eq_self]
    exact (analyticAt_outFun i l x).differentiableAt.hasFDerivAt
  have h1 := hY.comp_hasDerivAt (x (Coord.v j l)) (hasDerivAt_update x (Coord.v j l) _)
  have hfun : outFun i l ∘ Function.update x (Coord.v j l) = fun t =>
      attnOutput (qMat x) (kMat x) (Function.update (vMat x) j (Function.update (vMat x j) l t))
        i l := by
    funext t
    have hq : qMat (Function.update x (Coord.v j l) t) = qMat x := by
      funext i' l'
      simp [qMat]
    have hk : kMat (Function.update x (Coord.v j l) t) = kMat x := by
      funext i' l'
      simp [kMat]
    have hv : vMat (Function.update x (Coord.v j l) t) =
        Function.update (vMat x) j (Function.update (vMat x j) l t) := by
      funext j' l'
      by_cases hj : j' = j
      · subst hj
        by_cases hl : l' = l
        · subst hl
          simp [vMat]
        · simp [vMat, hl]
      · simp [vMat, hj]
    simp only [Function.comp_apply, outFun, hq, hk, hv]
  rw [hfun] at h1
  have h2 := hasDerivAt_attnOutput_value (qMat x) (kMat x) (vMat x) i j l l
  simp only [↓reduceIte] at h2
  exact h1.unique h2

section Elements

variable (U : Set (Coord n d → ℝ)) [Fact (IsOpen U)] [Fact (IsConnected U)]

/-- The class in `K` of the partial derivative `∂Y_{il}/∂x_c`. For fixed `(i, l)`, the map
`c ↦ attnJacobian U i l c` is the Jacobian row of `Y_{il}`. -/
noncomputable def attnJacobian (i : Fin n) (l : Fin d) (c : Coord n d) :
    AnalyticFunctionField U :=
  algebraMap (analyticRing U) _ (partialElem U (outFun i l) (fun x _ => analyticAt_outFun i l x) c)

end Elements

section Ratios

variable (U : Set (Coord (m + 1) d → ℝ)) [Fact (IsOpen U)] [Fact (IsConnected U)]

/-- The ratio `R_{ij}` as an element of the analytic ring. -/
noncomputable def ratioRingElem (i j : Fin (m + 1)) : analyticRing U :=
  ⟨fun x : U => ratioFun i j (x : Coord (m + 1) d → ℝ),
    AnalyticField.restrict_mem fun x _ => analyticAt_ratioFun i j x⟩

/-- The class of `R_{ij}` in the analytic function field. -/
noncomputable def ratioElem (i j : Fin (m + 1)) : AnalyticFunctionField U :=
  algebraMap (analyticRing U) _ (ratioRingElem U i j)

end Ratios

end Main

open Main

variable {n m d : ℕ}

/-- **The ratios are independent in the analytic function field** (`prop:attention-field`). On a
nonempty connected open set `U` of inputs with `d ≥ 1`, the `n(n-1)` ratios `R_{ij}` (`j < n`)
are algebraically independent over `ℝ(Q, K, V)` in the fraction field of analytic functions on
`U`. -/
theorem ratio_algebraicIndependent (hd : 0 < d) (U : Set (Coord (m + 1) d → ℝ))
    [Fact (IsOpen U)] [Fact (IsConnected U)] :
    AlgebraicIndependent (FractionRing (MvPolynomial (Coord (m + 1) d) ℝ))
      (fun ij : Fin (m + 1) × Fin m => ratioElem U ij.1 ij.2.castSucc) := by
  have hU : IsOpen U := Fact.out
  have hne : U.Nonempty := (Fact.out : IsConnected U).nonempty
  set r' : Fin (m + 1) × Fin m → analyticRing U := fun ij => ratioRingElem U ij.1 ij.2.castSucc
  set c' := AnalyticField.coord U
  have h1 : AlgebraicIndependent ℝ (Sum.elim r' c') := by
    refine AlgebraicIndependent.of_comp (analyticRing U).val ?_
    convert attnRatio_algebraicIndependent hd hU hne using 1
    ext (ij | c) x <;> rfl
  set f := IsScalarTower.toAlgHom ℝ (analyticRing U) (AnalyticFunctionField U)
  have h2 : AlgebraicIndependent ℝ (Sum.elim (f ∘ r') (f ∘ c')) := by
    rw [← Sum.comp_elim]
    exact h1.map' (IsFractionRing.injective _ _)
  have h3 := (AlgebraicIndependent.sumElim_iff.mp h2).2
  have h4 := IntermediateField.algebraicIndependent_adjoin_iff.mpr h3
  have hc : Set.range (f ∘ c') = Set.range (coordK U) := rfl
  have hmem : ∀ z, algebraMap (FractionRing (MvPolynomial (Coord (m + 1) d) ℝ))
      (AnalyticFunctionField U) z ∈ IntermediateField.adjoin ℝ (Set.range (f ∘ c')) := by
    rw [hc]
    exact ratFunc_mem_adjoin U
  let φ := (algebraMap (FractionRing (MvPolynomial (Coord (m + 1) d) ℝ))
    (AnalyticFunctionField U)).codRestrict (IntermediateField.adjoin ℝ (Set.range (f ∘ c'))) hmem
  exact AlgebraicIndependent.of_ringHom_of_comp_eq φ (RingHom.id _) h4 φ.injective
    (RingHom.ext fun _ => rfl)

/-- **Ratios from output derivatives** (`prop:attention-field`, the containment `𝒯 ⊆ F₀(DY)`).
In the analytic function field, `R_{ij} = (∂Y_{il}/∂V_{jl}) / (∂Y_{il}/∂V_{nl})`. -/
theorem ratio_eq_jacobian_div (U : Set (Coord (m + 1) d → ℝ)) [Fact (IsOpen U)]
    [Fact (IsConnected U)] (i j : Fin (m + 1)) (l : Fin d) :
    ratioElem U i j =
      attnJacobian U i l (Coord.v j l) / attnJacobian U i l (Coord.v (Fin.last m) l) := by
  have hpt : ∀ x : Coord (m + 1) d → ℝ,
      ratioFun i j x * attnWeight (qMat x) (kMat x) i (Fin.last m) =
        attnWeight (qMat x) (kMat x) i j := by
    intro x
    have h := attnWeight_div_last (qMat x) (kMat x) i j
    have hpos := attnWeight_pos (qMat x) (kMat x) i (Fin.last m)
    rw [div_eq_iff hpos.ne'] at h
    rw [ratioFun, ← h]
  have hring : ratioRingElem U i j *
      partialElem U (outFun i l) (fun x _ => analyticAt_outFun i l x) (Coord.v (Fin.last m) l) =
      partialElem U (outFun i l) (fun x _ => analyticAt_outFun i l x) (Coord.v j l) := by
    apply Subtype.ext
    funext x
    change ratioFun i j (x : Coord (m + 1) d → ℝ) *
        fderiv ℝ (outFun i l) x (Pi.single (Coord.v (Fin.last m) l) 1) =
      fderiv ℝ (outFun i l) x (Pi.single (Coord.v j l) 1)
    rw [fderiv_outFun_v, fderiv_outFun_v, hpt]
  have hne : partialElem U (outFun i l) (fun x _ => analyticAt_outFun i l x)
      (Coord.v (Fin.last m) l) ≠ 0 := by
    obtain ⟨x₀, hx₀⟩ := (Fact.out : IsConnected U).nonempty
    intro h
    have := congrFun (congrArg Subtype.val h) ⟨x₀, hx₀⟩
    change fderiv ℝ (outFun i l) x₀ (Pi.single (Coord.v (Fin.last m) l) 1) = 0 at this
    rw [fderiv_outFun_v] at this
    exact (attnWeight_pos _ _ i (Fin.last m)).ne' this
  have hneK : attnJacobian U i l (Coord.v (Fin.last m) l) ≠ 0 := by
    intro h
    apply hne
    apply IsFractionRing.injective (analyticRing U) (AnalyticFunctionField U)
    rw [map_zero]
    exact h
  rw [eq_div_iff hneK, ratioElem, attnJacobian, attnJacobian, ← map_mul, hring]

/-- **Exact attention**, the counting part of `thm:attention` for a derivative trace. Let `U` be a nonempty
connected open set of inputs, `K` the fraction field of analytic functions on `U` and
`F = ℝ(Q, K, V)`. Take any derivative trace over `F` in `K` (`thm:history`) in which, for each
output entry `Y_{il}`, some output word ends with the Jacobian row of `Y_{il}`. If `n ≥ 2`,
`d ≥ 2` and the trace makes at least `nd` transfers, then `I ≥ (nd + n²/M)/32`
(`eq:main-lower`). -/
theorem attention_io_lower_bound (hn : 2 ≤ n) (hd : 2 ≤ d) (U : Set (Coord n d → ℝ))
    [Fact (IsOpen U)] [Fact (IsConnected U)] {W : Type*}
    (T : Trace (FractionRing (MvPolynomial (Coord n d) ℝ)) (AnalyticFunctionField U) W
      (Coord n d))
    (O : Set W) (hO : ∀ i l, ∃ w ∈ O, T.row T.e w = attnJacobian U i l)
    (hI : n * d ≤ T.I) :
    ((n * d : ℝ) + (n : ℝ) ^ 2 / T.M) / 32 ≤ T.I := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hd0 : 0 < d := by omega
  set l₀ : Fin d := ⟨0, hd0⟩
  have hκ : (m + 1) * (m + 1 - 1) ≤ Fintype.card (Fin (m + 1) × Fin m) := by
    simp
  have hjac : ∀ i c, attnJacobian U i l₀ c ∈ T.outputField O := by
    intro i c
    obtain ⟨w, hw, hrow⟩ := hO i l₀
    rw [← hrow]
    exact IntermediateField.subset_adjoin _ _ ⟨w, hw, c, rfl⟩
  refine attention_bound_of_trace T O hn hd hκ
    (fun ij : Fin (m + 1) × Fin m => ratioElem U ij.1 ij.2.castSucc)
    (ratio_algebraicIndependent hd0 U) (fun ij => ?_) hI
  rw [ratio_eq_jacobian_div U ij.1 ij.2.castSucc l₀]
  exact IntermediateField.div_mem _ (hjac _ _) (hjac _ _)

end ExactAttention
