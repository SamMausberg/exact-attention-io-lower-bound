import ExactAttention.Defs

/-!
# The field of analytic functions on an open execution set

This is the paragraph after `lem:open` in `sec:model`. For a set `U` in a real normed space,
`analyticRing U` is the ring of real functions on `U` that extend to a function analytic at every
point of `U`. Functions are compared only on `U`, so two analytic functions that agree on `U`
give the same element. For a nonempty connected open `U` this ring is an integral domain
(`isDomain_analyticRing`), and `AnalyticFunctionField U` is its fraction field, the ambient field
of `sec:history`. The domain property uses the identity theorem and holds in any real normed
space; finite dimension is needed only for the polynomials below.

For `U ⊆ σ → ℝ` with `σ` finite, evaluation of real polynomials gives an injective algebra map
into `analyticRing U` (`polyToAnalytic_injective`), because no nonzero polynomial vanishes on a
nonempty open set. It extends to an embedding of the rational function field `ℝ(x)`
(`ratFuncToAnalytic_injective`).
-/

namespace ExactAttention

open MvPolynomial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Real functions on `U` that extend to functions analytic at every point of `U`. Functions are
identified when they agree on `U`. -/
def analyticRing (U : Set E) : Subalgebra ℝ (U → ℝ) where
  carrier := {g | ∃ f : E → ℝ, AnalyticOnNhd ℝ f U ∧ g = fun x : U => f x}
  mul_mem' := by
    rintro _ _ ⟨f₁, hf₁, rfl⟩ ⟨f₂, hf₂, rfl⟩
    exact ⟨f₁ * f₂, hf₁.mul hf₂, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f₁, hf₁, rfl⟩ ⟨f₂, hf₂, rfl⟩
    exact ⟨f₁ + f₂, hf₁.add hf₂, rfl⟩
  algebraMap_mem' r := ⟨fun _ => r, analyticOnNhd_const, rfl⟩

namespace AnalyticField

theorem mem_analyticRing {U : Set E} {g : U → ℝ} :
    g ∈ analyticRing U ↔ ∃ f : E → ℝ, AnalyticOnNhd ℝ f U ∧ g = fun x : U => f x :=
  Iff.rfl

theorem restrict_mem {U : Set E} {f : E → ℝ} (hf : AnalyticOnNhd ℝ f U) :
    (fun x : U => f x) ∈ analyticRing U :=
  ⟨f, hf, rfl⟩

end AnalyticField

open AnalyticField

/-- **Analytic functions form an integral domain** (paragraph after `lem:open`). On a nonempty
connected open set, the ring of analytic functions, with functions identified when they agree on
the set, has no zero divisors. -/
theorem isDomain_analyticRing {U : Set E} (hU : IsOpen U) (hconn : IsConnected U) :
    IsDomain (analyticRing U) := by
  have : Nonempty U := hconn.nonempty.to_subtype
  refine (isDomain_iff_noZeroDivisors_and_nontrivial _).mpr ⟨⟨?_⟩, inferInstance⟩
  rintro ⟨_, f₁, hf₁, rfl⟩ ⟨_, f₂, hf₂, rfl⟩ h
  have h' : ∀ x ∈ U, f₁ x * f₂ x = 0 := fun x hx =>
    congrFun (congrArg Subtype.val h) ⟨x, hx⟩
  by_cases hz : ∀ x ∈ U, f₁ x = 0
  · left
    ext x
    exact hz x x.2
  · right
    push Not at hz
    obtain ⟨x₀, hx₀U, hx₀⟩ := hz
    have hev : f₂ =ᶠ[nhds x₀] 0 := by
      filter_upwards [hU.mem_nhds hx₀U,
        (hf₁ x₀ hx₀U).continuousAt.eventually_ne hx₀] with y hyU hy
      exact (mul_eq_zero.mp (h' y hyU)).resolve_left hy
    have := hf₂.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn.isPreconnected hx₀U hev
    ext x
    exact this x.2

instance {U : Set E} [Fact (IsOpen U)] [Fact (IsConnected U)] : IsDomain (analyticRing U) :=
  isDomain_analyticRing (Fact.out) (Fact.out)

/-- The ambient field of `sec:history`: the fraction field of the analytic functions on `U`. -/
abbrev AnalyticFunctionField (U : Set E) := FractionRing (analyticRing U)

section Polynomial

variable {σ : Type*} [Fintype σ]

namespace AnalyticField

/-- The coordinate function `x ↦ x i` as an element of the analytic ring. -/
def coord (U : Set (σ → ℝ)) (i : σ) : analyticRing U :=
  ⟨fun x : U => (x : σ → ℝ) i,
    restrict_mem (f := fun x : σ → ℝ => x i) fun x _ =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ => ℝ) i).analyticAt x⟩

end AnalyticField

/-- Evaluation of real polynomials, as functions on `U`. -/
noncomputable def polyToAnalytic (U : Set (σ → ℝ)) : MvPolynomial σ ℝ →ₐ[ℝ] analyticRing U :=
  aeval (AnalyticField.coord U)

theorem polyToAnalytic_apply (U : Set (σ → ℝ)) (p : MvPolynomial σ ℝ) (x : U) :
    (polyToAnalytic U p : U → ℝ) x = eval (x : σ → ℝ) p := by
  have h := congrArg (fun φ : MvPolynomial σ ℝ →ₐ[ℝ] ℝ => φ p)
    (comp_aeval (R := ℝ) (AnalyticField.coord U)
      ((Pi.evalAlgHom ℝ (fun _ : U => ℝ) x).comp (analyticRing U).val))
  simpa [polyToAnalytic, AnalyticField.coord, coe_aeval_eq_eval] using h

/-- **Polynomials embed in the analytic ring** (paragraph after `lem:open`). On a nonempty open
set, distinct real polynomials define distinct analytic functions. -/
theorem polyToAnalytic_injective {U : Set (σ → ℝ)} (hU : IsOpen U) (hne : U.Nonempty) :
    Function.Injective (polyToAnalytic U) := by
  refine (injective_iff_map_eq_zero _).mpr fun p hp => ?_
  refine mvPolynomial_eq_zero_of_isOpen hU hne fun x hx => ?_
  rw [← polyToAnalytic_apply U p ⟨x, hx⟩, hp]
  rfl

variable (U : Set (σ → ℝ)) [Fact (IsOpen U)] [Fact (IsConnected U)]

namespace AnalyticField

/-- Polynomials as elements of the field of analytic functions on `U`. -/
noncomputable def polyToField : MvPolynomial σ ℝ →ₐ[ℝ] AnalyticFunctionField U :=
  (IsScalarTower.toAlgHom ℝ (analyticRing U) (AnalyticFunctionField U)).comp (polyToAnalytic U)

theorem polyToField_injective : Function.Injective (polyToField U) :=
  (IsFractionRing.injective (analyticRing U) (AnalyticFunctionField U)).comp
    (polyToAnalytic_injective Fact.out (Fact.out : IsConnected U).nonempty)

end AnalyticField

/-- The rational function field `ℝ(x)` mapped into the field of analytic functions on `U`. -/
noncomputable def ratFuncToAnalytic :
    FractionRing (MvPolynomial σ ℝ) →ₐ[ℝ] AnalyticFunctionField U :=
  IsFractionRing.liftAlgHom (AnalyticField.polyToField_injective U)

/-- **The rational function field embeds** (paragraph after `lem:open`). For a nonempty
connected open `U`, the map from `ℝ(x)` to the fraction field of the analytic functions on `U` is
injective. -/
theorem ratFuncToAnalytic_injective : Function.Injective (ratFuncToAnalytic U) :=
  (ratFuncToAnalytic U).toRingHom.injective

theorem ratFuncToAnalytic_algebraMap (p : MvPolynomial σ ℝ) :
    ratFuncToAnalytic U (algebraMap _ _ p) = algebraMap _ _ (polyToAnalytic U p) := by
  rw [ratFuncToAnalytic, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

end Polynomial

end ExactAttention
