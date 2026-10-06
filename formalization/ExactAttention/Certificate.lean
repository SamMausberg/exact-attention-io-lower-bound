import ExactAttention.Defs

/-!
# What field containment cannot certify

This file covers `cor:subintermediate` and `thm:certificate`.

`Certificate.sigma_lt_three` records `σ = log₂ 7 < 3`. `subintermediate` takes the parameter
sequence `d = 2^k`, `n = d³`, `M = d²`, with `B = n / d` blocks and `R = 7^k` bilinear products,
and checks the arithmetic of `cor:subintermediate`: `R = d^σ`, both terms of `eq:aux-io` equal
`d^{σ+2}`, the prefix work is at most `2 n² d`, and the transfer term is `o(n d + n² d / M)`.
The transfer count of the prefix and the fact that its history contains the target field are
part of `thm:bilinear-prefix`. They are not proved in Lean.

`no_certificate_charge` is the counting argument of `thm:certificate` for the prefixes along
that sequence. Facts about a
prefix enter as hypotheses: a transfer bound `I ≤ K d^{σ+2}`, the epoch count `e ≤ I / M + 1` of
`eq:epochs`, and containment of the target field `𝒯` in the history after the last epoch.
Histories are not modelled. Containment of `𝒯` is an arbitrary predicate on the epochs of each
prefix, and a charge is any real number attached to each epoch history of each prefix. The
correct attention program that follows each prefix in the paper is not modelled.
-/

namespace ExactAttention

namespace Certificate

open Filter Topology Asymptotics

/-- The exponent `σ = log₂ 7` of the seven-product decomposition. -/
noncomputable def sigma : ℝ := Real.logb 2 7

/-- `σ = log₂ 7 < 3`. -/
theorem sigma_lt_three : sigma < 3 := by
  rw [sigma, Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num),
    show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- `(2^k)^σ = 7^k`. -/
lemma two_pow_rpow_sigma (k : ℕ) : ((2 : ℝ) ^ k) ^ sigma = 7 ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
    sigma, Real.rpow_logb (by norm_num) (by norm_num) (by norm_num), Real.rpow_natCast]

/-- `(2^k)^(σ+2) = 7^k (2^k)²`. -/
lemma two_pow_rpow_sigma_add_two (k : ℕ) :
    ((2 : ℝ) ^ k) ^ (sigma + 2) = 7 ^ k * ((2 : ℝ) ^ k) ^ 2 := by
  rw [Real.rpow_add (by positivity), two_pow_rpow_sigma, Real.rpow_two]

private lemma eight_pow (k : ℕ) : (8 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 3 := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

end Certificate

open Filter Topology Asymptotics Certificate

/-- `cor:subintermediate`, the arithmetic of the parameter sequence. Let `d = 2^k`, `n = d³`,
`M = d²`, let `B = n / d` be the number of blocks and `R = 7^k` the number of bilinear products.
Then `R = d^σ`; both terms `B R` and `B² R / M` of `eq:aux-io` equal `d^{σ+2}`; the work
`B R + B² R` of the prefix is at most `2 n² d`; and `B R + B² R / M = o(n d + n² d / M)`. -/
theorem subintermediate (d n M B R : ℕ → ℝ) (hd : ∀ k, d k = 2 ^ k) (hn : ∀ k, n k = d k ^ 3)
    (hM : ∀ k, M k = d k ^ 2) (hB : ∀ k, B k = n k / d k) (hR : ∀ k, R k = 7 ^ k) :
    (∀ k, R k = d k ^ sigma ∧ B k * R k = d k ^ (sigma + 2) ∧
      B k ^ 2 * R k / M k = d k ^ (sigma + 2) ∧
      B k * R k + B k ^ 2 * R k ≤ 2 * n k ^ 2 * d k) ∧
    (fun k => B k * R k + B k ^ 2 * R k / M k) =o[atTop]
      (fun k => n k * d k + n k ^ 2 * d k / M k) := by
  have hBk : ∀ k, B k = ((2 : ℝ) ^ k) ^ 2 := fun k => by
    rw [hB, hn, hd]
    field_simp
  refine ⟨fun k => ?_, ?_⟩
  · have hx : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hy : (7 : ℝ) ^ k ≤ ((2 : ℝ) ^ k) ^ 3 := by
      rw [← eight_pow]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) k
    refine ⟨by rw [hR, hd, two_pow_rpow_sigma], ?_, ?_, ?_⟩
    · rw [hBk, hR, hd, two_pow_rpow_sigma_add_two, mul_comm]
    · rw [hBk, hR, hM, hd, two_pow_rpow_sigma_add_two]
      field_simp
    · rw [hBk, hR, hn, hd]
      have hy0 : (0 : ℝ) ≤ 7 ^ k := by positivity
      nlinarith [pow_le_pow_right₀ hx (show 5 ≤ 7 by norm_num),
        pow_le_pow_right₀ hx (show 2 ≤ 4 by norm_num), mul_le_mul_of_nonneg_left hy
          (show (0 : ℝ) ≤ ((2 : ℝ) ^ k) ^ 2 by positivity),
        mul_le_mul_of_nonneg_left hy (show (0 : ℝ) ≤ ((2 : ℝ) ^ k) ^ 4 by positivity)]
  · have hf : (fun k => B k * R k + B k ^ 2 * R k / M k) =
        fun k => 2 * (((2 : ℝ) ^ k) ^ 2 * 7 ^ k) := by
      funext k
      rw [hBk, hR, hM, hd]
      field_simp
      ring
    have hg : (fun k => n k * d k + n k ^ 2 * d k / M k) =
        fun k => ((2 : ℝ) ^ k) ^ 4 + ((2 : ℝ) ^ k) ^ 5 := by
      funext k
      rw [hn, hM, hd]
      field_simp
    rw [hf, hg]
    refine isLittleO_iff_tendsto' (Eventually.of_forall fun k hk => ?_) |>.2 ?_
    · exfalso
      have : (0 : ℝ) < ((2 : ℝ) ^ k) ^ 4 + ((2 : ℝ) ^ k) ^ 5 := by positivity
      exact this.ne' hk
    · have hlim : Tendsto (fun k : ℕ => 2 * ((7 : ℝ) / 8) ^ k) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 7 / 8)
          (by norm_num)).const_mul 2
      refine squeeze_zero (fun k => by positivity) (fun k => ?_) hlim
      have hx : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      have hx0 : (0 : ℝ) < 2 ^ k := by positivity
      rw [div_le_iff₀ (by positivity), div_pow, eight_pow]
      field_simp
      nlinarith [pow_pos hx0 3, pow_pos (show (0 : ℝ) < 7 by norm_num) k]

/-- The counting argument of `thm:certificate`. Take `d = 2^k` for `k ≥ 3`, `n = d³` and
`M = d²`, and for each such `k` a prefix with `I k` transfers, split into `e k` epochs of at most
`M` transfers. Assume, as `thm:bilinear-prefix` and `cor:subintermediate` provide, that
`I k ≤ K d^{σ+2}`, that `e k ≤ I k / M + 1` (`eq:epochs`), and that the history after the last
epoch contains the target field. Containment of the target field is an arbitrary predicate
`ContainsT k t` on the history after `t` epochs. Then there are no constants `c, C > 0` and
charges `charge k t` on these histories with initial value `0`, increase at most
`C (M + M² / d)` across each epoch, and value at least `c n (n - 1)` at every history that
contains the target field. -/
theorem no_certificate_charge (d n M : ℕ → ℝ) (hd : ∀ k, d k = 2 ^ k)
    (hn : ∀ k, n k = d k ^ 3) (hM : ∀ k, M k = d k ^ 2) (K : ℝ) (I e : ℕ → ℕ)
    (ContainsT : ℕ → ℕ → Prop) (hI : ∀ k ≥ 3, (I k : ℝ) ≤ K * d k ^ (sigma + 2))
    (he : ∀ k ≥ 3, (e k : ℝ) ≤ I k / M k + 1) (hT : ∀ k ≥ 3, ContainsT k (e k)) :
    ¬ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ charge : ℕ → ℕ → ℝ, ∀ k ≥ 3,
      charge k 0 = 0 ∧
      (∀ t < e k, charge k (t + 1) - charge k t ≤ C * (M k + M k ^ 2 / d k)) ∧
      (∀ t ≤ e k, ContainsT k t → c * (n k * (n k - 1)) ≤ charge k t) := by
  rintro ⟨c, C, hc, hC, charge, hch⟩
  set A : ℝ := 4 * C * (|K| + 1) / c
  have key : ∀ k ≥ 3, (8 : ℝ) ^ k ≤ A * 7 ^ k := by
    intro k hk
    obtain ⟨h0, hinc, hcont⟩ := hch k hk
    have hsum : ∀ t ≤ e k, charge k t ≤ t * (C * (M k + M k ^ 2 / d k)) := by
      intro t
      induction t with
      | zero => intro _; simp [h0]
      | succ t ih =>
        intro ht
        have h1 := hinc t (by omega)
        have h2 := ih (by omega)
        push_cast
        linarith
    have hlow := hcont (e k) le_rfl (hT k hk)
    have hup := hsum (e k) le_rfl
    set x : ℝ := 2 ^ k with hxdef
    have hx8 : (8 : ℝ) ≤ x := by
      rw [hxdef]
      calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
    have hx0 : 0 < x := by linarith
    have hy1 : (1 : ℝ) ≤ 7 ^ k := one_le_pow₀ (by norm_num)
    have hek : (e k : ℝ) ≤ K * 7 ^ k + 1 := by
      have h1 := he k hk
      have h2 := hI k hk
      rw [hd, two_pow_rpow_sigma_add_two] at h2
      rw [hM, hd] at h1
      have : (I k : ℝ) / x ^ 2 ≤ K * 7 ^ k := by
        rw [div_le_iff₀ (by positivity)]
        linarith
      linarith
    have hek' : (e k : ℝ) ≤ (|K| + 1) * 7 ^ k := by
      nlinarith [le_abs_self K]
    rw [hn, hd] at hlow
    rw [hM, hd] at hup
    have hcap : C * ((x ^ 2) + (x ^ 2) ^ 2 / x) = C * x ^ 2 * (1 + x) := by
      field_simp
    rw [hcap] at hup
    have hmain : c * (x ^ 3 * (x ^ 3 - 1)) ≤ (|K| + 1) * 7 ^ k * (C * x ^ 2 * (1 + x)) := by
      have hcap0 : 0 ≤ C * x ^ 2 * (1 + x) := by positivity
      calc c * (x ^ 3 * (x ^ 3 - 1)) ≤ charge k (e k) := hlow
        _ ≤ (e k : ℝ) * (C * x ^ 2 * (1 + x)) := hup
        _ ≤ (|K| + 1) * 7 ^ k * (C * x ^ 2 * (1 + x)) :=
          mul_le_mul_of_nonneg_right hek' hcap0
    have hx3 : c * x ^ 3 ≤ 4 * C * (|K| + 1) * 7 ^ k := by
      have hK0 : 0 ≤ (|K| + 1) * 7 ^ k := by positivity
      have h1 : x ^ 3 - 1 ≥ x ^ 3 / 2 := by nlinarith
      have h2 : 1 + x ≤ 2 * x := by linarith
      have h3 : c * (x ^ 3 * (x ^ 3 / 2)) ≤ (|K| + 1) * 7 ^ k * (C * x ^ 2 * (2 * x)) := by
        calc c * (x ^ 3 * (x ^ 3 / 2)) ≤ c * (x ^ 3 * (x ^ 3 - 1)) := by gcongr
          _ ≤ _ := hmain
          _ ≤ _ := by gcongr
      have h4 : x ^ 3 * (c * x ^ 3) ≤ x ^ 3 * (4 * C * (|K| + 1) * 7 ^ k) := by nlinarith
      exact le_of_mul_le_mul_left h4 (by positivity)
    rw [eight_pow, ← hxdef]
    rw [show A * 7 ^ k = 4 * C * (|K| + 1) * 7 ^ k / c by simp only [A]; ring]
    rw [le_div_iff₀ hc]
    linarith
  obtain ⟨N, hN⟩ := (tendsto_atTop.1 (tendsto_pow_atTop_atTop_of_one_lt
    (by norm_num : (1 : ℝ) < 8 / 7)) (A + 1)).exists_forall_of_atTop
  have hk := key (max N 3) (le_max_right _ _)
  have hk' := hN (max N 3) (le_max_left _ _)
  rw [div_pow, le_div_iff₀ (by positivity)] at hk'
  nlinarith [pow_pos (show (0 : ℝ) < 7 by norm_num) (max N 3)]

end ExactAttention
