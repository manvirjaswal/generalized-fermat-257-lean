module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

/-! # Additive valuations at the primes of a number field

For a prime `v` of the ring of integers of a number field `K`, `ν v x = -log (v.valuation K x) ∈ ℤ` is the
normalized additive valuation of `x ≠ 0` (the exponent of `v` in `(x)`; junk value `0` at `x = 0`). This file
collects the rules used in Section 4 of the paper in additive form: `ν (x y) = ν x + ν y`, the ultrametric
inequality and its strict form, and `ν x ≥ 0` for algebraic integers, with `ν x > 0` if and only if `x ∈ v`. -/

namespace X2Y5Z7.FiveAdic

open IsDedekindDomain NumberField

noncomputable section

/-- `5` is prime (for `padicValRat 5`). -/
scoped instance fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- The additive valuation `ν_v(x) = -log v(x)`. -/
def ν (x : K) : ℤ := -WithZero.log (v.valuation K x)

variable {v}

theorem val_ne_zero {x : K} (hx : x ≠ 0) : v.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx

theorem val_eq_exp {x : K} (hx : x ≠ 0) : v.valuation K x = WithZero.exp (-ν v x) := by
  rw [ν, neg_neg, WithZero.exp_log (val_ne_zero hx)]

theorem ν_zero : ν v (0 : K) = 0 := by simp [ν]

theorem ν_one : ν v (1 : K) = 0 := by simp [ν]

theorem ν_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : ν v (x * y) = ν v x + ν v y := by
  rw [ν, ν, ν, map_mul, WithZero.log_mul (val_ne_zero hx) (val_ne_zero hy)]
  ring

theorem ν_pow (x : K) (n : ℕ) : ν v (x ^ n) = n * ν v x := by
  rw [ν, ν, map_pow, WithZero.log_pow, nsmul_eq_mul]
  ring

theorem ν_inv (x : K) : ν v x⁻¹ = -ν v x := by
  rw [ν, ν, map_inv₀, WithZero.log_inv]

theorem ν_div {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : ν v (x / y) = ν v x - ν v y := by
  rw [div_eq_mul_inv, ν_mul hx (inv_ne_zero hy), ν_inv]
  ring

theorem ν_neg (x : K) : ν v (-x) = ν v x := by
  rw [ν, ν, Valuation.map_neg]

theorem ν_le_iff {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ν v x ≤ ν v y ↔ v.valuation K y ≤ v.valuation K x := by
  rw [val_eq_exp hx, val_eq_exp hy, WithZero.exp_le_exp]
  omega

theorem ν_lt_iff {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ν v x < ν v y ↔ v.valuation K y < v.valuation K x := by
  rw [val_eq_exp hx, val_eq_exp hy, WithZero.exp_lt_exp]
  omega

theorem ν_nonneg_iff {x : K} (hx : x ≠ 0) : 0 ≤ ν v x ↔ v.valuation K x ≤ 1 := by
  rw [val_eq_exp hx, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem ν_pos_iff {x : K} (hx : x ≠ 0) : 0 < ν v x ↔ v.valuation K x < 1 := by
  rw [val_eq_exp hx, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

/-- Strict ultrametric inequality: if `ν x < ν y` (or `y = 0`) then `ν (x + y) = ν x`. -/
theorem ν_add_eq {x y : K} (hx : x ≠ 0) (h : y = 0 ∨ ν v x < ν v y) : ν v (x + y) = ν v x := by
  by_cases hy : y = 0
  · rw [hy, add_zero]
  rcases h with h | h
  · exact absurd h hy
  rw [ν, ν, Valuation.map_add_eq_of_lt_left _ ((ν_lt_iff hx hy).mp h)]

/-- Ultrametric inequality. -/
theorem ν_add_ge {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (ν v x) (ν v y) ≤ ν v (x + y) := by
  rcases le_total (ν v x) (ν v y) with h | h
  · rw [min_eq_left h, ν_le_iff hx hxy]
    exact (Valuation.map_add _ _ _).trans (max_le le_rfl ((ν_le_iff hx hy).mp h))
  · rw [min_eq_right h, ν_le_iff hy hxy]
    exact (Valuation.map_add _ _ _).trans (max_le ((ν_le_iff hy hx).mp h) le_rfl)

/-- If `x + y = 0` then `ν x = ν y`. -/
theorem ν_eq_of_add_eq_zero {x y : K} (h : x + y = 0) : ν v x = ν v y := by
  rw [add_eq_zero_iff_eq_neg] at h
  rw [h, ν_neg]

/-- A sum `x + y` with `ν x < ν y` (or `y = 0`) is not zero. -/
theorem add_ne_zero_of_lt {x y : K} (hx : x ≠ 0) (h : y = 0 ∨ ν v x < ν v y) : x + y ≠ 0 := by
  rcases h with rfl | h
  · rwa [add_zero]
  intro h0
  have := ν_eq_of_add_eq_zero (v := v) h0
  omega

theorem ν_intCast_nonneg (x : 𝓞 K) : 0 ≤ ν v (x : K) := by
  by_cases hx : (x : K) = 0
  · rw [hx, ν_zero]
  rw [ν_nonneg_iff hx]
  exact v.valuation_le_one x

theorem ν_pos_iff_mem {x : 𝓞 K} (hx : (x : K) ≠ 0) : 0 < ν v (x : K) ↔ x ∈ v.asIdeal := by
  rw [ν_pos_iff hx]
  exact v.valuation_lt_one_iff_mem x

/-- Elements with `ν ≥ 0` form a subring (the valuation ring). -/
theorem ν_nonneg_iff_mem_integer {x : K} (hx : x ≠ 0) :
    0 ≤ ν v x ↔ x ∈ (v.valuation K).integer := by
  rw [ν_nonneg_iff hx]
  rfl

theorem mem_integer_of_ν_nonneg {x : K} (h : x = 0 ∨ 0 ≤ ν v x) : x ∈ (v.valuation K).integer := by
  rcases h with rfl | h
  · exact zero_mem _
  by_cases hx : x = 0
  · rw [hx]; exact zero_mem _
  exact (ν_nonneg_iff_mem_integer hx).mp h

theorem ν_nonneg_of_mem_integer {x : K} (hx : x ≠ 0) (h : x ∈ (v.valuation K).integer) : 0 ≤ ν v x :=
  (ν_nonneg_iff_mem_integer hx).mpr h

/-- Elements of the valuation ring: `ν` of a nonzero element of the valuation ring is `≥ 0`. -/
theorem ν_ge_of_mem {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (h : x / y ∈ (v.valuation K).integer) :
    ν v y ≤ ν v x := by
  have := ν_nonneg_of_mem_integer (div_ne_zero hx hy) h
  rw [ν_div hx hy] at this
  omega

/-! ## Lower bounds

`Ge v c y` says that `y = 0` or `ν y ≥ c`; these bounds add up along sums and products. -/

/-- `y` is zero or has valuation at least `c`. -/
def Ge (v : HeightOneSpectrum (𝓞 K)) (c : ℤ) (y : K) : Prop := y = 0 ∨ c ≤ ν v y

theorem Ge.zero (c : ℤ) : Ge v c (0 : K) := Or.inl rfl

theorem Ge.of_ν {y : K} {c : ℤ} (h : c ≤ ν v y) : Ge v c y := Or.inr h

theorem Ge.self (y : K) : Ge v (ν v y) y := Or.inr le_rfl

theorem Ge.mono {y : K} {c d : ℤ} (h : Ge v c y) (hdc : d ≤ c) : Ge v d y := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (hdc.trans h)

theorem Ge.add {y z : K} {c : ℤ} (hy : Ge v c y) (hz : Ge v c z) : Ge v c (y + z) := by
  rcases hy with rfl | hy
  · rwa [zero_add]
  rcases hz with rfl | hz
  · rw [add_zero]; exact Or.inr hy
  by_cases hy0 : y = 0
  · rw [hy0, zero_add]; exact Or.inr hz
  by_cases hz0 : z = 0
  · rw [hz0, add_zero]; exact Or.inr hy
  by_cases h : y + z = 0
  · exact Or.inl h
  exact Or.inr ((le_min hy hz).trans (ν_add_ge hy0 hz0 h))

theorem Ge.neg {y : K} {c : ℤ} (hy : Ge v c y) : Ge v c (-y) := by
  rcases hy with rfl | hy
  · rw [neg_zero]; exact Or.inl rfl
  · rw [Ge, ν_neg, neg_eq_zero]; exact Or.inr hy

theorem Ge.sub {y z : K} {c : ℤ} (hy : Ge v c y) (hz : Ge v c z) : Ge v c (y - z) := by
  rw [sub_eq_add_neg]; exact hy.add hz.neg

theorem Ge.mul {y z : K} {c d : ℤ} (hy : Ge v c y) (hz : Ge v d z) : Ge v (c + d) (y * z) := by
  rcases hy with rfl | hy
  · rw [zero_mul]; exact Or.inl rfl
  rcases hz with rfl | hz
  · rw [mul_zero]; exact Or.inl rfl
  by_cases hy0 : y = 0
  · rw [hy0, zero_mul]; exact Or.inl rfl
  by_cases hz0 : z = 0
  · rw [hz0, mul_zero]; exact Or.inl rfl
  right
  rw [ν_mul hy0 hz0]
  omega

theorem Ge.pow {y : K} {c : ℤ} (hy : Ge v c y) (n : ℕ) : Ge v (n * c) (y ^ n) := by
  induction n with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul]; exact Or.inr (by rw [ν_one])
  | succ n ih => rw [pow_succ]; convert ih.mul hy using 1; push_cast; ring

theorem Ge.of_mem {y : K} (h : y ∈ (v.valuation K).integer) : Ge v 0 y := by
  by_cases hy : y = 0
  · exact Or.inl hy
  · exact Or.inr (ν_nonneg_of_mem_integer hy h)

theorem Ge.mem {y : K} (h : Ge v 0 y) : y ∈ (v.valuation K).integer := mem_integer_of_ν_nonneg h

/-- If `y` has valuation `> ν x`, then `ν (x + y) = ν x`. -/
theorem ν_add_of_Ge {x y : K} (hx : x ≠ 0) (hy : Ge v (ν v x + 1) y) : ν v (x + y) = ν v x := by
  refine ν_add_eq hx ?_
  rcases hy with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

theorem add_ne_zero_of_Ge {x y : K} (hx : x ≠ 0) (hy : Ge v (ν v x + 1) y) : x + y ≠ 0 := by
  refine add_ne_zero_of_lt (v := v) hx ?_
  rcases hy with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

theorem ν_intCast_nonneg' (m : ℤ) : 0 ≤ ν v (m : K) := by
  have := ν_intCast_nonneg (v := v) (m : 𝓞 K)
  simpa using this

theorem Ge.intCast (m : ℤ) : Ge v 0 (m : K) := Or.inr (ν_intCast_nonneg' m)

/-- `ν(x - c)` for a unit `c`: equal to `ν x` if `ν x < 0`, to `0` if `ν x > 0`, and `≥ 0` if `ν x = 0`. -/
theorem ν_sub_unit {x c : K} (hx : x ≠ 0) (hc : c ≠ 0) (hc0 : ν v c = 0) (hxc : x - c ≠ 0) :
    (ν v x < 0 → ν v (x - c) = ν v x) ∧ (0 < ν v x → ν v (x - c) = 0) ∧ (ν v x = 0 → 0 ≤ ν v (x - c)) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [sub_eq_add_neg, ν_add_of_Ge hx (Ge.of_ν (by rw [ν_neg]; omega))]
  · rw [sub_eq_neg_add, ν_add_of_Ge (neg_ne_zero.mpr hc) (Ge.of_ν (by rw [ν_neg]; omega)), ν_neg, hc0]
  · rcases (Ge.of_ν (v := v) (le_of_eq h.symm)).sub (Ge.of_ν (v := v) (le_of_eq hc0.symm)) with h' | h'
    · exact absurd h' hxc
    · exact h'

end

end X2Y5Z7.FiveAdic
