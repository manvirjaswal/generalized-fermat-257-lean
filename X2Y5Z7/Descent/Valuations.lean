import X2Y5Z7.Descent.Basic
import X2Y5Z7.Selmer.L24SIntegers

/-! # Proposition 3.1: the descent element has valuations divisible by 5 away from 2, 5, 7

Let `θ ∈ L₂₄` be a root of the fibre polynomial `f_η(t) = 4t⁵ψ(t) - η(4t - 1)` and
`E = 80000 (θ - b) ψ(θ)³` (`Edesc`).

* `Edesc_ne_zero`: if `η ≠ 0` then `E ≠ 0` (`ψ(θ) = 0` would force `θ = 1/4`, but
  `64 ψ(1/4) = 1225`).
* `count_Edesc_dvd_five`: if `η = X⁵/Z⁷` comes from a solution, then for every prime `v` of `𝓞 L₂₄` not above
  2, 5 or 7, the exponent of `v` in the fractional ideal `(E)` is divisible by 5.
* `Edesc_mem_selmer`: hence the class of `E` lies in the Selmer group `L₂₄(S, 5)`.

The proof works with the multiplicative valuation `V = v.valuation L24` (values in `ℤᵐ⁰`, so that
`V x ≤ 1` means that `x` is `v`-integral) and shows that `V E` is a fifth power
(`val_Edesc_fifth_power`, which splits into the cases below); `count_eq_neg_log` converts this into the divisibility of the exponent.
The `v`-adic facts about `b` are proved from explicit identities:
`b (25b² + 20b + 14) = -14`, `(1 - 4b)(400b² + 420b + 329) = 1225` and
`ψ'(b) (130b² - 183b - 28) = 8750 = 2·5⁴·7`, where `ψ'(b) = 75b² + 40b + 14`.
With `ψ(θ) = (θ - b) Q`, `Q = 25θ² + (25b + 20)θ + 25b² + 20b + 14`, the cases are:

* `V θ > 1`: `V(θ - b) = V θ` and `V ψ(θ) = (V θ)³`, so `V E = (V θ)¹⁰`;
* `V(4θ - 1) < 1`: `θ - b` and `ψ(θ)` are `v`-units (`64 ψ(θ) = 1225 + (4θ - 1)(…)`), so `V E = 1`;
* otherwise `V(θ)⁵ V ψ(θ) = V η ≤ 1`, which forces `V Z = 1` and `V η = (V X)⁵`; if `V θ < 1`
  then `V E = 1`, and if `V θ = 1` then at most one of `θ - b`, `Q` is not a unit, so
  `V E = (V η)⁴` or `(V η)³`.
-/

namespace X2Y5Z7

open Polynomial IsDedekindDomain
open scoped NumberField nonZeroDivisors WithZero

noncomputable section

namespace Prop31

/-! ## Identities in `L₂₄` -/

theorem aeval_ψ_L24 (t : L24) : aeval t ψ = 25 * t ^ 3 + 20 * t ^ 2 + 14 * t + 14 := by
  simp [ψ, ψZ, aeval_def]

theorem ψ_b : 25 * b ^ 3 + 20 * b ^ 2 + 14 * b + 14 = 0 := by
  rw [← aeval_ψ_L24, b_root]

/-- `f_η(θ) = 0` says `4θ⁵ψ(θ) = η(4θ - 1)`. -/
theorem fibre_eq {η : ℚ} {θ : L24} (hθ : aeval θ (fpoly η) = 0) :
    4 * θ ^ 5 * aeval θ ψ = algebraMap ℚ L24 η * (4 * θ - 1) := by
  rw [aeval_fpoly] at hθ
  rw [aeval_ψ_L24]
  linear_combination hθ

/-- `ψ(θ) ≠ 0`: otherwise `θ = 1/4`, but `64 ψ(1/4) = 1225`. -/
theorem aeval_ψ_ne_zero {η : ℚ} (hη : η ≠ 0) {θ : L24} (hθ : aeval θ (fpoly η) = 0) :
    aeval θ ψ ≠ 0 := by
  intro hP
  have h1 := fibre_eq hθ
  rw [hP, mul_zero, eq_comm, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact hη ((map_eq_zero_iff _ (algebraMap ℚ L24).injective).mp h1)
  · rw [aeval_ψ_L24] at hP
    have h : (1225 : L24) = 0 := by
      linear_combination 64 * hP - (400 * θ ^ 2 + 420 * θ + 329) * h1
    norm_num at h

theorem η_ne_zero (s : Solution) : s.η ≠ 0 :=
  div_ne_zero (pow_ne_zero 5 (Int.cast_ne_zero.mpr s.X_ne))
    (pow_ne_zero 7 (Int.cast_ne_zero.mpr s.Z_ne))

theorem η_mul_Z_pow (s : Solution) :
    algebraMap ℚ L24 s.η * (s.Z : L24) ^ 7 = (s.X : L24) ^ 5 := by
  have hZ : (s.Z : L24) ≠ 0 := Int.cast_ne_zero.mpr s.Z_ne
  rw [Solution.η, map_div₀, map_pow, map_pow, map_intCast, map_intCast,
    div_mul_cancel₀ _ (pow_ne_zero 7 hZ)]

end Prop31

open Prop31 in
/-- The descent element is nonzero. -/
theorem Edesc_ne_zero (η : ℚ) (hη : η ≠ 0) (θ : L24) (hθ : aeval θ (fpoly η) = 0) :
    Edesc θ ≠ 0 := by
  have hP := aeval_ψ_ne_zero hη hθ
  have hD : θ - b ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [h, b_root] at hP
    exact hP rfl
  unfold Edesc
  exact mul_ne_zero (mul_ne_zero (by norm_num) hD) (pow_ne_zero 3 hP)

/-- Membership of an integer polynomial expression in a subring, from membership of the
variables (found among the hypotheses). -/
local macro "int_mem" : tactic => `(tactic| repeat' (first
  | assumption
  | apply add_mem
  | apply sub_mem
  | apply mul_mem
  | apply pow_mem
  | apply neg_mem
  | apply ofNat_mem
  | apply one_mem))

namespace Prop31

/-! ## Valuations at a prime `v` of `𝓞 L₂₄` -/

section Valuation

variable (v : HeightOneSpectrum (𝓞 L24))

/-- The exponent of `v` in `(x)` is minus the logarithm of the `v`-adic valuation of `x`. -/
theorem count_eq_neg_log {x : L24} (hx : x ≠ 0) :
    FractionalIdeal.count L24 v (FractionalIdeal.spanSingleton (𝓞 L24)⁰ x) =
      -WithZero.log (v.valuation L24 x) := by
  have h1 := Selmer.SUnitSequence.valuationOfNeZero_eq_neg_count v (Units.mk0 x hx)
  have h2 := v.valuationOfNeZero_eq (K := L24) (Units.mk0 x hx)
  rw [Units.val_mk0] at h1 h2
  rw [← h2]
  change _ = -Multiplicative.toAdd (v.valuationOfNeZero (Units.mk0 x hx))
  rw [h1, neg_neg]

theorem val_intCast_le_one (n : ℤ) : v.valuation L24 (n : L24) ≤ 1 := by
  rw [← map_intCast (algebraMap (𝓞 L24) L24) n]
  exact v.valuation_le_one n

/-- A product of two `v`-integers which is a `v`-unit has `v`-unit factors. -/
theorem val_eq_one_of_mul_eq {x y z : L24} (h : x * y = z) (hz : v.valuation L24 z = 1)
    (hx : v.valuation L24 x ≤ 1) (hy : v.valuation L24 y ≤ 1) : v.valuation L24 x = 1 := by
  refine le_antisymm hx (not_lt.mp fun hlt => ?_)
  have h' : v.valuation L24 (x * y) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hy) hlt
  rw [h, hz] at h'
  exact lt_irrefl _ h'

/-- If `V η ≤ 1` then `Z` is a `v`-unit (as `X`, `Z` are coprime) and `V η = (V X)⁵`. -/
theorem val_η_of_le_one (s : Solution) (hηle : v.valuation L24 (algebraMap ℚ L24 s.η) ≤ 1) :
    v.valuation L24 (algebraMap ℚ L24 s.η) = v.valuation L24 (s.X : L24) ^ 5 := by
  have hηZ : v.valuation L24 (algebraMap ℚ L24 s.η) * v.valuation L24 (s.Z : L24) ^ 7 =
      v.valuation L24 (s.X : L24) ^ 5 := by
    rw [← map_pow, ← map_mul, η_mul_Z_pow, map_pow]
  have hZ : v.valuation L24 (s.Z : L24) = 1 := by
    refine le_antisymm (val_intCast_le_one v _) (not_lt.mp fun hZlt => ?_)
    have hX : v.valuation L24 (s.X : L24) = 1 := by
      obtain ⟨u, w, huw⟩ := s.coprime
      have h1 : (u : L24) * s.X + (w : L24) * s.Z = 1 := by exact_mod_cast huw
      refine le_antisymm (val_intCast_le_one v _) (not_lt.mp fun hXlt => ?_)
      have h : v.valuation L24 ((u : L24) * s.X + (w : L24) * s.Z) < 1 := by
        apply Valuation.map_add_lt
        · rw [map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one v u)) hXlt
        · rw [map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one v w)) hZlt
      rw [h1, map_one] at h
      exact lt_irrefl _ h
    have h7 : v.valuation L24 (s.Z : L24) ^ 7 < 1 := by
      rw [pow_succ]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (pow_le_one' hZlt.le 6)) hZlt
    have h : v.valuation L24 (algebraMap ℚ L24 s.η) * v.valuation L24 (s.Z : L24) ^ 7 < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left' hηle) h7
    rw [hηZ, hX, one_pow] at h
    exact lt_irrefl _ h
  rw [← hηZ, hZ, one_pow, mul_one]

variable {v} (hv : v ∉ Selmer.L24SIntegers.Sprimes)
include hv

theorem val_two : v.valuation L24 2 = 1 := by
  have h := (v.valuation_eq_one_iff_notMem (K := L24) (r := 2)).mpr fun h => hv (Or.inl h)
  rwa [map_ofNat] at h

theorem val_five : v.valuation L24 5 = 1 := by
  have h := (v.valuation_eq_one_iff_notMem (K := L24) (r := 5)).mpr
    fun h => hv (Or.inr (Or.inl h))
  rwa [map_ofNat] at h

theorem val_seven : v.valuation L24 7 = 1 := by
  have h := (v.valuation_eq_one_iff_notMem (K := L24) (r := 7)).mpr
    fun h => hv (Or.inr (Or.inr h))
  rwa [map_ofNat] at h

/-- Products of powers of 2, 5 and 7 are `v`-units. -/
theorem val_of_eq {x : L24} (i j k : ℕ) (h : x = 2 ^ i * 5 ^ j * 7 ^ k) :
    v.valuation L24 x = 1 := by
  rw [h, map_mul, map_mul, map_pow, map_pow, map_pow, val_two hv, val_five hv, val_seven hv,
    one_pow, one_pow, one_pow, one_mul, one_mul]

/-- If `V t > 1` then the leading term of `ψ(t)` dominates: `V ψ(t) = (V t)³`. -/
theorem val_ψ_of_one_lt {t : L24} (ht : 1 < v.valuation L24 t) :
    v.valuation L24 (aeval t ψ) = v.valuation L24 t ^ 3 := by
  have h25 : v.valuation L24 25 = 1 := val_of_eq hv 0 2 0 (by norm_num)
  have h20 : v.valuation L24 20 = 1 := val_of_eq hv 2 1 0 (by norm_num)
  have h14 : v.valuation L24 14 = 1 := val_of_eq hv 1 0 1 (by norm_num)
  have h1 : 1 ≤ v.valuation L24 t ^ 2 := one_le_pow₀ ht.le
  have h2 : v.valuation L24 t ≤ v.valuation L24 t ^ 2 := le_self_pow₀ ht.le (by norm_num)
  have hlow : v.valuation L24 (20 * t ^ 2 + 14 * t + 14) < v.valuation L24 (25 * t ^ 3) := by
    rw [map_mul, h25, one_mul, map_pow]
    refine lt_of_le_of_lt ?_ (pow_lt_pow_right₀ ht (by norm_num : 2 < 3))
    refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) (h14 ▸ h1)
    · rw [map_mul, map_pow, h20, one_mul]
    · rw [map_mul, h14, one_mul]
      exact h2
  rw [show aeval t ψ = 25 * t ^ 3 + (20 * t ^ 2 + 14 * t + 14) by rw [aeval_ψ_L24]; ring,
    Valuation.map_add_eq_of_lt_left _ hlow, map_mul, h25, one_mul, map_pow]

theorem val_b_le_one : v.valuation L24 b ≤ 1 := by
  by_contra h
  have h3 := val_ψ_of_one_lt hv (not_le.mp h)
  rw [b_root, map_zero] at h3
  exact pow_ne_zero 3 (ne_of_gt (lt_trans zero_lt_one (not_le.mp h))) h3.symm

/-- `b` is a `v`-unit: `b (25b² + 20b + 14) = -14`. -/
theorem val_b : v.valuation L24 b = 1 := by
  have hb : b ∈ (v.valuation L24).integer := val_b_le_one hv
  refine val_eq_one_of_mul_eq v (y := 25 * b ^ 2 + 20 * b + 14) (z := -14) ?_ ?_
    (val_b_le_one hv) ?_
  · linear_combination ψ_b
  · rw [Valuation.map_neg]
    exact val_of_eq hv 1 0 1 (by norm_num)
  · exact (by int_mem : 25 * b ^ 2 + 20 * b + 14 ∈ (v.valuation L24).integer)

/-- `1 - 4b` is a `v`-unit: `(1 - 4b)(400b² + 420b + 329) = 1225`. -/
theorem val_one_sub_four_b : v.valuation L24 (1 - 4 * b) = 1 := by
  have hb : b ∈ (v.valuation L24).integer := val_b_le_one hv
  refine val_eq_one_of_mul_eq v (y := 400 * b ^ 2 + 420 * b + 329) (z := 1225) ?_
    (val_of_eq hv 0 2 2 (by norm_num)) ?_ ?_
  · linear_combination (-64) * ψ_b
  · exact (by int_mem : 1 - 4 * b ∈ (v.valuation L24).integer)
  · exact (by int_mem : 400 * b ^ 2 + 420 * b + 329 ∈ (v.valuation L24).integer)

/-- `ψ'(b) = 75b² + 40b + 14` is a `v`-unit: `ψ'(b) (130b² - 183b - 28) = 8750`. -/
theorem val_dψ_b : v.valuation L24 (75 * b ^ 2 + 40 * b + 14) = 1 := by
  have hb : b ∈ (v.valuation L24).integer := val_b_le_one hv
  refine val_eq_one_of_mul_eq v (y := 130 * b ^ 2 - 183 * b - 28) (z := 8750) ?_
    (val_of_eq hv 1 4 1 (by norm_num)) ?_ ?_
  · linear_combination (390 * b - 653) * ψ_b
  · exact (by int_mem : 75 * b ^ 2 + 40 * b + 14 ∈ (v.valuation L24).integer)
  · exact (by int_mem : 130 * b ^ 2 - 183 * b - 28 ∈ (v.valuation L24).integer)

/-- `V E = V(θ - b) · V(ψ(θ))³`, since `80000 = 2⁷5⁴` is a `v`-unit. -/
theorem val_Edesc (θ : L24) :
    v.valuation L24 (Edesc θ) = v.valuation L24 (θ - b) * v.valuation L24 (aeval θ ψ) ^ 3 := by
  rw [Edesc, map_mul, map_mul, map_pow, val_of_eq hv 7 4 0 (by norm_num), one_mul]

/-- Case `V θ > 1`: `V E = (V θ)¹⁰`. -/
theorem val_Edesc_of_one_lt {θ : L24} (hθ1 : 1 < v.valuation L24 θ) :
    v.valuation L24 (Edesc θ) = (v.valuation L24 θ ^ 2) ^ 5 := by
  rw [val_Edesc hv, val_ψ_of_one_lt hv hθ1,
    Valuation.map_sub_eq_of_lt_left _ ((val_b hv) ▸ hθ1), ← pow_mul, ← pow_succ', ← pow_mul]

/-- Case `V θ ≤ 1`, `V(4θ - 1) < 1`: `θ - b` and `ψ(θ)` are `v`-units, so `V E = 1`. -/
theorem val_Edesc_of_eps_lt {θ : L24} (hθ1 : v.valuation L24 θ ≤ 1)
    (hε : v.valuation L24 (4 * θ - 1) < 1) : v.valuation L24 (Edesc θ) = 1 := by
  have hθO : θ ∈ (v.valuation L24).integer := hθ1
  have h4 : v.valuation L24 4 = 1 := val_of_eq hv 2 0 0 (by norm_num)
  have hD : v.valuation L24 (θ - b) = 1 := by
    have h : v.valuation L24 (4 * (θ - b)) = 1 := by
      rw [show 4 * (θ - b) = (4 * θ - 1) + (1 - 4 * b) by ring,
        Valuation.map_add_eq_of_lt_right _ (by rw [val_one_sub_four_b hv]; exact hε),
        val_one_sub_four_b hv]
    rwa [map_mul, h4, one_mul] at h
  have hP : v.valuation L24 (aeval θ ψ) = 1 := by
    have h1225 : v.valuation L24 1225 = 1 := val_of_eq hv 0 2 2 (by norm_num)
    have hR : v.valuation L24 (459 + 155 * (4 * θ - 1) + 25 * (4 * θ - 1) ^ 2) ≤ 1 :=
      (by int_mem : 459 + 155 * (4 * θ - 1) + 25 * (4 * θ - 1) ^ 2 ∈ (v.valuation L24).integer)
    have h : v.valuation L24 (64 * aeval θ ψ) = 1 := by
      rw [show 64 * aeval θ ψ = 1225 + (4 * θ - 1) *
          (459 + 155 * (4 * θ - 1) + 25 * (4 * θ - 1) ^ 2) by rw [aeval_ψ_L24]; ring,
        Valuation.map_add_eq_of_lt_left, h1225]
      rw [h1225, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hR) hε
    rwa [map_mul, val_of_eq hv 6 0 0 (by norm_num), one_mul] at h
  rw [val_Edesc hv, hD, hP, one_pow, one_mul]

/-- Case `V θ < 1`: `θ - b` and `ψ(θ)` are `v`-units, so `V E = 1`. -/
theorem val_Edesc_of_lt_one {θ : L24} (hθlt : v.valuation L24 θ < 1) :
    v.valuation L24 (Edesc θ) = 1 := by
  have hθO : θ ∈ (v.valuation L24).integer := hθlt.le
  have hb1 := val_b hv
  have hD : v.valuation L24 (θ - b) = 1 := by
    rw [Valuation.map_sub_eq_of_lt_right _ (hb1 ▸ hθlt), hb1]
  have hP : v.valuation L24 (aeval θ ψ) = 1 := by
    have h14 : v.valuation L24 14 = 1 := val_of_eq hv 1 0 1 (by norm_num)
    have hR : v.valuation L24 (14 + 20 * θ + 25 * θ ^ 2) ≤ 1 :=
      (by int_mem : 14 + 20 * θ + 25 * θ ^ 2 ∈ (v.valuation L24).integer)
    rw [show aeval θ ψ = 14 + θ * (14 + 20 * θ + 25 * θ ^ 2) by rw [aeval_ψ_L24]; ring,
      Valuation.map_add_eq_of_lt_left, h14]
    rw [h14, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hR) hθlt
  rw [val_Edesc hv, hD, hP, one_pow, one_mul]

/-- Case `V θ = 1`, `V(θ - b) < 1`: `Q = ψ(θ)/(θ - b)` is a `v`-unit, so `V(θ - b) = V ψ(θ)`. -/
theorem val_sub_b_eq_val_ψ {θ : L24} (hθ1 : v.valuation L24 θ ≤ 1)
    (hDlt : v.valuation L24 (θ - b) < 1) :
    v.valuation L24 (θ - b) = v.valuation L24 (aeval θ ψ) := by
  have hθO : θ ∈ (v.valuation L24).integer := hθ1
  have hb : b ∈ (v.valuation L24).integer := val_b_le_one hv
  have hQ : v.valuation L24
      (25 * θ ^ 2 + (25 * b + 20) * θ + (25 * b ^ 2 + 20 * b + 14)) = 1 := by
    have hR : v.valuation L24 (25 * θ + 50 * b + 20) ≤ 1 :=
      (by int_mem : 25 * θ + 50 * b + 20 ∈ (v.valuation L24).integer)
    rw [show 25 * θ ^ 2 + (25 * b + 20) * θ + (25 * b ^ 2 + 20 * b + 14) =
        (75 * b ^ 2 + 40 * b + 14) + (θ - b) * (25 * θ + 50 * b + 20) by ring,
      Valuation.map_add_eq_of_lt_left, val_dψ_b hv]
    rw [val_dψ_b hv, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hR) hDlt
  rw [show aeval θ ψ = (θ - b) * (25 * θ ^ 2 + (25 * b + 20) * θ +
      (25 * b ^ 2 + 20 * b + 14)) by rw [aeval_ψ_L24]; linear_combination ψ_b,
    map_mul, hQ, mul_one]

/-- Case `V θ ≤ 1`, `V ψ(θ) = w⁵` when `V θ = 1`: `V E` is a fifth power. -/
theorem val_Edesc_of_le_one {θ : L24} (hθ1 : v.valuation L24 θ ≤ 1) (w : ℤᵐ⁰)
    (hfib : v.valuation L24 θ ^ 5 * v.valuation L24 (aeval θ ψ) = w ^ 5) :
    ∃ c : ℤᵐ⁰, v.valuation L24 (Edesc θ) = c ^ 5 := by
  rcases lt_or_eq_of_le hθ1 with hθlt | hθeq
  · exact ⟨1, by rw [val_Edesc_of_lt_one hv hθlt, one_pow]⟩
  have hPw : v.valuation L24 (aeval θ ψ) = w ^ 5 := by
    rw [← hfib, hθeq, one_pow, one_mul]
  have hθO : θ ∈ (v.valuation L24).integer := hθ1
  have hb : b ∈ (v.valuation L24).integer := val_b_le_one hv
  have hDO : θ - b ∈ (v.valuation L24).integer := by int_mem
  rcases lt_or_eq_of_le (show v.valuation L24 (θ - b) ≤ 1 from hDO) with hDlt | hDeq
  · refine ⟨w ^ 4, ?_⟩
    rw [val_Edesc hv, val_sub_b_eq_val_ψ hv hθ1 hDlt, ← pow_succ', hPw, ← pow_mul, ← pow_mul]
  · refine ⟨w ^ 3, ?_⟩
    rw [val_Edesc hv, hDeq, one_mul, hPw, ← pow_mul, ← pow_mul]

/-- The `v`-adic valuation of the descent element is a fifth power. -/
theorem val_Edesc_fifth_power (s : Solution) {θ : L24} (hθ : aeval θ (fpoly s.η) = 0) :
    ∃ c : ℤᵐ⁰, v.valuation L24 (Edesc θ) = c ^ 5 := by
  rcases lt_or_ge 1 (v.valuation L24 θ) with hθ1 | hθ1
  · exact ⟨_, val_Edesc_of_one_lt hv hθ1⟩
  rcases lt_or_ge (v.valuation L24 (4 * θ - 1)) 1 with hε | hε
  · exact ⟨1, by rw [val_Edesc_of_eps_lt hv hθ1 hε, one_pow]⟩
  have hθO : θ ∈ (v.valuation L24).integer := hθ1
  have hε1 : v.valuation L24 (4 * θ - 1) = 1 :=
    le_antisymm (by int_mem : 4 * θ - 1 ∈ (v.valuation L24).integer) hε
  have hPO : aeval θ ψ ∈ (v.valuation L24).integer := by
    rw [aeval_ψ_L24]
    int_mem
  have hfib : v.valuation L24 θ ^ 5 * v.valuation L24 (aeval θ ψ) =
      v.valuation L24 (algebraMap ℚ L24 s.η) := by
    have h := congrArg (v.valuation L24) (fibre_eq hθ)
    rwa [map_mul, map_mul, map_mul, map_pow, val_of_eq hv 2 0 0 (by norm_num), one_mul, hε1,
      mul_one] at h
  have hηle : v.valuation L24 (algebraMap ℚ L24 s.η) ≤ 1 :=
    hfib ▸ mul_le_one' (pow_le_one' hθ1 5) hPO
  exact val_Edesc_of_le_one hv hθ1 _ (hfib.trans (val_η_of_le_one v s hηle))


end Valuation

end Prop31

open Prop31 in
/-- **Proposition 3.1.** For a solution `s`, a root `θ ∈ L₂₄` of `f_η` and a prime `v` of `𝓞 L₂₄`
not above 2, 5 or 7, the exponent of `v` in `(E)`, `E = 80000 (θ - b) ψ(θ)³`, is divisible by 5. -/
theorem count_Edesc_dvd_five (s : Solution) (θ : L24) (hθ : aeval θ (fpoly s.η) = 0)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L24)) (hv : v ∉ Selmer.L24SIntegers.Sprimes) :
    (5 : ℤ) ∣ FractionalIdeal.count L24 v
      (FractionalIdeal.spanSingleton (𝓞 L24)⁰ (Edesc θ)) := by
  obtain ⟨c, hc⟩ := val_Edesc_fifth_power hv s hθ
  rw [count_eq_neg_log v (Edesc_ne_zero s.η (η_ne_zero s) θ hθ), hc, WithZero.log_pow, dvd_neg,
    nsmul_eq_mul]
  exact dvd_mul_right _ _

/-- The class of the descent element lies in the Selmer group `L₂₄(S, 5)`. -/
theorem Edesc_mem_selmer (s : Solution) (θ : L24) (hθ : aeval θ (fpoly s.η) = 0) :
    QuotientGroup.mk (Units.mk0 (Edesc θ) (Edesc_ne_zero s.η (Prop31.η_ne_zero s) θ hθ)) ∈
      @IsDedekindDomain.selmerGroup (𝓞 L24) _ _ L24 _ _ _ Selmer.L24SIntegers.Sprimes 5 :=
  (Selmer.L24SIntegers.mem_selmer_iff_outside_counts _).mpr fun v hv => count_Edesc_dvd_five s θ hθ v hv

end

end X2Y5Z7
