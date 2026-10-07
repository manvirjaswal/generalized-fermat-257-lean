import X2Y5Z7.FiveAdic.Valuation
import X2Y5Z7.Descent.Valuations

/-! # Section 4.2: the local analysis at one prime of `L₂₄` above 5

Let `v` be a prime of `𝓞 L₂₄` with `ν(5) = e > 0` and `ν(m) = 0` for the integers `m` prime to 5, and let `θ ∈ L₂₄`
be a root of `f_η`, so that `4θ⁵ψ(θ) = η(4θ - 1)` (`fibre_eq`); put `N = ν(η)`. The ultrametric inequality applied to
this equation, to `ψ(b) = 0` and to the expansion of `f_η(1/4 + s)` gives the local statements that replace the
Newton polygons and Hensel's lemma of the paper:

* `ν_θ_of_lt`, `ν_θ_of_eq`, `ν_θ_of_mid`, `ν_θ_of_pos`: `t = ν(θ)` satisfies `7t = N - 2e` if `t < -e`, `N ≥ -5e` if `t = -e`, and `5t = N` if
  `-e < t < 0` or `t > 0` (the slopes of the Newton polygon of `f_η`, Steps 1–3);
* `ν_b_cases`: `ν(b) ∈ {0, -e}`; at a prime with `ν(b) = 0`, `ν(1 - 4b) = 2e` and `b ≡ -1` (`ν_one_sub_four_b`,
  `b1_add_one`); at a prime with `ν(b) = -e`, `5b ≡ -2` and `ν(75b + 20) = e` (Lemma 2.6);
* Steps 4 and 5: `step4_pos`, `step4_ne`, `step5`, from `f_η(1/4 + s) = c₀ + c₁s + c₂s² + …` with
  `c₀ = 1225/16384`, `c₁ = (823 - 2048η)/512`;
* Step 6: the valuations of `θ - b` and `ψ(θ)` in each case. -/

namespace X2Y5Z7.FiveAdic

open Polynomial IsDedekindDomain NumberField Prop31

noncomputable section

/-- Membership of an integer polynomial expression in the valuation ring, from membership of the variables. -/
local macro "int_mem" : tactic => `(tactic| repeat' (first
  | assumption
  | apply add_mem
  | apply sub_mem
  | apply mul_mem
  | apply pow_mem
  | apply neg_mem
  | apply ofNat_mem
  | apply one_mem))

variable {v : HeightOneSpectrum (𝓞 L24)} {e : ℤ}

section Constants

variable (he : ν v (5 : L24) = e) (hZ : ∀ m : ℤ, ¬ (5 : ℤ) ∣ m → ν v (m : L24) = 0)
include he hZ

/-- `ν(5ᵏ m / d) = k e` for integers `m, d` prime to 5. -/
theorem ν_const {x : L24} (k : ℕ) (m d : ℤ) (hm : ¬ (5 : ℤ) ∣ m) (hd : ¬ (5 : ℤ) ∣ d)
    (hx : x = 5 ^ k * m / d) : ν v x = k * e := by
  have hm0 : (m : L24) ≠ 0 := Int.cast_ne_zero.mpr (by rintro rfl; exact hm (dvd_zero _))
  have hd0 : (d : L24) ≠ 0 := Int.cast_ne_zero.mpr (by rintro rfl; exact hd (dvd_zero _))
  rw [hx, ν_div (mul_ne_zero (pow_ne_zero _ (by norm_num)) hm0) hd0,
    ν_mul (pow_ne_zero _ (by norm_num)) hm0, ν_pow, he, hZ m hm, hZ d hd]
  ring

theorem ν_unit_const {x : L24} (m d : ℤ) (hm : ¬ (5 : ℤ) ∣ m) (hd : ¬ (5 : ℤ) ∣ d) (hx : x = m / d) :
    ν v x = 0 := by
  rw [ν_const he hZ 0 m d hm hd (by rw [hx, pow_zero, one_mul])]
  ring

end Constants

/-! ## The equation `ψ(b) = 0` (Lemma 2.6) -/

section B

theorem b_ne_zero : b ≠ 0 := by
  intro h
  have := ψ_b
  rw [h] at this
  norm_num at this

/-- `ν(b) ∈ {0, -e}`. -/
theorem ν_b_cases (he : ν v (5 : L24) = e) (he0 : 0 < e)
    (hZ : ∀ m : ℤ, ¬ (5 : ℤ) ∣ m → ν v (m : L24) = 0) :
    ν v b = 0 ∨ ν v b = -e := by
  have hb := b_ne_zero
  set t := ν v b with ht
  have h25 : ν v (25 : L24) = 2 * e := by
    rw [ν_const he hZ 2 1 1 (by decide) (by decide) (by norm_num)]; push_cast; ring
  have h20 : ν v (20 : L24) = e := by
    rw [ν_const he hZ 1 4 1 (by decide) (by decide) (by norm_num)]; push_cast; ring
  have h14 : ν v (14 : L24) = 0 := ν_unit_const he hZ 14 1 (by decide) (by decide) (by norm_num)
  have hrel : 25 * b ^ 3 + (20 * b ^ 2 + 14 * b + 14) = 0 := by linear_combination ψ_b
  have hrel' : 14 * b + (25 * b ^ 3 + 20 * b ^ 2 + 14) = 0 := by linear_combination ψ_b
  have hrel'' : (14 : L24) + (25 * b ^ 3 + 20 * b ^ 2 + 14 * b) = 0 := by linear_combination ψ_b
  have h3 : ν v (25 * b ^ 3) = 2 * e + 3 * t := by
    rw [ν_mul (by norm_num) (pow_ne_zero _ hb), h25, ν_pow]; push_cast; ring
  have h2 : ν v (20 * b ^ 2) = e + 2 * t := by
    rw [ν_mul (by norm_num) (pow_ne_zero _ hb), h20, ν_pow]; push_cast; ring
  have h1 : ν v (14 * b) = t := by rw [ν_mul (by norm_num) hb, h14]; ring
  rcases lt_trichotomy t (-e) with hlt | heq | hgt
  · exfalso
    refine add_ne_zero_of_Ge (v := v) (mul_ne_zero (by norm_num) (pow_ne_zero _ hb)) ?_ hrel
    rw [h3]
    exact ((Ge.of_ν (by omega : _ ≤ ν v (20 * b ^ 2))).add (Ge.of_ν (by omega : _ ≤ ν v (14 * b)))).add
      (Ge.of_ν (by omega : _ ≤ ν v (14 : L24)))
  · exact Or.inr heq
  rcases lt_trichotomy t 0 with hlt0 | heq0 | hgt0
  · exfalso
    refine add_ne_zero_of_Ge (v := v) (mul_ne_zero (by norm_num) hb) ?_ hrel'
    rw [h1]
    exact ((Ge.of_ν (by omega : _ ≤ ν v (25 * b ^ 3))).add (Ge.of_ν (by omega : _ ≤ ν v (20 * b ^ 2)))).add
      (Ge.of_ν (by omega : _ ≤ ν v (14 : L24)))
  · exact Or.inl heq0
  · exfalso
    refine add_ne_zero_of_Ge (v := v) (by norm_num) ?_ hrel''
    rw [h14]
    exact ((Ge.of_ν (by omega : _ ≤ ν v (25 * b ^ 3))).add (Ge.of_ν (by omega : _ ≤ ν v (20 * b ^ 2)))).add
      (Ge.of_ν (by omega : _ ≤ ν v (14 * b)))

theorem ν25 (he : ν v (5 : L24) = e) (hZ : ∀ m : ℤ, ¬ (5 : ℤ) ∣ m → ν v (m : L24) = 0) :
    ν v (25 : L24) = 2 * e := by
  rw [ν_const he hZ 2 1 1 (by decide) (by decide) (by norm_num)]; push_cast; ring

/-- At a prime with `ν(b) = 0`: `b ≡ -1` (`14 (b + 1) = -(25b³ + 20b²)`). -/
theorem b1_add_one (he : ν v (5 : L24) = e) (he0 : 0 < e) (hZ : ∀ m : ℤ, ¬ (5 : ℤ) ∣ m → ν v (m : L24) = 0) (hb0 : ν v b = 0) : Ge v e (b + 1) := by
  have hb := b_ne_zero
  by_cases h1 : b + 1 = 0
  · exact Or.inl h1
  have h14 : ν v (14 : L24) = 0 := ν_unit_const he hZ 14 1 (by decide) (by decide) (by norm_num)
  have hrel : 14 * (b + 1) = -(25 * b ^ 3 + 20 * b ^ 2) := by linear_combination ψ_b
  have hR : Ge v e (-(25 * b ^ 3 + 20 * b ^ 2)) := by
    refine Ge.neg (Ge.add ?_ ?_)
    · refine Ge.of_ν ?_
      rw [ν_mul (by norm_num) (pow_ne_zero _ hb), ν25 he hZ, ν_pow, hb0]; omega
    · refine Ge.of_ν ?_
      rw [ν_mul (by norm_num) (pow_ne_zero _ hb), ν_pow, hb0,
        ν_const he hZ 1 4 1 (by decide) (by decide) (by norm_num)]; push_cast; omega
  rw [← hrel] at hR
  rcases hR with h | h
  · exact absurd h (mul_ne_zero (by norm_num) h1)
  · rw [ν_mul (by norm_num) h1, h14, zero_add] at h
    exact Or.inr h

/-- **Lemma 2.6** (`v₅(4b₁ - 1) = 2`): at a prime with `ν(b) = 0`, `ν(1 - 4b) = 2e`, from
`(1 - 4b)(400b² + 420b + 329) = 1225` and `400b² + 420b + 329 = 309 + 20(20b + 1)(b + 1)`. -/
theorem ν_one_sub_four_b (he : ν v (5 : L24) = e) (he0 : 0 < e)
    (hZ : ∀ m : ℤ, ¬ (5 : ℤ) ∣ m → ν v (m : L24) = 0)
    (hb0 : ν v b = 0) : ν v (1 - 4 * b) = 2 * e := by
  have hb := b_ne_zero
  have hbO : b ∈ (v.valuation L24).integer := (Ge.of_ν (le_of_eq hb0.symm)).mem
  have hU : ν v (309 + 20 * (20 * b + 1) * (b + 1)) = 0 := by
    have h309 : ν v (309 : L24) = 0 := ν_unit_const he hZ 309 1 (by decide) (by decide) (by norm_num)
    rw [ν_add_of_Ge (by norm_num) ?_, h309]
    rw [h309, zero_add]
    have h20 : Ge v e (20 : L24) := Ge.of_ν (by
      rw [ν_const he hZ 1 4 1 (by decide) (by decide) (by norm_num)]; push_cast; omega)
    have := (h20.mul (Ge.of_mem (by int_mem : 20 * b + 1 ∈ (v.valuation L24).integer))).mul
      (b1_add_one he he0 hZ hb0)
    exact this.mono (by omega)
  have hrel : (1 - 4 * b) * (309 + 20 * (20 * b + 1) * (b + 1)) = 1225 := by
    linear_combination (-64) * ψ_b
  have hne : (309 + 20 * (20 * b + 1) * (b + 1) : L24) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hrel; norm_num at hrel
  have hne' : (1 - 4 * b : L24) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hrel; norm_num at hrel
  have := congrArg (ν v) hrel
  rw [ν_mul hne' hne, hU, ν_const (x := (1225 : L24)) he hZ 2 49 1 (by decide) (by decide) (by norm_num)] at this
  push_cast at this
  omega

/-- At a prime with `ν(b) = -e`: `β = 5b` satisfies `β (β + 2)² = -10 (β + 7)`, so `5b ≡ -2`. -/
theorem b2_five_b_add_two (he : ν v (5 : L24) = e) (he0 : 0 < e) (hb1 : ν v b = -e) : Ge v 1 (5 * b + 2) := by
  have hb := b_ne_zero
  by_cases h2 : 5 * b + 2 = 0
  · exact Or.inl h2
  have hβ : ν v (5 * b) = 0 := by rw [ν_mul (by norm_num) hb, he, hb1]; ring
  have hβO : 5 * b ∈ (v.valuation L24).integer := (Ge.of_ν (le_of_eq hβ.symm)).mem
  have hrel : (5 * b) * (5 * b + 2) ^ 2 = 5 * (-2 * (5 * b + 7)) := by linear_combination 5 * ψ_b
  have hR : Ge v e (5 * (-2 * (5 * b + 7))) := by
    have := (Ge.of_ν (le_of_eq he.symm)).mul (Ge.of_mem (v := v)
      (by int_mem : -2 * (5 * b + 7) ∈ (v.valuation L24).integer))
    simpa using this
  rw [← hrel] at hR
  rcases hR with h | h
  · exact absurd h (mul_ne_zero (mul_ne_zero (by norm_num) hb) (pow_ne_zero _ h2))
  · rw [ν_mul (mul_ne_zero (by norm_num) hb) (pow_ne_zero _ h2), hβ, ν_pow] at h
    exact Or.inr (by push_cast at h; omega)

/-- At a prime with `ν(b) = -e`: `ν(75b + 20) = e` (`75b + 20 = 5 (3(5b + 2) - 2)`). -/
theorem ν_75b_20 (he : ν v (5 : L24) = e) (he0 : 0 < e)
    (hZ : ∀ m : ℤ, ¬ (5 : ℤ) ∣ m → ν v (m : L24) = 0) (hb1 : ν v b = -e) : ν v (75 * b + 20) = e := by
  have hne : (-2 + 3 * (5 * b + 2) : L24) ≠ 0 := by
    refine add_ne_zero_of_Ge (v := v) (by norm_num) ?_
    rw [ν_unit_const he hZ (-2) 1 (by decide) (by decide) (by norm_num), zero_add]
    have := (Ge.intCast (v := v) 3).mul (b2_five_b_add_two he he0 hb1)
    simpa using this
  have hu : ν v (-2 + 3 * (5 * b + 2) : L24) = 0 := by
    rw [ν_add_of_Ge (by norm_num), ν_unit_const he hZ (-2) 1 (by decide) (by decide) (by norm_num)]
    rw [ν_unit_const he hZ (-2) 1 (by decide) (by decide) (by norm_num), zero_add]
    have := (Ge.intCast (v := v) 3).mul (b2_five_b_add_two he he0 hb1)
    simpa using this
  rw [show (75 * b + 20 : L24) = 5 * (-2 + 3 * (5 * b + 2)) by ring, ν_mul (by norm_num) hne, hu, he]
  ring

end B

/-! ## The valuation of `θ` (Steps 1–3) -/

section Theta

variable {η : ℚ} {θ : L24}

theorem θ_ne_zero (hη : η ≠ 0) (hθ : aeval θ (fpoly η) = 0) : θ ≠ 0 := by
  rintro rfl
  rw [aeval_fpoly] at hθ
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
    sub_zero, zero_add] at hθ
  exact hη ((map_eq_zero_iff _ (algebraMap ℚ L24).injective).mp hθ)

theorem four_θ_sub_one_ne (hη : η ≠ 0) (hθ : aeval θ (fpoly η) = 0) : 4 * θ - 1 ≠ 0 := by
  intro h
  have h1 := fibre_eq hθ
  rw [h, mul_zero] at h1
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (θ_ne_zero hη hθ)))
    (aeval_ψ_ne_zero hη hθ) h1

theorem η_ne_zero' (hη : η ≠ 0) : algebraMap ℚ L24 η ≠ 0 :=
  (map_ne_zero_iff _ (algebraMap ℚ L24).injective).mpr hη

/-- `5 ν(θ) + ν(ψ(θ)) = ν(η) + ν(4θ - 1)`. -/
theorem ν_fibre (he : ν v (5 : L24) = e) (hZ : ∀ m : ℤ, ¬ (5 : ℤ) ∣ m → ν v (m : L24) = 0) (hη : η ≠ 0)
    (hθ : aeval θ (fpoly η) = 0) :
    5 * ν v θ + ν v (aeval θ ψ) = ν v (algebraMap ℚ L24 η) + ν v (4 * θ - 1) := by
  have h := congrArg (ν v) (fibre_eq hθ)
  have hθ0 := θ_ne_zero hη hθ
  rw [ν_mul (mul_ne_zero (by norm_num) (pow_ne_zero _ hθ0)) (aeval_ψ_ne_zero hη hθ),
    ν_mul (by norm_num) (pow_ne_zero _ hθ0), ν_mul (η_ne_zero' hη) (four_θ_sub_one_ne hη hθ), ν_pow,
    ν_unit_const he hZ 4 1 (by decide) (by decide) (by norm_num)] at h
  push_cast at h
  omega

theorem ν_four_θ_sub_one_of_neg (he : ν v (5 : L24) = e) (hZ : ∀ m : ℤ, ¬ (5 : ℤ) ∣ m → ν v (m : L24) = 0)
    (hθ0 : θ ≠ 0) (ht : ν v θ < 0) : ν v (4 * θ - 1) = ν v θ := by
  have h4 : ν v (4 * θ) = ν v θ := by
    rw [ν_mul (by norm_num) hθ0, ν_unit_const he hZ 4 1 (by decide) (by decide) (by norm_num), zero_add]
  rw [sub_eq_add_neg, ν_add_of_Ge (mul_ne_zero (by norm_num) hθ0), h4]
  rw [h4]
  exact Ge.of_ν (by rw [ν_neg, ν_one]; omega)

theorem ν_four_θ_sub_one_of_pos (he : ν v (5 : L24) = e) (hZ : ∀ m : ℤ, ¬ (5 : ℤ) ∣ m → ν v (m : L24) = 0)
    (hθ0 : θ ≠ 0) (ht : 0 < ν v θ) : ν v (4 * θ - 1) = 0 := by
  rw [show 4 * θ - 1 = -1 + 4 * θ by ring, ν_add_of_Ge (by norm_num), ν_neg, ν_one]
  rw [ν_neg, ν_one]
  exact Ge.of_ν (by
    rw [ν_mul (by norm_num) hθ0, ν_unit_const he hZ 4 1 (by decide) (by decide) (by norm_num)]; omega)

section Psi

variable (he : ν v (5 : L24) = e) (hZ : ∀ m : ℤ, ¬ (5 : ℤ) ∣ m → ν v (m : L24) = 0) (hθ0 : θ ≠ 0)
include he hZ hθ0

theorem ν_ψ_terms : ν v (25 * θ ^ 3) = 2 * e + 3 * ν v θ ∧ ν v (20 * θ ^ 2) = e + 2 * ν v θ ∧
    ν v (14 * θ) = ν v θ ∧ ν v (14 : L24) = 0 := by
  have h14 : ν v (14 : L24) = 0 := ν_unit_const he hZ 14 1 (by decide) (by decide) (by norm_num)
  refine ⟨?_, ?_, ?_, h14⟩
  · rw [ν_mul (by norm_num) (pow_ne_zero _ hθ0), ν25 he hZ, ν_pow]; push_cast; ring
  · rw [ν_mul (by norm_num) (pow_ne_zero _ hθ0), ν_pow,
      ν_const he hZ 1 4 1 (by decide) (by decide) (by norm_num)]; push_cast; ring
  · rw [ν_mul (by norm_num) hθ0, h14, zero_add]

theorem ν_ψ_of_lt (he0 : 0 < e) (ht : ν v θ < -e) : ν v (aeval θ ψ) = 2 * e + 3 * ν v θ := by
  obtain ⟨h3, h2, h1, h0⟩ := ν_ψ_terms he hZ hθ0
  rw [aeval_ψ_L24, show 25 * θ ^ 3 + 20 * θ ^ 2 + 14 * θ + 14 = 25 * θ ^ 3 + (20 * θ ^ 2 + 14 * θ + 14) by ring,
    ν_add_of_Ge (mul_ne_zero (by norm_num) (pow_ne_zero _ hθ0)), h3]
  rw [h3]
  exact ((Ge.of_ν (by omega : _ ≤ ν v (20 * θ ^ 2))).add (Ge.of_ν (by omega : _ ≤ ν v (14 * θ)))).add
    (Ge.of_ν (by omega : _ ≤ ν v (14 : L24)))

theorem ν_ψ_ge_of_eq (he0 : 0 < e) (ht : ν v θ = -e) : Ge v (-e) (aeval θ ψ) := by
  obtain ⟨h3, h2, h1, h0⟩ := ν_ψ_terms he hZ hθ0
  rw [aeval_ψ_L24]
  exact (((Ge.of_ν (by omega : _ ≤ ν v (25 * θ ^ 3))).add (Ge.of_ν (by omega : _ ≤ ν v (20 * θ ^ 2)))).add
    (Ge.of_ν (by omega : _ ≤ ν v (14 * θ)))).add (Ge.of_ν (by omega : _ ≤ ν v (14 : L24)))

theorem ν_ψ_of_mid (ht1 : -e < ν v θ) (ht2 : ν v θ < 0) : ν v (aeval θ ψ) = ν v θ := by
  obtain ⟨h3, h2, h1, h0⟩ := ν_ψ_terms he hZ hθ0
  rw [aeval_ψ_L24, show 25 * θ ^ 3 + 20 * θ ^ 2 + 14 * θ + 14 = 14 * θ + (25 * θ ^ 3 + 20 * θ ^ 2 + 14) by ring,
    ν_add_of_Ge (mul_ne_zero (by norm_num) hθ0), h1]
  rw [h1]
  exact ((Ge.of_ν (by omega : _ ≤ ν v (25 * θ ^ 3))).add (Ge.of_ν (by omega : _ ≤ ν v (20 * θ ^ 2)))).add
    (Ge.of_ν (by omega : _ ≤ ν v (14 : L24)))

theorem ν_ψ_of_pos (he0 : 0 < e) (ht : 0 < ν v θ) : ν v (aeval θ ψ) = 0 := by
  obtain ⟨h3, h2, h1, h0⟩ := ν_ψ_terms he hZ hθ0
  rw [aeval_ψ_L24, show 25 * θ ^ 3 + 20 * θ ^ 2 + 14 * θ + 14 = 14 + (25 * θ ^ 3 + 20 * θ ^ 2 + 14 * θ) by ring,
    ν_add_of_Ge (by norm_num), h0]
  rw [h0]
  exact ((Ge.of_ν (by omega : _ ≤ ν v (25 * θ ^ 3))).add (Ge.of_ν (by omega : _ ≤ ν v (20 * θ ^ 2)))).add
    (Ge.of_ν (by omega : _ ≤ ν v (14 * θ)))

end Psi

theorem ψ_Ge_of_nonneg (ht : 0 ≤ ν v θ) : Ge v 0 (aeval θ ψ) := by
  have hθO : θ ∈ (v.valuation L24).integer := (Ge.of_ν ht).mem
  rw [aeval_ψ_L24]
  exact Ge.of_mem (by int_mem)

variable (he : ν v (5 : L24) = e) (he0 : 0 < e) (hZ : ∀ m : ℤ, ¬ (5 : ℤ) ∣ m → ν v (m : L24) = 0)
  (hη : η ≠ 0) (hθ : aeval θ (fpoly η) = 0)
include he he0 hZ hη hθ

/-- The slopes (Steps 1–3): `t = ν(θ) < -e` forces `7t = ν(η) - 2e`. -/
theorem ν_θ_of_lt (ht : ν v θ < -e) : 7 * ν v θ = ν v (algebraMap ℚ L24 η) - 2 * e := by
  have hθ0 := θ_ne_zero hη hθ
  have h1 := ν_fibre he hZ hη hθ
  rw [ν_ψ_of_lt he hZ hθ0 he0 ht, ν_four_θ_sub_one_of_neg he hZ hθ0 (by omega)] at h1
  omega

theorem ν_θ_of_eq (ht : ν v θ = -e) : -5 * e ≤ ν v (algebraMap ℚ L24 η) := by
  have hθ0 := θ_ne_zero hη hθ
  have h1 := ν_fibre he hZ hη hθ
  rw [ν_four_θ_sub_one_of_neg he hZ hθ0 (by omega)] at h1
  rcases ν_ψ_ge_of_eq he hZ hθ0 he0 ht with h | h
  · exact absurd h (aeval_ψ_ne_zero hη hθ)
  · omega

omit he0 in
theorem ν_θ_of_mid (ht1 : -e < ν v θ) (ht2 : ν v θ < 0) : 5 * ν v θ = ν v (algebraMap ℚ L24 η) := by
  have hθ0 := θ_ne_zero hη hθ
  have h1 := ν_fibre he hZ hη hθ
  rw [ν_ψ_of_mid he hZ hθ0 ht1 ht2, ν_four_θ_sub_one_of_neg he hZ hθ0 ht2] at h1
  omega

theorem ν_θ_of_pos (ht : 0 < ν v θ) : 5 * ν v θ = ν v (algebraMap ℚ L24 η) := by
  have hθ0 := θ_ne_zero hη hθ
  have h1 := ν_fibre he hZ hη hθ
  rw [ν_ψ_of_pos he hZ hθ0 he0 ht, ν_four_θ_sub_one_of_pos he hZ hθ0 ht] at h1
  omega

/-- Steps 2–3: if `ν(η) ≥ 0` then `ν(θ) ∈ {-e, 0}` or `ν(θ) > 0` with `5 ν(θ) = ν(η)`. -/
theorem ν_θ_cases_nonneg (hN : 0 ≤ ν v (algebraMap ℚ L24 η)) :
    ν v θ = -e ∨ ν v θ = 0 ∨ (0 < ν v θ ∧ 5 * ν v θ = ν v (algebraMap ℚ L24 η)) := by
  rcases lt_trichotomy (ν v θ) (-e) with h | h | h
  · have := ν_θ_of_lt he he0 hZ hη hθ h; omega
  · exact Or.inl h
  rcases lt_trichotomy (ν v θ) 0 with h' | h' | h'
  · have := ν_θ_of_mid he hZ hη hθ h h'; omega
  · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr ⟨h', ν_θ_of_pos he he0 hZ hη hθ h'⟩)

/-- At a prime with `ν(θ) = -e`: `ν(ψ(θ)) = ν(η) + 4e`. -/
theorem ν_ψ_of_neg_e (ht : ν v θ = -e) : ν v (aeval θ ψ) = ν v (algebraMap ℚ L24 η) + 4 * e := by
  have hθ0 := θ_ne_zero hη hθ
  have h1 := ν_fibre he hZ hη hθ
  rw [ν_four_θ_sub_one_of_neg he hZ hθ0 (by omega)] at h1
  omega

/-- Step 1 (local part): if `ν(η) ≤ -7e` and `7 ∤ ν(η) - 2e`, then `θ` is a unit and
`ν(4θ - 1) = 2e - ν(η)`. -/
theorem step1_local (hN : ν v (algebraMap ℚ L24 η) ≤ -7 * e)
    (h7 : ¬ (7 : ℤ) ∣ ν v (algebraMap ℚ L24 η) - 2 * e) : ν v (4 * θ - 1) = 2 * e - ν v (algebraMap ℚ L24 η) := by
  have hθ0 := θ_ne_zero hη hθ
  have ht : ν v θ = 0 := by
    rcases lt_trichotomy (ν v θ) (-e) with h | h | h
    · exact absurd ⟨ν v θ, by have := ν_θ_of_lt he he0 hZ hη hθ h; omega⟩ h7
    · have := ν_θ_of_eq he he0 hZ hη hθ h; omega
    rcases lt_trichotomy (ν v θ) 0 with h' | h' | h'
    · have := ν_θ_of_mid he hZ hη hθ h h'; omega
    · exact h'
    · have := ν_θ_of_pos he he0 hZ hη hθ h'; omega
  have h1 := ν_fibre he hZ hη hθ
  have hθO : θ ∈ (v.valuation L24).integer := (Ge.of_ν (le_of_eq ht.symm)).mem
  have hψ0 := ν_nonneg_of_mem_integer (aeval_ψ_ne_zero hη hθ) (ψ_Ge_of_nonneg (le_of_eq ht.symm)).mem
  -- `64 ψ(θ) = 1225 + (4θ - 1)(459 + 155(4θ - 1) + 25(4θ - 1)²)` and `ν(4θ - 1) ≥ 7e > 2e`
  have hψ : ν v (aeval θ ψ) = 2 * e := by
    have h1225 : ν v (1225 : L24) = 2 * e := by
      rw [ν_const he hZ 2 49 1 (by decide) (by decide) (by norm_num)]; push_cast; ring
    have hR : Ge v (2 * e + 1) ((4 * θ - 1) * (459 + 155 * (4 * θ - 1) + 25 * (4 * θ - 1) ^ 2)) := by
      have := (Ge.of_ν (le_refl (ν v (4 * θ - 1)))).mul (Ge.of_mem (v := v)
        (by int_mem : 459 + 155 * (4 * θ - 1) + 25 * (4 * θ - 1) ^ 2 ∈ (v.valuation L24).integer))
      exact this.mono (by omega)
    have h64 : 64 * aeval θ ψ = 1225 + (4 * θ - 1) * (459 + 155 * (4 * θ - 1) + 25 * (4 * θ - 1) ^ 2) := by
      rw [aeval_ψ_L24]; ring
    have := congrArg (ν v) h64
    rw [ν_add_of_Ge (by norm_num) (by rw [h1225]; exact hR), h1225,
      ν_mul (by norm_num) (aeval_ψ_ne_zero hη hθ), ν_unit_const he hZ 64 1 (by decide) (by decide) (by norm_num),
      zero_add] at this
    exact this
  omega

end Theta

/-! ## Steps 4 and 5: the unit roots near `1/4`

`f_η(1/4 + s) = c₀ + c₁ s + c₂ s² + s³ R₃(s)` with `c₀ = 1225/16384`, `c₁ = (823 - 2048η)/512 = -1225/512 - 4(η - 1)`,
`c₂ = 3675/256` and `R₃` with coefficients `2205/32, 6195/32, 665/2, 371, 280, 100`. -/

section Steps45

variable {η : ℚ} {θ : L24}

/-- The expansion of `f_η` at `1/4`. -/
theorem fpoly_quarter (hθ : aeval θ (fpoly η) = 0) :
    (1225 / 16384 : L24) + ((-1225 - 2048 * (algebraMap ℚ L24 η - 1)) / 512) * (θ - 1 / 4) +
      (3675 / 256) * (θ - 1 / 4) ^ 2 + (θ - 1 / 4) ^ 3 * ((2205 + 6195 * (θ - 1 / 4) +
      10640 * (θ - 1 / 4) ^ 2 + 11872 * (θ - 1 / 4) ^ 3 + 8960 * (θ - 1 / 4) ^ 4 + 3200 * (θ - 1 / 4) ^ 5) / 32) = 0 := by
  rw [aeval_fpoly] at hθ
  linear_combination hθ

/-- `f_η = (t + 1)⁶ + 5 G(t) + (η - 1)(1 - 4t)`, with `G = 20t⁸ + 16t⁷ + 11t⁶ + 10t⁵ - 3t⁴ - 4t³ - 3t² - 2t`. -/
theorem fpoly_minus_one (hθ : aeval θ (fpoly η) = 0) :
    (θ + 1) ^ 6 = -(5 * (20 * θ ^ 8 + 16 * θ ^ 7 + 11 * θ ^ 6 + 10 * θ ^ 5 - 3 * θ ^ 4 - 4 * θ ^ 3 -
      3 * θ ^ 2 - 2 * θ) + (algebraMap ℚ L24 η - 1) * (1 - 4 * θ)) := by
  rw [aeval_fpoly] at hθ
  linear_combination hθ

variable (he : ν v (5 : L24) = e) (he0 : 0 < e) (hZ : ∀ m : ℤ, ¬ (5 : ℤ) ∣ m → ν v (m : L24) = 0)
  (ht : 0 ≤ ν v θ)
include he hZ ht

omit he0 in
/-- `R₃(θ - 1/4)` is `v`-integral. -/
theorem R3_integral :
    Ge v 0 ((2205 + 6195 * (θ - 1 / 4) + 10640 * (θ - 1 / 4) ^ 2 + 11872 * (θ - 1 / 4) ^ 3 +
      8960 * (θ - 1 / 4) ^ 4 + 3200 * (θ - 1 / 4) ^ 5) / 32 : L24) := by
  have hθO : θ ∈ (v.valuation L24).integer := (Ge.of_ν ht).mem
  have hq : (1 / 4 : L24) ∈ (v.valuation L24).integer :=
    (Ge.of_ν (le_of_eq (ν_unit_const he hZ 1 4 (by decide) (by decide) (by norm_num)).symm)).mem
  have hsO : θ - 1 / 4 ∈ (v.valuation L24).integer := sub_mem hθO hq
  have h32 : (1 / 32 : L24) ∈ (v.valuation L24).integer :=
    (Ge.of_ν (le_of_eq (ν_unit_const he hZ 1 32 (by decide) (by decide) (by norm_num)).symm)).mem
  refine Ge.of_mem ?_
  rw [div_eq_mul_one_div]
  int_mem

omit he0 ht in
theorem c2_Ge : Ge v (2 * e) (3675 / 256 : L24) :=
  Ge.of_ν (le_of_eq (by rw [ν_const he hZ 2 147 256 (by decide) (by decide) (by norm_num)]; push_cast; ring))

omit he0 ht in
theorem c0_ν : ν v (1225 / 16384 : L24) = 2 * e := by
  rw [ν_const he hZ 2 49 16384 (by decide) (by decide) (by norm_num)]; push_cast; ring

omit ht in
/-- `c₁ = (-1225 - 2048(η - 1))/512` is a unit when `η ≢ 1`. -/
theorem c1_ν (he0 : 0 < e) (hη1 : algebraMap ℚ L24 η - 1 ≠ 0) (hη1' : ν v (algebraMap ℚ L24 η - 1) = 0) :
    (-1225 - 2048 * (algebraMap ℚ L24 η - 1)) / 512 ≠ 0 ∧
      ν v ((-1225 - 2048 * (algebraMap ℚ L24 η - 1)) / 512 : L24) = 0 := by
  have hA : ν v (-2048 * (algebraMap ℚ L24 η - 1) : L24) = 0 := by
    rw [ν_mul (by norm_num) hη1, hη1', ν_unit_const he hZ (-2048) 1 (by decide) (by decide) (by norm_num)]
    ring
  have hB : Ge v (ν v (-2048 * (algebraMap ℚ L24 η - 1) : L24) + 1) (-1225 : L24) :=
    Ge.of_ν (by rw [hA, ν_const he hZ 2 (-49) 1 (by decide) (by decide) (by norm_num)]; push_cast; omega)
  have hne : (-2048 * (algebraMap ℚ L24 η - 1) : L24) ≠ 0 := mul_ne_zero (by norm_num) hη1
  have e1 : (-1225 - 2048 * (algebraMap ℚ L24 η - 1) : L24) = -2048 * (algebraMap ℚ L24 η - 1) + -1225 := by ring
  have hN : (-1225 - 2048 * (algebraMap ℚ L24 η - 1) : L24) ≠ 0 := by rw [e1]; exact add_ne_zero_of_Ge hne hB
  refine ⟨div_ne_zero hN (by norm_num), ?_⟩
  rw [ν_div hN (by norm_num), e1, ν_add_of_Ge hne hB, hA, ν_unit_const he hZ 512 1 (by decide) (by decide) (by norm_num)]
  ring

include he0

/-- **Step 5** (local part): if `η ≢ 1`, a unit root `θ ≡ 1/4` has `ν(θ - 1/4) = 2e`. -/
theorem step5 (hθ : aeval θ (fpoly η) = 0) (hη1 : algebraMap ℚ L24 η - 1 ≠ 0)
    (hη1' : ν v (algebraMap ℚ L24 η - 1) = 0) (hs0 : θ - 1 / 4 ≠ 0) (hs : 0 < ν v (θ - 1 / 4)) :
    ν v (θ - 1 / 4) = 2 * e := by
  have hF := fpoly_quarter hθ
  set σ := θ - 1 / 4 with hσ
  set c1 := ((-1225 - 2048 * (algebraMap ℚ L24 η - 1)) / 512 : L24) with hc1
  set R3 := ((2205 + 6195 * σ + 10640 * σ ^ 2 + 11872 * σ ^ 3 + 8960 * σ ^ 4 + 3200 * σ ^ 5) / 32 : L24)
    with hR3
  obtain ⟨hc10, hc1ν⟩ := c1_ν he hZ he0 hη1 hη1'
  have hR : Ge v 0 (3675 / 256 + σ * R3) :=
    ((c2_Ge he hZ).mono (by omega)).add (((Ge.self σ).mul (R3_integral he hZ ht)).mono (by omega))
  have hx : ν v (c1 * σ) = ν v σ := by rw [ν_mul hc10 hs0, hc1ν, zero_add]
  have hc0 := c0_ν he hZ
  have hF' : c1 * σ + ((1225 / 16384 : L24) + σ ^ 2 * (3675 / 256 + σ * R3)) = 0 := by
    rw [← hF]; ring
  have hF'' : (1225 / 16384 : L24) + (c1 * σ + σ ^ 2 * (3675 / 256 + σ * R3)) = 0 := by
    rw [← hF]; ring
  rcases lt_trichotomy (ν v σ) (2 * e) with h | h | h
  · exfalso
    refine add_ne_zero_of_Ge (v := v) (mul_ne_zero hc10 hs0) ?_ hF'
    rw [hx]
    exact (Ge.of_ν (by omega : ν v σ + 1 ≤ ν v (1225 / 16384 : L24))).add
      ((((Ge.self σ).pow 2).mul hR).mono (by push_cast; omega))
  · exact h
  · exfalso
    refine add_ne_zero_of_Ge (v := v) (by norm_num) ?_ hF''
    rw [hc0]
    exact (Ge.of_ν (by omega : 2 * e + 1 ≤ ν v (c1 * σ))).add
      ((((Ge.self σ).pow 2).mul hR).mono (by push_cast; omega))

/-- **Step 4** (local part): if `η ≡ 1 (mod 5²)` (`ν(η - 1) ≥ 2e`), every unit root is `≡ -1 ≡ 1/4`. -/
theorem step4_pos (hθ : aeval θ (fpoly η) = 0) (hη1 : Ge v (2 * e) (algebraMap ℚ L24 η - 1)) :
    Ge v 1 (θ - 1 / 4) := by
  have hθO : θ ∈ (v.valuation L24).integer := (Ge.of_ν ht).mem
  have h6 := fpoly_minus_one hθ
  have hRHS : Ge v e (-(5 * (20 * θ ^ 8 + 16 * θ ^ 7 + 11 * θ ^ 6 + 10 * θ ^ 5 - 3 * θ ^ 4 - 4 * θ ^ 3 -
      3 * θ ^ 2 - 2 * θ) + (algebraMap ℚ L24 η - 1) * (1 - 4 * θ))) := by
    refine Ge.neg (Ge.add ?_ ?_)
    · have := (Ge.of_ν (le_of_eq he.symm)).mul (Ge.of_mem (v := v)
        (by int_mem : 20 * θ ^ 8 + 16 * θ ^ 7 + 11 * θ ^ 6 + 10 * θ ^ 5 - 3 * θ ^ 4 - 4 * θ ^ 3 -
          3 * θ ^ 2 - 2 * θ ∈ (v.valuation L24).integer))
      simpa using this
    · exact (hη1.mul (Ge.of_mem (v := v) (by int_mem : 1 - 4 * θ ∈ (v.valuation L24).integer))).mono
        (by omega)
  rw [← h6] at hRHS
  have h1 : Ge v 1 (θ + 1) := by
    by_cases h0 : θ + 1 = 0
    · exact Or.inl h0
    rcases hRHS with h | h
    · exact absurd h (pow_ne_zero _ h0)
    · rw [ν_pow] at h; exact Or.inr (by push_cast at h; omega)
  rw [show θ - 1 / 4 = (θ + 1) + (-5 / 4 : L24) by ring]
  exact h1.add (Ge.of_ν (by
    rw [ν_const he hZ 1 (-1) 4 (by decide) (by decide) (by norm_num)]; push_cast; omega))

/-- **Step 4** (local part): if `η ≡ 1 (mod 5²)`, no root has `ν(θ - 1/4) = e`. -/
theorem step4_ne (hθ : aeval θ (fpoly η) = 0) (hη1 : Ge v (2 * e) (algebraMap ℚ L24 η - 1))
    (hs : ν v (θ - 1 / 4) = e) : False := by
  have hF := fpoly_quarter hθ
  set σ := θ - 1 / 4 with hσ
  have hc1 : Ge v (2 * e) ((-1225 - 2048 * (algebraMap ℚ L24 η - 1)) / 512 : L24) := by
    rw [div_eq_mul_one_div]
    have h512 : Ge v 0 (1 / 512 : L24) :=
      Ge.of_ν (le_of_eq (ν_unit_const he hZ 1 512 (by decide) (by decide) (by norm_num)).symm)
    have h2048 : Ge v (2 * e) (2048 * (algebraMap ℚ L24 η - 1)) := by
      have := (Ge.intCast (v := v) 2048).mul hη1
      simpa using this
    have h1225 : Ge v (2 * e) (-1225 : L24) := Ge.of_ν (by
      rw [ν_const he hZ 2 (-49) 1 (by decide) (by decide) (by norm_num)]; push_cast; omega)
    simpa using (h1225.sub h2048).mul h512
  set R3 := ((2205 + 6195 * σ + 10640 * σ ^ 2 + 11872 * σ ^ 3 + 8960 * σ ^ 4 + 3200 * σ ^ 5) / 32 : L24)
    with hR3
  have hF' : (1225 / 16384 : L24) + (((-1225 - 2048 * (algebraMap ℚ L24 η - 1)) / 512) * σ +
      (3675 / 256) * σ ^ 2 + σ ^ 3 * R3) = 0 := by
    rw [← hF]; ring
  refine add_ne_zero_of_Ge (v := v) (by norm_num) ?_ hF'
  rw [c0_ν he hZ]
  have hσ : Ge v e σ := Ge.of_ν (le_of_eq hs.symm)
  exact (((hc1.mul hσ).mono (by omega)).add (((c2_Ge he hZ).mul (hσ.pow 2)).mono (by push_cast; omega))).add
    (((hσ.pow 3).mul (R3_integral he hZ ht)).mono (by push_cast; omega))

end Steps45


/-! ## Step 6: the valuations of `θ - b` and `ψ(θ)` -/

section Step6

variable {η : ℚ} {θ : L24}

theorem sub_b_ne_zero (hη : η ≠ 0) (hθ : aeval θ (fpoly η) = 0) : θ - b ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  exact aeval_ψ_ne_zero hη hθ (by rw [h, b_root])

/-- `ψ(θ) = (θ - b) Q` with `Q = 25θ² + (25b + 20)θ + 25b² + 20b + 14`. -/
theorem ψ_eq_mul (θ : L24) : aeval θ ψ = (θ - b) * (25 * θ ^ 2 + (25 * b + 20) * θ + (25 * b ^ 2 + 20 * b + 14)) := by
  rw [aeval_ψ_L24]; linear_combination ψ_b

variable (he : ν v (5 : L24) = e) (he0 : 0 < e) (hZ : ∀ m : ℤ, ¬ (5 : ℤ) ∣ m → ν v (m : L24) = 0)
  (hη : η ≠ 0) (hθ : aeval θ (fpoly η) = 0)
include he he0 hZ hη hθ

omit he0 in
/-- The descent element: `ν(E) = 4e + ν(θ - b) + 3 ν(ψ(θ))` (`80000 = 2⁷ 5⁴`). -/
theorem ν_Edesc : ν v (Edesc θ) = 4 * e + ν v (θ - b) + 3 * ν v (aeval θ ψ) := by
  have h1 := sub_b_ne_zero hη hθ
  have h2 := aeval_ψ_ne_zero hη hθ
  rw [Edesc, ν_mul (mul_ne_zero (by norm_num) h1) (pow_ne_zero _ h2), ν_mul (by norm_num) h1, ν_pow,
    ν_const he hZ 4 128 1 (by decide) (by decide) (by norm_num)]
  push_cast
  ring

/-- At a prime with `ν(b) = 0` and `ν(θ) = 0`: `ν(θ - b) = ν(ψ(θ))` (the other factor `Q ≡ 14` is a unit). -/
theorem ν_sub_b_of_b1 (hb0 : ν v b = 0) (ht : ν v θ = 0) : ν v (θ - b) = ν v (aeval θ ψ) := by
  have hθO : θ ∈ (v.valuation L24).integer := (Ge.of_ν (le_of_eq ht.symm)).mem
  have hbO : b ∈ (v.valuation L24).integer := (Ge.of_ν (le_of_eq hb0.symm)).mem
  have h14 : ν v (14 : L24) = 0 := ν_unit_const he hZ 14 1 (by decide) (by decide) (by norm_num)
  have hR : Ge v (ν v (14 : L24) + 1) (5 * (5 * θ ^ 2 + (5 * b + 4) * θ + (5 * b ^ 2 + 4 * b))) := by
    rw [h14]
    have := (Ge.of_ν (le_of_eq he.symm)).mul (Ge.of_mem (v := v)
      (by int_mem : 5 * θ ^ 2 + (5 * b + 4) * θ + (5 * b ^ 2 + 4 * b) ∈ (v.valuation L24).integer))
    exact this.mono (by omega)
  have hQ : ν v (25 * θ ^ 2 + (25 * b + 20) * θ + (25 * b ^ 2 + 20 * b + 14)) = 0 := by
    rw [show 25 * θ ^ 2 + (25 * b + 20) * θ + (25 * b ^ 2 + 20 * b + 14) =
      14 + 5 * (5 * θ ^ 2 + (5 * b + 4) * θ + (5 * b ^ 2 + 4 * b)) by ring, ν_add_of_Ge (by norm_num) hR, h14]
  have hQ0 : (25 * θ ^ 2 + (25 * b + 20) * θ + (25 * b ^ 2 + 20 * b + 14) : L24) ≠ 0 := by
    rw [show 25 * θ ^ 2 + (25 * b + 20) * θ + (25 * b ^ 2 + 20 * b + 14) =
      14 + 5 * (5 * θ ^ 2 + (5 * b + 4) * θ + (5 * b ^ 2 + 4 * b)) by ring]
    exact add_ne_zero_of_Ge (by norm_num) hR
  rw [ψ_eq_mul, ν_mul (sub_b_ne_zero hη hθ) hQ0, hQ, add_zero]

omit he0 in
/-- At a unit prime: `ν(ψ(θ)) = ν(η) + ν(4θ - 1)`. -/
theorem ν_ψ_of_zero (ht : ν v θ = 0) :
    ν v (aeval θ ψ) = ν v (algebraMap ℚ L24 η) + ν v (4 * θ - 1) := by
  have := ν_fibre he hZ hη hθ
  omega

/-- **Step 6(b)**, `n > 0`: at the prime with `ν(b) = 0` above `p_B`, `ν(ψ(θ)) = ν(η) + 2e`. -/
theorem pB_pos (hb0 : ν v b = 0) (ht : ν v θ = 0) (hN : 0 < ν v (algebraMap ℚ L24 η)) :
    ν v (aeval θ ψ) = ν v (algebraMap ℚ L24 η) + 2 * e := by
  have hs := ν_sub_b_of_b1 he he0 hZ hη hθ hb0 ht
  have hf := ν_ψ_of_zero he hZ hη hθ ht
  have hD := sub_b_ne_zero hη hθ
  have h4b := ν_one_sub_four_b he he0 hZ hb0
  have h4b0 : (1 - 4 * b : L24) ≠ 0 := by intro h0; rw [h0, ν_zero] at h4b; omega
  have h4D : ν v (4 * (θ - b)) = ν v (θ - b) := by
    rw [ν_mul (by norm_num) hD, ν_unit_const he hZ 4 1 (by decide) (by decide) (by norm_num), zero_add]
  have e4 : 4 * θ - 1 = 4 * (θ - b) + -(1 - 4 * b) := by ring
  rcases lt_trichotomy (ν v (θ - b)) (2 * e) with h | h | h
  · have : ν v (4 * θ - 1) = ν v (θ - b) := by
      rw [e4, ν_add_of_Ge (mul_ne_zero (by norm_num) hD) (Ge.of_ν (by rw [ν_neg, h4D]; omega)), h4D]
    omega
  · exfalso
    have hge : Ge v (2 * e) (4 * θ - 1) := by
      rw [e4]
      exact (Ge.of_ν (le_of_eq (by rw [h4D, h]))).add (Ge.of_ν (by rw [ν_neg]; omega))
    rcases hge with h0 | h0
    · exact four_θ_sub_one_ne hη hθ h0
    · omega
  · have : ν v (4 * θ - 1) = 2 * e := by
      rw [e4, add_comm, ν_add_of_Ge (neg_ne_zero.mpr h4b0) (Ge.of_ν (by rw [ν_neg, h4D]; omega)), ν_neg, h4b]
    omega

omit he he0 hZ hη hθ in
/-- **Step 6(a)**: at the prime with `ν(b) = 0` above `p_A`, when `ν(θ) > 0`: `ν(θ - b) = 0`. -/
theorem pA_pos (hb0 : ν v b = 0) (ht : 0 < ν v θ) : ν v (θ - b) = 0 := by
  rw [sub_eq_neg_add, ν_add_of_Ge (neg_ne_zero.mpr b_ne_zero) (Ge.of_ν (by rw [ν_neg]; omega)), ν_neg, hb0]

omit hη hθ in
/-- **Step 6(a)**, `n = 0`: at the prime with `ν(b) = 0` above `p_A`, if `θ ≢ 1/4` then `ν(θ - b) = 0`. -/
theorem pA_zero (hb0 : ν v b = 0) (hs0 : θ - 1 / 4 ≠ 0) (hs : ν v (θ - 1 / 4) = 0) : ν v (θ - b) = 0 := by
  have h4b := ν_one_sub_four_b he he0 hZ hb0
  rw [show θ - b = (θ - 1 / 4) + (1 - 4 * b) / 4 by ring, ν_add_of_Ge hs0, hs]
  refine Ge.of_ν ?_
  by_cases h0 : (1 - 4 * b : L24) = 0
  · rw [h0, ν_zero] at h4b; omega
  rw [hs, ν_div h0 (by norm_num), h4b, ν_unit_const he hZ 4 1 (by decide) (by decide) (by norm_num)]
  omega

omit he hZ hη hθ in
/-- At a prime with `ν(b) = -e` where `θ` is integral: `ν(θ - b) = -e`. -/
theorem sub_b2 (hb1 : ν v b = -e) (ht : 0 ≤ ν v θ) : ν v (θ - b) = -e := by
  rw [sub_eq_neg_add, ν_add_of_Ge (neg_ne_zero.mpr b_ne_zero), ν_neg, hb1]
  rw [ν_neg, hb1]
  by_cases hθ0 : θ = 0
  · exact Or.inl hθ0
  · exact Or.inr (by omega)

omit he hZ in
/-- **Step 6(c)**: at a prime with `ν(θ) = -e` and `ν(b) = 0`: `ν(θ - b) = -e`. -/
theorem pC_b1 (hb0 : ν v b = 0) (ht : ν v θ = -e) : ν v (θ - b) = -e := by
  rw [sub_eq_add_neg, ν_add_of_Ge (θ_ne_zero hη hθ) (Ge.of_ν (by rw [ν_neg, hb0]; omega)), ht]

/-- **Step 6(c)**: at a prime with `ν(θ) = -e`, `ν(b) = -e` and `2 ν(ψ'(b)) = 5e` (`v₅(b₂ - b₃) = 3/2`):
`2 ν(θ - b) ∈ {-2e, 3e, 2 ν(η) + 3e}`. -/
theorem pC_b2 (hb1 : ν v b = -e) (ht : ν v θ = -e) (hdψ0 : (75 * b ^ 2 + 40 * b + 14 : L24) ≠ 0)
    (hdψ : 2 * ν v (75 * b ^ 2 + 40 * b + 14) = 5 * e) (hN : 0 ≤ ν v (algebraMap ℚ L24 η)) :
    2 * ν v (θ - b) = -2 * e ∨ 2 * ν v (θ - b) = 3 * e ∨
      2 * ν v (θ - b) = 2 * ν v (algebraMap ℚ L24 η) + 3 * e := by
  have hD0 := sub_b_ne_zero hη hθ
  have hψ := ν_ψ_of_neg_e he he0 hZ hη hθ ht
  have hQ : aeval θ ψ = (θ - b) * (25 * (θ - b) ^ 2 + (75 * b + 20) * (θ - b) + (75 * b ^ 2 + 40 * b + 14)) := by
    rw [aeval_ψ_L24]; linear_combination ψ_b
  have hQ0 : (25 * (θ - b) ^ 2 + (75 * b + 20) * (θ - b) + (75 * b ^ 2 + 40 * b + 14) : L24) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hQ; exact aeval_ψ_ne_zero hη hθ hQ
  have hνQ : ν v (25 * (θ - b) ^ 2 + (75 * b + 20) * (θ - b) + (75 * b ^ 2 + 40 * b + 14)) =
      ν v (algebraMap ℚ L24 η) + 4 * e - ν v (θ - b) := by
    have := congrArg (ν v) hQ
    rw [ν_mul hD0 hQ0, hψ] at this
    omega
  have hd : -e ≤ ν v (θ - b) := by
    have hG : Ge v (-e) (θ - b) := (Ge.of_ν (le_of_eq ht.symm)).sub (Ge.of_ν (le_of_eq hb1.symm))
    rcases hG with h | h
    · exact absurd h hD0
    · exact h
  have h75 := ν_75b_20 he he0 hZ hb1
  have h750 : (75 * b + 20 : L24) ≠ 0 := by intro h0; rw [h0, ν_zero] at h75; omega
  have hT1 : ν v (25 * (θ - b) ^ 2) = 2 * e + 2 * ν v (θ - b) := by
    rw [ν_mul (by norm_num) (pow_ne_zero _ hD0), ν25 he hZ, ν_pow]; push_cast; ring
  have hT2 : ν v ((75 * b + 20) * (θ - b)) = e + ν v (θ - b) := by rw [ν_mul h750 hD0, h75]
  rcases eq_or_lt_of_le hd with h | h
  · exact Or.inl (by omega)
  rcases lt_trichotomy (2 * (e + ν v (θ - b))) (5 * e) with h' | h' | h'
  · exfalso
    have : ν v (25 * (θ - b) ^ 2 + (75 * b + 20) * (θ - b) + (75 * b ^ 2 + 40 * b + 14)) = e + ν v (θ - b) := by
      rw [show 25 * (θ - b) ^ 2 + (75 * b + 20) * (θ - b) + (75 * b ^ 2 + 40 * b + 14) =
        (75 * b + 20) * (θ - b) + (25 * (θ - b) ^ 2 + (75 * b ^ 2 + 40 * b + 14)) by ring,
        ν_add_of_Ge (mul_ne_zero h750 hD0), hT2]
      rw [hT2]
      exact (Ge.of_ν (by omega : e + ν v (θ - b) + 1 ≤ ν v (25 * (θ - b) ^ 2))).add
        (Ge.of_ν (by omega : e + ν v (θ - b) + 1 ≤ ν v (75 * b ^ 2 + 40 * b + 14)))
    omega
  · exact Or.inr (Or.inl (by omega))
  · have : ν v (25 * (θ - b) ^ 2 + (75 * b + 20) * (θ - b) + (75 * b ^ 2 + 40 * b + 14)) =
        ν v (75 * b ^ 2 + 40 * b + 14) := by
      rw [show 25 * (θ - b) ^ 2 + (75 * b + 20) * (θ - b) + (75 * b ^ 2 + 40 * b + 14) =
        (75 * b ^ 2 + 40 * b + 14) + (25 * (θ - b) ^ 2 + (75 * b + 20) * (θ - b)) by ring, ν_add_of_Ge hdψ0]
      exact (Ge.of_ν (by omega : ν v (75 * b ^ 2 + 40 * b + 14) + 1 ≤ ν v (25 * (θ - b) ^ 2))).add
        (Ge.of_ν (by omega : ν v (75 * b ^ 2 + 40 * b + 14) + 1 ≤ ν v ((75 * b + 20) * (θ - b))))
    exact Or.inr (Or.inr (by omega))

end Step6

end

end X2Y5Z7.FiveAdic
