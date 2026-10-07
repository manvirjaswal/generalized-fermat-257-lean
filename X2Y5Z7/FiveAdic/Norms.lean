import X2Y5Z7.FiveAdic.Group
import X2Y5Z7.FiveAdic.Local
import X2Y5Z7.FiveAdic.Cert
import X2Y5Z7.Auxiliary.Generators
import Mathlib.RingTheory.Adjoin.PowerBasis

/-! # Norms, and the valuations of `b` at the primes above 5 (Lemmas 2.5, 2.6)

* `norm_sub_rat`: for a root `θ` of `f_η` generating `L₈` and `c ∈ ℚ`, `N_{L₈/ℚ}(θ - c) = f_η(c)/100` (the
  minimal polynomial of `θ` is `f_η/100`); with the product formula this gives
  `Σ_k ν_{Q k}(θ - c) = 3 (v₅(f_η(c)) - 2)` (`sum_ν_sub_rat`), which replaces the counting of roots by slopes.
* `sum_ν_b`: `Σ_k ν_{Q k}(b) = v₅(N(b)) = 8 v₅(-14/25) = -16`.
* `ν_z`: `z = ψ'(b)² b⁵ = -1200b² - 280b - 56` is an algebraic integer (`z³ - 632z² - 460992z + 421654016 = 0`)
  of norm `(-2⁹ 7⁷)⁸`, so `ν_{Q k}(z) = 0` for all `k`: `2 ν(ψ'(b)) = -5 ν(b)` (`v₅(b₂ - b₃) = 3/2`).
* `ν_Q3_b`: `5b + 2 ∈ P₅ = Q 3` (`Cert.lean`), so `ν_{Q 3}(b) = -e`.
* `b_types`: `ν(b) = 0` at `Q 1, Q 5` (the primes `P₃, P₇` with odd `e`, by `ν_z`), `ν(b) = -e` at `Q 3, Q 4`. -/

namespace X2Y5Z7.FiveAdic

open Polynomial IsDedekindDomain NumberField Integral Prop31

noncomputable section

/-! ## `v₅` of rational constants -/

theorem padicValRat_const (k : ℕ) (m d : ℤ) (hm : ¬ (5 : ℤ) ∣ m) (hd : ¬ (5 : ℤ) ∣ d) :
    padicValRat 5 (5 ^ k * m / d) = k := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have hd0 : d ≠ 0 := by rintro rfl; exact hd (dvd_zero _)
  rw [padicValRat.div (mul_ne_zero (pow_ne_zero _ (by norm_num)) (Int.cast_ne_zero.mpr hm0))
      (Int.cast_ne_zero.mpr hd0), padicValRat.mul (pow_ne_zero _ (by norm_num)) (Int.cast_ne_zero.mpr hm0),
    padicValRat.pow, padicValRat.of_int, padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hm,
    padicValInt.eq_zero_of_not_dvd hd]
  have h55 : padicValRat 5 (5 : ℚ) = 1 := by exact_mod_cast padicValRat.self (p := 5) (by norm_num)
  rw [h55]
  push_cast
  ring

/-! ## `N_{L₈/ℚ}(θ - c)` -/

section NormSub

variable {η : ℚ} {θ : L8}

theorem fpoly_eq (η : ℚ) :
    fpoly η = 100 * X ^ 8 + 80 * X ^ 7 + 56 * X ^ 6 + 56 * X ^ 5 - 4 * C η * X + C η := by
  simp only [fpoly, ψ, ψZ, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_ofNat, map_ofNat C 4]
  ring

theorem fpoly_natDegree (η : ℚ) : (fpoly η).natDegree = 8 := by
  rw [fpoly_eq]
  compute_degree!

theorem fpoly_leadingCoeff (η : ℚ) : (fpoly η).leadingCoeff = 100 := by
  rw [leadingCoeff, fpoly_natDegree, fpoly_eq]
  simp [coeff_X_pow]

/-- The minimal polynomial of a generating root: `f_η = 100 · minpoly θ`. -/
theorem fpoly_eq_minpoly (hθ : aeval θ (fpoly η) = 0) (hgen : Algebra.adjoin ℚ {θ} = ⊤) :
    fpoly η = C 100 * minpoly ℚ θ := by
  have hint : IsIntegral ℚ θ := Algebra.IsIntegral.isIntegral θ
  have htop : IntermediateField.adjoin ℚ {θ} = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hgen,
      IntermediateField.top_toSubalgebra]
  have h8 : (minpoly ℚ θ).natDegree = 8 := by
    rw [← IntermediateField.adjoin.finrank hint, htop, IntermediateField.finrank_top', L8_finrank]
  have hne : fpoly η ≠ 0 := by
    intro h0; have := fpoly_natDegree η; rw [h0, natDegree_zero] at this; norm_num at this
  obtain ⟨q, hq⟩ := minpoly.dvd ℚ θ hθ
  have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; exact hne hq
  have hdeg : q.natDegree = 0 := by
    have := congrArg natDegree hq
    rw [natDegree_mul (minpoly.ne_zero hint) hq0, h8, fpoly_natDegree] at this
    omega
  rw [eq_C_of_natDegree_eq_zero hdeg] at hq
  have hlc := congrArg leadingCoeff hq
  rw [fpoly_leadingCoeff, leadingCoeff_mul, minpoly.monic hint, one_mul, leadingCoeff_C] at hlc
  rw [hq, ← hlc, mul_comm]

/-- `N_{L₈/ℚ}(θ - c) = f_η(c)/100` for a root `θ` of `f_η` generating `L₈`. -/
theorem norm_sub_rat (hθ : aeval θ (fpoly η) = 0) (hgen : Algebra.adjoin ℚ {θ} = ⊤) (c : ℚ) :
    Algebra.norm ℚ (θ - algebraMap ℚ L8 c) = (fpoly η).eval c / 100 := by
  have hint : IsIntegral ℚ (θ - algebraMap ℚ L8 c) := Algebra.IsIntegral.isIntegral _
  have hgen' : Algebra.adjoin ℚ {θ - algebraMap ℚ L8 c} = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine Algebra.adjoin_le (Set.singleton_subset_iff.mpr ?_)
    have h1 : θ - algebraMap ℚ L8 c ∈ Algebra.adjoin ℚ {θ - algebraMap ℚ L8 c} :=
      Algebra.subset_adjoin (Set.mem_singleton _)
    simpa using add_mem h1 (Subalgebra.algebraMap_mem _ c)
  have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (PowerBasis.ofAdjoinEqTop hint hgen')
  rw [PowerBasis.ofAdjoinEqTop_gen, PowerBasis.ofAdjoinEqTop_dim, minpoly.sub_algebraMap] at h
  have hθi : IsIntegral ℚ θ := Algebra.IsIntegral.isIntegral θ
  have h8 : (minpoly ℚ θ).natDegree = 8 := by
    have := congrArg natDegree (fpoly_eq_minpoly hθ hgen)
    rw [fpoly_natDegree, natDegree_C_mul (by norm_num)] at this
    exact this.symm
  rw [h, natDegree_comp, h8, coeff_zero_eq_eval_zero, eval_comp]
  simp only [eval_add, eval_X, eval_C, zero_add]
  rw [fpoly_eq_minpoly hθ hgen, eval_mul, eval_C]
  norm_num

theorem fpoly_eval (η c : ℚ) :
    (fpoly η).eval c = 100 * c ^ 8 + 80 * c ^ 7 + 56 * c ^ 6 + 56 * c ^ 5 - 4 * η * c + η := by
  rw [fpoly_eq]
  simp

end NormSub

/-- The product formula for `θ - c`: `Σ_k ν_{Q k}(θ - c) = 3 (v₅(f_η(c)) - 2)`. -/
theorem sum_ν_sub_rat {η : ℚ} {θ : L8} (hθ : aeval θ (fpoly η) = 0) (hgen : Algebra.adjoin ℚ {θ} = ⊤) (c : ℚ)
    (hc : (fpoly η).eval c ≠ 0) :
    ∑ k : Fin 7, ν (Q k) (algebraMap L8 L24 θ - algebraMap ℚ L24 c) =
      3 * (padicValRat 5 ((fpoly η).eval c) - 2) := by
  have hN := norm_sub_rat hθ hgen c
  have hx : algebraMap L8 L24 θ - algebraMap ℚ L24 c = algebraMap L8 L24 (θ - algebraMap ℚ L8 c) := by
    rw [map_sub, ← IsScalarTower.algebraMap_apply]
  have hN0 : Algebra.norm ℚ (θ - algebraMap ℚ L8 c) ≠ 0 := by
    rw [hN]; exact div_ne_zero hc (by norm_num)
  have hx0 : algebraMap L8 L24 θ - algebraMap ℚ L24 c ≠ 0 := by
    rw [hx]; intro h0
    apply hN0
    rw [(map_eq_zero_iff _ (algebraMap L8 L24).injective).mp h0, Algebra.norm_zero]
  rw [← prodF _ hx0, hx, norm_algebraMap_L8, hN, padicValRat.pow, padicValRat.div hc (by norm_num)]
  have h100 : padicValRat 5 (100 : ℚ) = 2 := by
    have := padicValRat_const 2 4 1 (by decide) (by decide)
    norm_num at this
    exact this
  rw [h100]
  push_cast
  ring

/-! ## The valuations of `b` -/

theorem b_eq_rel : b = algebraMap L8 L24 0 + algebraMap L8 L24 1 * b + algebraMap L8 L24 0 * b ^ 2 := by simp

theorem norm_b : Algebra.norm ℚ b = (-14 / 25) ^ 8 := by
  rw [← Algebra.norm_norm (S := L8)]
  conv_lhs => rw [b_eq_rel]
  rw [norm_rel]
  simp only [Nf]
  rw [show (625 * 0 ^ 3 - 500 * 0 ^ 2 * 1 - 300 * 0 ^ 2 * 0 + 350 * 0 * 1 ^ 2 + 770 * 0 * 1 * 0 - 364 * 0 * 0 ^ 2 -
      350 * 1 ^ 3 + 280 * 1 ^ 2 * 0 - 196 * 1 * 0 ^ 2 + 196 * 0 ^ 3 : L8) / 625 = algebraMap ℚ L8 (-14 / 25) by
    rw [map_div₀, map_neg]; norm_num]
  rw [Algebra.norm_algebraMap, L8_finrank]

theorem sum_ν_b : ∑ k : Fin 7, ν (Q k) b = -16 := by
  rw [← prodF b b_ne_zero, norm_b, padicValRat.pow,
    show (-14 / 25 : ℚ) = 5 ^ 0 * (-14 : ℤ) / (25 : ℤ) by norm_num, padicValRat.div (by norm_num) (by norm_num),
    padicValRat.mul (by norm_num) (by norm_num)]
  have h1 : padicValRat 5 ((-14 : ℤ) : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd (by decide)]; rfl
  have h2 : padicValRat 5 ((25 : ℤ) : ℚ) = 2 := by
    have := padicValRat_const 2 1 1 (by decide) (by decide)
    norm_num at this ⊢
    exact this
  rw [h1, h2]
  simp

/-- `z = ψ'(b)² b⁵ = -1200b² - 280b - 56`. -/
theorem z_eq : (75 * b ^ 2 + 40 * b + 14) ^ 2 * b ^ 5 = -1200 * b ^ 2 - 280 * b - 56 := by
  linear_combination (225 * b ^ 6 + 60 * b ^ 5 - 26 * b ^ 4 - 94 * b ^ 3 + 64 * b ^ 2 + 16 * b + 4) * ψ_b

theorem z_isIntegral : IsIntegral ℤ (-1200 * b ^ 2 - 280 * b - 56 : L24) := by
  refine isIntegral_of_cubic _ 632 (-460992) (-421654016) ?_ ?_ ?_ ?_
  · exact_mod_cast isIntegral_algebraMap (R := ℤ) (A := L24) (x := 632)
  · exact_mod_cast isIntegral_algebraMap (R := ℤ) (A := L24) (x := -460992)
  · exact_mod_cast isIntegral_algebraMap (R := ℤ) (A := L24) (x := -421654016)
  · linear_combination (-69120000 * b ^ 3 + 6912000 * b ^ 2 - 24192000 * b + 31808000) * ψ_b

theorem z_eq_rel : (-1200 * b ^ 2 - 280 * b - 56 : L24) =
    algebraMap L8 L24 (-56) + algebraMap L8 L24 (-280) * b + algebraMap L8 L24 (-1200) * b ^ 2 := by
  simp only [map_neg, map_ofNat]; ring

theorem norm_z : Algebra.norm ℚ (-1200 * b ^ 2 - 280 * b - 56 : L24) = (-421654016) ^ 8 := by
  rw [← Algebra.norm_norm (S := L8), z_eq_rel, norm_rel]
  simp only [Nf]
  rw [show (625 * (-56) ^ 3 - 500 * (-56) ^ 2 * (-280) - 300 * (-56) ^ 2 * (-1200) + 350 * (-56) * (-280) ^ 2 +
      770 * (-56) * (-280) * (-1200) - 364 * (-56) * (-1200) ^ 2 - 350 * (-280) ^ 3 + 280 * (-280) ^ 2 * (-1200) -
      196 * (-280) * (-1200) ^ 2 + 196 * (-1200) ^ 3 : L8) / 625 = algebraMap ℚ L8 (-421654016) by
    rw [map_neg]; norm_num]
  rw [Algebra.norm_algebraMap, L8_finrank]

theorem z_ne_zero : (-1200 * b ^ 2 - 280 * b - 56 : L24) ≠ 0 := by
  intro h0
  have := norm_z
  rw [h0, Algebra.norm_zero] at this
  norm_num at this

/-- `ν_{Q k}(ψ'(b)² b⁵) = 0`: `z` is integral and `v₅(N(z)) = 0`. -/
theorem ν_z (k : Fin 7) : ν (Q k) (-1200 * b ^ 2 - 280 * b - 56 : L24) = 0 := by
  have hsum := prodF _ z_ne_zero
  rw [norm_z, padicValRat.pow, show (-421654016 : ℚ) = ((-421654016 : ℤ) : ℚ) by norm_num, padicValRat.of_int,
    padicValInt.eq_zero_of_not_dvd (by decide)] at hsum
  have hnn : ∀ l : Fin 7, 0 ≤ ν (Q l) (-1200 * b ^ 2 - 280 * b - 56 : L24) :=
    fun l => ν_nonneg_of_isIntegral l z_isIntegral
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => hnn l)).mp (by rw [← hsum]; simp) k (Finset.mem_univ k)
  exact this

theorem dψ_ne_zero : (75 * b ^ 2 + 40 * b + 14 : L24) ≠ 0 := by
  intro h0
  apply z_ne_zero
  rw [← z_eq, h0]
  ring

/-- **Lemma 2.6** (`v₅(b₂ - b₃) = 3/2`, i.e. `v₅(ψ'(b₂)) = 5/2`): `2 ν(ψ'(b)) = -5 ν(b)` at every prime above 5. -/
theorem ν_dψ (k : Fin 7) : 2 * ν (Q k) (75 * b ^ 2 + 40 * b + 14) = -5 * ν (Q k) b := by
  have h := ν_z k
  rw [← z_eq, ν_mul (pow_ne_zero _ dψ_ne_zero) (pow_ne_zero _ b_ne_zero), ν_pow, ν_pow] at h
  push_cast at h
  omega

/-- `5b + 2 ∈ P₅ = Q 3` (`Cert.lean`), so `ν_{Q 3}(b) = -2`. -/
theorem ν_Q3_b : ν (Q 3) b = -2 := by
  have hrel : ev Ynum5 / (Yden5 : L24) * B 4 = 5 * b + 2 := by
    have h := relY5
    rw [ev_mul, SUnits.ev_smul_const] at h
    have hY : (Yden5 : L24) ≠ 0 := by norm_num [Yden5]
    have hB : (Bden 4 : L24) ≠ 0 := SUnits.Bden_ne_zero 4
    have e2 : ev [[2], [5]] = 2 + 5 * b := by simp [ev, P2.eval, P1.eval]; ring
    rw [e2] at h
    simp only [B]
    field_simp
    push_cast at h
    linear_combination h
  have hBν : ν (Q 3) (B 4) = 1 := by rw [ν_B]; rfl
  have hne : (5 * b + 2 : L24) ≠ 0 := by
    intro h0
    have : (10 : L24) = 0 := by linear_combination ψ_b - (5 * b ^ 2 + 2 * b + 2) * h0
    norm_num at this
  have hY0 : ev Ynum5 / (Yden5 : L24) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hrel; exact hne hrel.symm
  have hge : 1 ≤ ν (Q 3) (5 * b + 2) := by
    rw [← hrel, ν_mul hY0 (B_ne_zero 4), hBν]
    have := ν_nonneg_of_isIntegral 3 isIntegral_Y5
    omega
  have h2 : ν (Q 3) (-2 : L24) = 0 := by
    have := ν_int_prime_to_five 3 (-2) (by decide)
    simpa using this
  have h5b : ν (Q 3) (5 * b) = 0 := by
    rw [show 5 * b = (-2 : L24) + (5 * b + 2) by ring, ν_add_of_Ge (by norm_num) (Ge.of_ν (by omega)), h2]
  rw [ν_mul (by norm_num) b_ne_zero, ν_five] at h5b
  have : eQ 3 = 2 := rfl
  omega

theorem ν_b_Q (k : Fin 7) : ν (Q k) b = 0 ∨ ν (Q k) b = -eQ k :=
  ν_b_cases (ν_five k) (eQ_pos k) (hZ_Q k)

/-- The primes `P₃, P₇` (`Q 1, Q 5`) have `b ↦ b₁` (`ν(b) = 0`), and `P₅, P₆` (`Q 3, Q 4`) have `b ↦ b₂`
(`ν(b) = -e`) (Lemma 2.5). -/
theorem b_types : ν (Q 1) b = 0 ∧ ν (Q 5) b = 0 ∧ ν (Q 3) b = -2 ∧ ν (Q 4) b = -10 := by
  have h1 : ν (Q 1) b = 0 := by
    rcases ν_b_Q 1 with h | h
    · exact h
    · have := ν_dψ 1; rw [h] at this; simp [eQ] at this; omega
  have h5 : ν (Q 5) b = 0 := by
    rcases ν_b_Q 5 with h | h
    · exact h
    · have := ν_dψ 5; rw [h] at this; simp [eQ] at this; omega
  have h3 := ν_Q3_b
  refine ⟨h1, h5, h3, ?_⟩
  have hs := sum_ν_b
  rw [Fin.sum_univ_seven] at hs
  have h0 := ν_b_Q 0
  have h2 := ν_b_Q 2
  have h4 := ν_b_Q 4
  have h6 := ν_b_Q 6
  simp only [eQ] at h0 h2 h4 h6
  norm_num at h0 h2 h4 h6
  omega

theorem b_add_one_ne : b + 1 ≠ 0 := by
  intro h0
  have : (5 : L24) = 0 := by linear_combination -ψ_b + (25 * b ^ 2 - 5 * b + 19) * h0
  norm_num at this

theorem five_b_add_two_ne : 5 * b + 2 ≠ 0 := by
  intro h0
  have : (10 : L24) = 0 := by linear_combination ψ_b - (5 * b ^ 2 + 2 * b + 2) * h0
  norm_num at this

/-- **Lemma 2.6**, at the primes of `L₂₄` above 5. At each `Q k` either `b ↦ b₁` (`ν(b) = 0`; then `b ≡ -1` and
`ν(4b - 1) = 2e`, i.e. `v₅(4b₁ - 1) = 2`) or `b ↦ b₂, b₃` (`ν(b) = -e`, i.e. `v₅(b₂) = v₅(b₃) = -1`; then
`5b ≡ -2` and `2ν(ψ'(b)) = 5e`, i.e. `v₅(ψ'(b₂)) = v₅(25 (b₂ - b₁)(b₂ - b₃)) = 5/2`, `v₅(b₂ - b₃) = 3/2`). -/
theorem lemma_2_6 (k : Fin 7) :
    (ν (Q k) b = 0 ∧ eQ k ≤ ν (Q k) (b + 1) ∧ ν (Q k) (1 - 4 * b) = 2 * eQ k) ∨
      (ν (Q k) b = -eQ k ∧ 1 ≤ ν (Q k) (5 * b + 2) ∧ 2 * ν (Q k) (75 * b ^ 2 + 40 * b + 14) = 5 * eQ k) := by
  rcases ν_b_Q k with hb | hb
  · left
    refine ⟨hb, ?_, ν_one_sub_four_b (ν_five k) (eQ_pos k) (hZ_Q k) hb⟩
    rcases b1_add_one (ν_five k) (eQ_pos k) (hZ_Q k) hb with h | h
    · exact absurd h b_add_one_ne
    · exact h
  · right
    refine ⟨hb, ?_, by rw [ν_dψ, hb]; ring⟩
    rcases b2_five_b_add_two (ν_five k) (eQ_pos k) hb with h | h
    · exact absurd h five_b_add_two_ne
    · exact h

end

end X2Y5Z7.FiveAdic
