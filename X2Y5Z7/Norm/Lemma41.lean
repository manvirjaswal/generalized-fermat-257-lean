import X2Y5Z7.Norm.Basic
import X2Y5Z7.SUnits.Theorems
import X2Y5Z7.Descent.Valuations
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! # Lemma 4.1: the valuation of the descent element at the prime above 2

`P1 = (B₁)` is the only prime of `L₂₄` above 2 (`eq_P1_of_two_mem`, from `Sprimes_eq`) and `N(B₁) = -2`, so
`v_{P1}(α) = v₂(N_{L₂₄/ℚ}(α))` for `α ≠ 0` (`count_P1_eq`): writing `α = B₁^m y` with `y` a `P1`-unit and `y = n/d`
with `n, d ∈ 𝓞 L₂₄ \ P1`, the norms of `n` and `d` are odd (`not_two_dvd_norm`: otherwise `(n) + (2) ≠ (1)`, as the
residue ring `𝓞/(n)` has an element of additive order 2, and a maximal ideal containing `n` and `2` is `P1`).

By Proposition 3.2, `N_{L₂₄/ℚ}(E) = N_{L₈/ℚ}(2²¹ · 5¹⁰ · ψ(θ)¹⁰) = 2¹⁶⁸ · 5⁸⁰ · N_{L₈/ℚ}(ψ(θ))¹⁰`, so
`v_{P1}(E) = 168 + 10 v₂(N_{L₈/ℚ}(ψ(θ))) ≡ 3 (mod 5)` (`count_Edesc_P1`). -/

namespace X2Y5Z7.Norm

open Polynomial IsDedekindDomain NumberField
open scoped nonZeroDivisors

noncomputable section

theorem Bint0_ne_zero : Bint 0 ≠ 0 := by
  intro h
  apply Bint_span_ne_bot 0
  rw [h, Ideal.span_singleton_eq_bot]

/-- The prime `P₁ = (B₁)` of `L₂₄` above 2. -/
def P1 : HeightOneSpectrum (𝓞 L24) where
  asIdeal := Ideal.span {Bint 0}
  isPrime := Bint_span_isPrime 0 (by decide)
  ne_bot := Bint_span_ne_bot 0

/-- `P₁` is the only prime of `L₂₄` above 2. -/
theorem eq_P1_of_two_mem (v : HeightOneSpectrum (𝓞 L24)) (h2 : (2 : 𝓞 L24) ∈ v.asIdeal) :
    v.asIdeal = P1.asIdeal := by
  obtain ⟨i, hi, hv⟩ := Sprimes_eq v (Or.inl h2)
  have hSp := Sp_mem i hi
  rw [← hv] at hSp
  have hone : ∀ c : ℕ, c = 5 ∨ c = 7 → (c : 𝓞 L24) ∈ v.asIdeal → False := by
    intro c hc hcm
    have h1 : (1 : 𝓞 L24) ∈ v.asIdeal := by
      rcases hc with rfl | rfl
      · have := v.asIdeal.sub_mem hcm (v.asIdeal.mul_mem_left 2 h2)
        convert this using 1
        norm_num
      · have := v.asIdeal.sub_mem hcm (v.asIdeal.mul_mem_left 3 h2)
        convert this using 1
        norm_num
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hi0 : i = 0 := by
    fin_cases i
    · rfl
    all_goals first
      | exact absurd hi (by decide)
      | exact (hone 5 (Or.inl rfl) hSp).elim
      | exact (hone 7 (Or.inr rfl) hSp).elim
  subst hi0
  exact hv

theorem natCard_quot_eq (I : Ideal (𝓞 L24)) : Nat.card (𝓞 L24 ⧸ I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

/-- An integer of `L₂₄` outside `P₁` has odd norm. -/
theorem not_two_dvd_norm (n : 𝓞 L24) (hn : n ∉ P1.asIdeal) : ¬ (2 : ℤ) ∣ Algebra.norm ℤ n := by
  intro h2
  set I := Ideal.span {n}
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (Ideal.zero_mem _)
  have hI0 : I ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hcard : 2 ∣ Ideal.absNorm I := by
    rw [Ideal.absNorm_span_singleton]
    exact Int.natAbs_dvd_natAbs.mpr h2
  -- `(n) + (2) ≠ (1)`
  have hne : I ⊔ Ideal.span {2} ≠ ⊤ := by
    intro htop
    have h1 : (1 : 𝓞 L24) ∈ I ⊔ Ideal.span {2} := htop ▸ Submodule.mem_top
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp h1
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    have : Finite (𝓞 L24 ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI0
    let _ := Fintype.ofFinite (𝓞 L24 ⧸ I)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hc : 2 ∣ Fintype.card (𝓞 L24 ⧸ I) := by
      rw [← Nat.card_eq_fintype_card, natCard_quot_eq]
      exact hcard
    obtain ⟨z, hz⟩ := exists_prime_addOrderOf_dvd_card 2 hc
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, addOrderOf_zero] at hz
      exact absurd hz (by decide)
    have h2z : (2 : 𝓞 L24 ⧸ I) * z = 0 := by
      have := addOrderOf_nsmul_eq_zero z
      rw [hz, two_nsmul] at this
      rw [two_mul]
      exact this
    have hr : (Ideal.Quotient.mk I r) * 2 = 1 := by
      have hx0 : Ideal.Quotient.mk I x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
      have := congrArg (Ideal.Quotient.mk I) hxy
      rw [map_add, map_mul, hx0, zero_add, map_one, map_ofNat] at this
      exact this
    apply hz0
    calc z = (Ideal.Quotient.mk I r * 2) * z := by rw [hr, one_mul]
      _ = Ideal.Quotient.mk I r * (2 * z) := mul_assoc _ _ _
      _ = 0 := by rw [h2z, mul_zero]
  -- a maximal ideal containing `n` and `2` is `P₁`
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have h2M : (2 : 𝓞 L24) ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self 2))
  have hnM : n ∈ M := hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self n))
  have hM0 : M ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at h2M
    exact two_ne_zero h2M
  let v : HeightOneSpectrum (𝓞 L24) := ⟨M, hM.isPrime, hM0⟩
  have hv := eq_P1_of_two_mem v h2M
  exact hn (hv ▸ hnM)

/-- The norm `N_{L₂₄/ℚ}` as a homomorphism of monoids with zero. -/
def normQ : L24 →*₀ ℚ where
  toFun := Algebra.norm ℚ
  map_zero' := Algebra.norm_zero
  map_one' := map_one _
  map_mul' := map_mul _

theorem normQ_apply (x : L24) : normQ x = Algebra.norm ℚ x := rfl

theorem padicValRat_norm_of_not_mem (n : 𝓞 L24) (hn : n ∉ P1.asIdeal) :
    padicValRat 2 (Algebra.norm ℚ (algebraMap (𝓞 L24) L24 n)) = 0 := by
  rw [← Algebra.coe_norm_int, padicValRat.of_int]
  have : ¬ ((2 : ℕ) : ℤ) ∣ Algebra.norm ℤ n := by exact_mod_cast not_two_dvd_norm n hn
  exact_mod_cast padicValInt.eq_zero_of_not_dvd this

theorem val_B0 : P1.valuation L24 (B 0) = WithZero.exp (-1 : ℤ) := by
  rw [show B 0 = algebraMap (𝓞 L24) L24 (Bint 0) from rfl, HeightOneSpectrum.valuation_of_algebraMap]
  exact P1.intValuation_singleton Bint0_ne_zero rfl

theorem B0_ne_zero : B 0 ≠ 0 := by
  intro h
  apply Bint0_ne_zero
  apply IsFractionRing.injective (𝓞 L24) L24
  rw [map_zero]
  exact h

/-- `v_{P₁}(α) = v₂(N_{L₂₄/ℚ}(α))`. -/
theorem count_P1_eq (x : L24) (hx : x ≠ 0) :
    FractionalIdeal.count L24 P1 (FractionalIdeal.spanSingleton (𝓞 L24)⁰ x) =
      padicValRat 2 (Algebra.norm ℚ x) := by
  have hm := Prop31.count_eq_neg_log P1 hx
  set m := FractionalIdeal.count L24 P1 (FractionalIdeal.spanSingleton (𝓞 L24)⁰ x)
  have hVx0 : P1.valuation L24 x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have hVx : P1.valuation L24 x = WithZero.exp (-m) := by
    rw [hm, neg_neg, WithZero.exp_log hVx0]
  -- `y = x · B₁^{-m}` is a `P₁`-unit
  set y := x * B 0 ^ (-m)
  have hVy : P1.valuation L24 y = 1 := by
    rw [map_mul, map_zpow₀, val_B0, hVx, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer P1 y (le_of_eq hVy)
  have hd : (d : 𝓞 L24) ∉ P1.asIdeal := d.2
  have hn : n ∉ P1.asIdeal := by
    have hVd : P1.valuation L24 (algebraMap (𝓞 L24) L24 d) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      exact hd
    have h := congrArg (P1.valuation L24) hnd
    rw [map_mul, hVy, hVd, one_mul, HeightOneSpectrum.valuation_of_algebraMap,
      eq_comm, HeightOneSpectrum.intValuation_eq_one_iff] at h
    exact h
  have hd0 : algebraMap (𝓞 L24) L24 d ≠ 0 := by
    intro h0
    apply hd
    rw [(IsFractionRing.injective (𝓞 L24) L24).eq_iff.mp (h0.trans (map_zero _).symm)]
    exact Ideal.zero_mem _
  have hy0 : y ≠ 0 := mul_ne_zero hx (zpow_ne_zero _ B0_ne_zero)
  have hn0 : algebraMap (𝓞 L24) L24 n ≠ 0 := by
    rw [← hnd]; exact mul_ne_zero hy0 hd0
  -- norms
  have hxy : x = y * B 0 ^ m := by
    rw [mul_assoc, ← zpow_add₀ B0_ne_zero, neg_add_cancel, zpow_zero, mul_one]
  have hNB : Algebra.norm ℚ (B 0) = -2 := B_norm_0
  have hNn : Algebra.norm ℚ (algebraMap (𝓞 L24) L24 n) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hn0
  have hNd : Algebra.norm ℚ (algebraMap (𝓞 L24) L24 d) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hd0
  have hNy : Algebra.norm ℚ y = Algebra.norm ℚ (algebraMap (𝓞 L24) L24 n) /
      Algebra.norm ℚ (algebraMap (𝓞 L24) L24 d) := by
    rw [eq_div_iff hNd, ← map_mul, hnd]
  have hNx : Algebra.norm ℚ x = Algebra.norm ℚ y * (-2) ^ m := by
    rw [← normQ_apply, hxy, map_mul, map_zpow₀, normQ_apply, normQ_apply, hNB]
  rw [hNx, padicValRat.mul (by rw [hNy]; exact div_ne_zero hNn hNd) (zpow_ne_zero _ (by norm_num)),
    padicValRat.zpow, padicValRat.neg, hNy, padicValRat.div hNn hNd,
    padicValRat_norm_of_not_mem n hn, padicValRat_norm_of_not_mem d hd]
  have : padicValRat 2 (2 : ℚ) = 1 := by
    have := padicValRat.self (p := 2) (by norm_num)
    exact_mod_cast this
  rw [this]
  ring

/-- **Lemma 4.1.** For `θ ∈ L₈` with `ψ(θ) ≠ 0`, the valuation of `E = 80000 (θ - b) ψ(θ)³` at the prime `P₁` of
`L₂₄` above 2 is `≡ 3 (mod 5)`. -/
theorem count_Edesc_P1 (θ : L8) (hθ : aeval θ ψ ≠ 0) :
    FractionalIdeal.count L24 P1 (FractionalIdeal.spanSingleton (𝓞 L24)⁰ (Edesc (algebraMap L8 L24 θ))) ≡ 3
      [ZMOD 5] := by
  have hN := norm_Edesc θ hθ
  have hN8 : Algebra.norm ℚ (aeval θ ψ) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hθ
  have hE0 : Edesc (algebraMap L8 L24 θ) ≠ 0 := by
    intro h0
    rw [h0, Algebra.norm_zero] at hN
    exact (mul_ne_zero (by norm_num) (pow_ne_zero 10 hθ)) hN.symm
  have hNQ : Algebra.norm ℚ (Edesc (algebraMap L8 L24 θ)) =
      (2 ^ 168 * 5 ^ 80 : ℚ) * Algebra.norm ℚ (aeval θ ψ) ^ 10 := by
    rw [← Algebra.norm_norm (S := L8), hN, map_mul, map_pow,
      show (2 ^ 21 * 5 ^ 10 : L8) = algebraMap ℚ L8 (2 ^ 21 * 5 ^ 10) by simp, Algebra.norm_algebraMap, L8_finrank]
    ring
  rw [count_P1_eq _ hE0, hNQ, padicValRat.mul (by norm_num) (pow_ne_zero _ hN8), padicValRat.pow,
    padicValRat.mul (by norm_num) (by norm_num), padicValRat.pow, padicValRat.pow]
  have h2 : padicValRat 2 (2 : ℚ) = 1 := by exact_mod_cast padicValRat.self (p := 2) (by norm_num)
  have h5 : padicValRat 2 (5 : ℚ) = 0 := by
    rw [show (5 : ℚ) = ((5 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (by decide)]
    rfl
  rw [h2, h5]
  push_cast
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd]
  exact ⟨(33 + 2 * padicValRat 2 (Algebra.norm ℚ (aeval θ ψ))), by ring⟩

end

end X2Y5Z7.Norm
