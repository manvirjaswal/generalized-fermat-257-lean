import X2Y5Z7.Main.PaperRoute
import X2Y5Z7.Main.SUnitFacts
import X2Y5Z7.SUnitPrimes.Theorems

/-! # Valuations of `∏ B_j^{e_j} · z⁵` at the primes `P_i = (B_i)`

Since `v_{P_i}(B_j) = δ_ij` (Proposition 6.2(i)), the exponent of `P_i` in `E = ∏ B_j^{e_j} z⁵` is
`e_i + 5 v_{P_i}(z)`. So the valuations of `E` modulo 5 at the primes above 5 (Proposition 4.2) determine the
coordinates `e_i mod 5` that condition (V) of Theorem 7.1 is about. -/

namespace X2Y5Z7.Main

open NumberField IsDedekindDomain

theorem units_eq_of_form (E : L24ˣ) (e : Fin 24 → ℤ) (z : L24ˣ)
    (hform : (E : L24) = (∏ j, B j ^ e j) * (z : L24) ^ 5) :
    E = (∏ j, SelmerForm.Bu sUnitFacts j ^ e j) * z ^ 5 := by
  apply Units.ext
  have hBu : ∀ j, ((SelmerForm.Bu sUnitFacts j : L24ˣ) : L24) = B j := fun j => Bint_coe j
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_prod, Units.val_zpow_eq_zpow_val, hBu]
  exact hform

theorem cnt_pow_five (v : HeightOneSpectrum (𝓞 L24)) (z : L24ˣ) :
    SelmerForm.cnt v (z ^ 5) = 5 * SelmerForm.cnt v z := by
  simp only [SelmerForm.cnt_eq_neg, map_pow, toAdd_pow, nsmul_eq_mul]
  push_cast; ring

/-- The exponent of `P_i` in `∏ B_j^{e_j} z⁵` is `e_i + 5 v_{P_i}(z)`. -/
theorem cnt_of_form (E : L24ˣ) (e : Fin 24 → ℤ) (z : L24ˣ)
    (hform : (E : L24) = (∏ j, B j ^ e j) * (z : L24) ^ 5)
    (v : HeightOneSpectrum (𝓞 L24)) (i : Fin 24) (hi : i.val < 12) (hv : v.asIdeal = Ideal.span {Bint i}) :
    SelmerForm.cnt v E = e i + 5 * SelmerForm.cnt v z := by
  rw [units_eq_of_form E e z hform, SelmerForm.cnt_mul, SelmerForm.cnt_prod_zpow, cnt_pow_five]
  simp only [SUnitPrimes.cnt_Bu_eq v i hi hv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-- The residue `e_i mod 5` from the valuation of `E` at `P_i`. -/
theorem cast_eq_of_cnt (E : L24ˣ) (e : Fin 24 → ℤ) (z : L24ˣ)
    (hform : (E : L24) = (∏ j, B j ^ e j) * (z : L24) ^ 5)
    (v : HeightOneSpectrum (𝓞 L24)) (i : Fin 24) (hi : i.val < 12) (hv : v.asIdeal = Ideal.span {Bint i})
    (r : ℤ) (h : SelmerForm.cnt v E ≡ r [ZMOD 5]) : (e i : ZMod 5) = r := by
  rw [cnt_of_form E e z hform v i hi hv] at h
  have h' := (ZMod.intCast_eq_intCast_iff _ _ 5).2 h
  push_cast at h'
  rwa [show (5 : ZMod 5) = 0 from rfl, zero_mul, add_zero] at h'

end X2Y5Z7.Main
