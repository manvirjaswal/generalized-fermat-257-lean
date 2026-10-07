module

public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.FieldTheory.Minpoly.Field

@[expose] public section

/-! # Degree bounds from power equations in finite fields

If `x ^ n = c ∈ 𝔽_q^×` and `n (q - 1) ∣ q ^ D - 1`, then `x ^ (q ^ D) = x`, so the minimal polynomial of `x` over
`ZMod q` divides `X ^ (q ^ D) - X` and its degree divides `D`. -/

namespace X2Y5Z7.Aux

open Polynomial

variable {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [Finite k] [Algebra (ZMod q) k]

/-- `x ^ (q ^ D) = x` implies that the degree of `x` over `ZMod q` divides `D`. -/
theorem minpoly_natDegree_dvd_of_frobenius (x : k) (D : ℕ) (hx : x ^ q ^ D = x) :
    (minpoly (ZMod q) x).natDegree ∣ D := by
  have hint : IsIntegral (ZMod q) x := IsIntegral.of_finite _ _
  apply (minpoly.irreducible hint).natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
  rw [Nat.card_zmod]
  exact minpoly.dvd _ _ (by simp [hx])

/-- `x ^ q = x` implies that `x` lies in the prime field. -/
theorem mem_range_of_pow_card_eq (x : k) (hx : x ^ q = x) : x ∈ (algebraMap (ZMod q) k).range := by
  have hint : IsIntegral (ZMod q) x := IsIntegral.of_finite _ _
  have h1 := minpoly_natDegree_dvd_of_frobenius x 1 (by rw [pow_one]; exact hx)
  rw [Nat.dvd_one] at h1
  exact minpoly.natDegree_eq_one_iff.mp h1

omit [Finite k] in
/-- If `x ^ n = c` with `c ∈ (ZMod q)ˣ` and `n (q - 1) ∣ q ^ D - 1`, then `x ^ (q ^ D) = x`. -/
theorem pow_card_pow_eq_self_of_pow_eq (x : k) (n D : ℕ) (c : ZMod q) (hc : c ≠ 0)
    (hx : x ^ n = algebraMap (ZMod q) k c) (hdiv : n * (q - 1) ∣ q ^ D - 1) : x ^ q ^ D = x := by
  have hq : 0 < q ^ D := pow_pos (Fact.out : q.Prime).pos D
  have h1 : x ^ (n * (q - 1)) = 1 := by
    rw [pow_mul, hx, ← map_pow, ZMod.pow_card_sub_one_eq_one hc, map_one]
  obtain ⟨t, ht⟩ := hdiv
  have h2 : x ^ (q ^ D - 1) = 1 := by rw [ht, pow_mul, h1, one_pow]
  calc x ^ q ^ D = x ^ (q ^ D - 1 + 1) := by rw [Nat.sub_add_cancel hq]
    _ = x := by rw [pow_succ, h2, one_mul]

/-- **Degree divides.** If `x ^ n = c ∈ (ZMod q)ˣ` and `n (q - 1) ∣ q ^ D - 1`, then `deg_{ZMod q} x ∣ D`. -/
theorem minpoly_natDegree_dvd_of_pow_eq (x : k) (n D : ℕ) (c : ZMod q) (hc : c ≠ 0)
    (hx : x ^ n = algebraMap (ZMod q) k c) (hdiv : n * (q - 1) ∣ q ^ D - 1) :
    (minpoly (ZMod q) x).natDegree ∣ D :=
  minpoly_natDegree_dvd_of_frobenius x D (pow_card_pow_eq_self_of_pow_eq x n D c hc hx hdiv)

end X2Y5Z7.Aux
