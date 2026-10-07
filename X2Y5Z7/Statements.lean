import X2Y5Z7.Main.Paper

/-! # Theorems 1.1 and 1.2 of the paper, as stated there

The objects in the statements:
* `h = x⁸ + 4x⁷ − 28x⁶ − 168x⁵ − 140x⁴ + 560x³ + 840x² − 480x − 940` and `L8 = ℚ[x]/(h)` (equation (1.6)),
  `ψ = 25t³ + 20t² + 14t + 14` and `L24 = L8[t]/(ψ)`, in `X2Y5Z7/Fields/Basic.lean`;
* `fpoly η = 4t⁵ψ(t) − η(4t − 1)`, so that `AdjoinRoot (fpoly η) = ℚ[t]/(f_η) = A_η`, in
  `X2Y5Z7/Descent/Basic.lean`.

A solution of (1.1) is a triple of integers with `X⁵ + Y² = Z⁷`, `gcd(X, Y, Z) = 1` and `XYZ ≠ 0`; then
`η = X⁵/Z⁷`.

The class-group hypothesis `hclass` says that the class group of `𝓞 L24` has no element of order 5. It follows
from Theorem 6.1 of the paper (the class number of `L24` is 1), which is not formalized here. The hypothesis
`hPutz` of Theorem 1.2 is Putz's Theorem 4.33 (Theorem 2.2 of the paper). -/

namespace X2Y5Z7

open NumberField Polynomial

/-- If `gcd(X, Y, Z) = 1` and `X⁵ + Y² = Z⁷`, then `X` and `Z` are coprime. -/
theorem isCoprime_of_gcd {X Y Z : ℤ} (hg : Int.gcd (Int.gcd X Y) Z = 1) (h : X ^ 5 + Y ^ 2 = Z ^ 7) :
    IsCoprime X Z := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hpX : (p : ℤ) ∣ X := (Int.natCast_dvd_natCast.mpr hpd).trans (Int.gcd_dvd_left X Z)
  have hpZ : (p : ℤ) ∣ Z := (Int.natCast_dvd_natCast.mpr hpd).trans (Int.gcd_dvd_right X Z)
  have hpY2 : (p : ℤ) ∣ Y ^ 2 := by
    have : Y ^ 2 = Z ^ 7 - X ^ 5 := by rw [← h]; ring
    rw [this]
    exact dvd_sub (dvd_pow hpZ (by norm_num)) (dvd_pow hpX (by norm_num))
  have hpY : (p : ℤ) ∣ Y := (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hpY2
  have h1 : (p : ℤ) ∣ ((Int.gcd (Int.gcd X Y) Z : ℕ) : ℤ) :=
    Int.dvd_coe_gcd (Int.dvd_coe_gcd hpX hpY) hpZ
  rw [hg, Nat.cast_one] at h1
  exact hp.one_lt.ne' (Int.natCast_dvd_natCast.mp h1 |> Nat.dvd_one.mp)

/-- **Theorem 1.1.** Let `(X, Y, Z)` be a solution of (1.1). Then `A_η` is not isomorphic to `L8`
(assuming that the class group of `L24` has no element of order 5). -/
theorem theorem_1_1 (hclass : ∀ c : ClassGroup (𝓞 L24), c ^ 5 = 1 → c = 1)
    (X Y Z : ℤ) (hX : X ≠ 0) (hY : Y ≠ 0) (hZ : Z ≠ 0) (hg : Int.gcd (Int.gcd X Y) Z = 1)
    (h : X ^ 5 + Y ^ 2 = Z ^ 7) :
    IsEmpty (AdjoinRoot (fpoly ((X : ℚ) ^ 5 / (Z : ℚ) ^ 7)) ≃ₐ[ℚ] L8) :=
  ⟨fun e => Main.false_of_equiv_paper hclass ⟨X, Y, Z, hX, hY, hZ, isCoprime_of_gcd hg h, h⟩ ⟨e⟩⟩

/-- **Theorem 1.2.** Assume that for every solution of (1.1) the algebra `A_η` is isomorphic to `L8`, as
Putz's Theorem 4.33 asserts (and that the class group of `L24` has no element of order 5). Then
`x² + y⁵ = z⁷` has no solution in nonzero coprime integers. -/
theorem theorem_1_2
    (hPutz : ∀ X Y Z : ℤ, X ≠ 0 → Y ≠ 0 → Z ≠ 0 → Int.gcd (Int.gcd X Y) Z = 1 → X ^ 5 + Y ^ 2 = Z ^ 7 →
      Nonempty (AdjoinRoot (fpoly ((X : ℚ) ^ 5 / (Z : ℚ) ^ 7)) ≃ₐ[ℚ] L8))
    (hclass : ∀ c : ClassGroup (𝓞 L24), c ^ 5 = 1 → c = 1)
    (x y z : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hg : Int.gcd (Int.gcd x y) z = 1) :
    x ^ 2 + y ^ 5 ≠ z ^ 7 := by
  intro h
  have hg' : Int.gcd (Int.gcd y x) z = 1 := by rw [Int.gcd_comm y x]; exact hg
  have h' : y ^ 5 + x ^ 2 = z ^ 7 := by rw [← h]; ring
  obtain ⟨e⟩ := hPutz y x z hy hx hz hg' h'
  exact (theorem_1_1 hclass y x z hy hx hz hg' h').false e

theorem gcd3_perm (a b c : ℤ) : Int.gcd (Int.gcd a (-c)) (-b) = Int.gcd (Int.gcd a b) c ∧
    Int.gcd (Int.gcd c (-a)) b = Int.gcd (Int.gcd a b) c := by
  simp only [Int.gcd, Int.natAbs_neg, Int.natAbs_natCast]
  exact ⟨Nat.gcd_right_comm _ _ _, by rw [Nat.gcd_comm c.natAbs]; exact Nat.gcd_right_comm _ _ _⟩

/-- **Theorem 1.2**, the equivalent form `x² + y⁷ = z⁵`. -/
theorem theorem_1_2_257
    (hPutz : ∀ X Y Z : ℤ, X ≠ 0 → Y ≠ 0 → Z ≠ 0 → Int.gcd (Int.gcd X Y) Z = 1 → X ^ 5 + Y ^ 2 = Z ^ 7 →
      Nonempty (AdjoinRoot (fpoly ((X : ℚ) ^ 5 / (Z : ℚ) ^ 7)) ≃ₐ[ℚ] L8))
    (hclass : ∀ c : ClassGroup (𝓞 L24), c ^ 5 = 1 → c = 1)
    (x y z : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hg : Int.gcd (Int.gcd x y) z = 1) :
    x ^ 2 + y ^ 7 ≠ z ^ 5 := by
  intro h
  refine theorem_1_2 hPutz hclass x (-z) (-y) hx (neg_ne_zero.mpr hz) (neg_ne_zero.mpr hy)
    ((gcd3_perm x y z).1.trans hg) ?_
  linear_combination h

/-- **Theorem 1.2**, the equivalent form `x⁵ + y⁷ = z²`. -/
theorem theorem_1_2_572
    (hPutz : ∀ X Y Z : ℤ, X ≠ 0 → Y ≠ 0 → Z ≠ 0 → Int.gcd (Int.gcd X Y) Z = 1 → X ^ 5 + Y ^ 2 = Z ^ 7 →
      Nonempty (AdjoinRoot (fpoly ((X : ℚ) ^ 5 / (Z : ℚ) ^ 7)) ≃ₐ[ℚ] L8))
    (hclass : ∀ c : ClassGroup (𝓞 L24), c ^ 5 = 1 → c = 1)
    (x y z : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hg : Int.gcd (Int.gcd x y) z = 1) :
    x ^ 5 + y ^ 7 ≠ z ^ 2 := by
  intro h
  refine theorem_1_2 hPutz hclass z (-x) y hz (neg_ne_zero.mpr hx) hy ((gcd3_perm x y z).2.trans hg) ?_
  linear_combination -h

end X2Y5Z7
