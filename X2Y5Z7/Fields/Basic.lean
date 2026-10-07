import X2Y5Z7.Fields.Frobenius17
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Tactic.ComputeDegree

/-! # The fields `L₈` and `L₂₄` (Section 2 of the paper)

* `h = x⁸ + 4x⁷ - 28x⁶ - 168x⁵ - 140x⁴ + 560x³ + 840x² - 480x - 940` (equation (1.6)); `L8 = ℚ[x]/(h)`, with the
  root `a`. `h` is irreducible because it is irreducible modulo 17 (`Frobenius17.lean`).
* `ψ = 25t³ + 20t² + 14t + 14` (equation (1.2)); it is Eisenstein at 2, and it stays irreducible over `L8`
  because a root in `L8` would generate a cubic subfield of the octic field (Lemma 2.4(c)). `L24 = L8[t]/(ψ)`,
  with the root `b`, is a number field of degree 24. -/

namespace X2Y5Z7

open Polynomial

noncomputable section

/-! ## The polynomials -/

/-- `h` with integer coefficients. -/
def hZ : ℤ[X] := X^8 + 4*X^7 - 28*X^6 - 168*X^5 - 140*X^4 + 560*X^3 + 840*X^2 - 480*X - 940

/-- `ψ` with integer coefficients. -/
def ψZ : ℤ[X] := 25*X^3 + 20*X^2 + 14*X + 14

/-- `h` over `ℚ`. -/
def h : ℚ[X] := hZ.map (Int.castRingHom ℚ)

/-- `ψ` over `ℚ`. -/
def ψ : ℚ[X] := ψZ.map (Int.castRingHom ℚ)

theorem hZ_natDegree : hZ.natDegree = 8 := by unfold hZ; compute_degree!

theorem hZ_monic : hZ.Monic := by unfold hZ; monicity!

theorem ψZ_natDegree : ψZ.natDegree = 3 := by unfold ψZ; compute_degree!

theorem h17_natDegree : h17.natDegree = 8 := by unfold h17; compute_degree!

theorem hZ_map_17 : hZ.map (Int.castRingHom (ZMod 17)) = h17 := by
  simp only [hZ, h17, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_ofNat]
  ring

theorem h17_frob8_family : ∀ m : ℕ, m = Fintype.card (ZMod 17) ^ 8 → h17 ∣ (X : P17) ^ m - X := by
  intro m hm
  rw [ZMod.card] at hm
  subst hm
  exact h17_dvd_frobenius8

theorem h17_frob4_family : ∃ R u v : P17, (∀ m : ℕ, m = Fintype.card (ZMod 17) ^ 4 → h17 ∣ (X : P17) ^ m - R) ∧
    u * h17 + v * (R - X) = 1 := by
  obtain ⟨R, u, v, hR, hb⟩ := h17_coprime_frobenius4
  refine ⟨R, u, v, fun m hm => ?_, hb⟩
  rw [ZMod.card] at hm
  subst hm
  exact hR

theorem h17_irreducible : Irreducible h17 := by
  have : Fact (Nat.Prime 17) := ⟨by decide⟩
  obtain ⟨R, u, v, h4, hb⟩ := h17_frob4_family
  exact irreducible_of_natDegree_eight' h17_natDegree h17_frob8_family R u v h4 hb

theorem hZ_irreducible : Irreducible hZ := by
  have : Fact (Nat.Prime 17) := ⟨by decide⟩
  exact hZ_monic.irreducible_of_irreducible_map (φ := Int.castRingHom (ZMod 17)) hZ
    (by rw [hZ_map_17]; exact h17_irreducible)

theorem h_irreducible : Irreducible h := by
  have := (hZ_monic.isPrimitive.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp hZ_irreducible
  rwa [algebraMap_int_eq] at this

theorem ψZ_coeff : ψZ.coeff 0 = 14 ∧ ψZ.coeff 1 = 14 ∧ ψZ.coeff 2 = 20 ∧ ψZ.coeff 3 = 25 := by
  simp [ψZ, coeff_X_pow, coeff_X]

theorem ψZ_leadingCoeff : ψZ.leadingCoeff = 25 := by
  rw [leadingCoeff, ψZ_natDegree, ψZ_coeff.2.2.2]

theorem ψZ_isEisensteinAt : ψZ.IsEisensteinAt (Ideal.span {(2 : ℤ)}) := by
  obtain ⟨h0, h1, h2, _⟩ := ψZ_coeff
  refine ⟨?_, ?_, ?_⟩
  · rw [Ideal.mem_span_singleton, ψZ_leadingCoeff]; decide
  · intro n hn
    rw [ψZ_natDegree] at hn
    rw [Ideal.mem_span_singleton]
    interval_cases n
    · rw [h0]; decide
    · rw [h1]; decide
    · rw [h2]; decide
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, h0]; decide

theorem ψZ_isPrimitive : ψZ.IsPrimitive := by
  intro r hr
  have h0 := (C_dvd_iff_dvd_coeff r ψZ).mp hr 0
  have h3 := (C_dvd_iff_dvd_coeff r ψZ).mp hr 3
  rw [ψZ_coeff.1] at h0
  rw [ψZ_coeff.2.2.2] at h3
  have h1 : r ∣ 1 := by
    have : (1 : ℤ) = 9 * 14 - 5 * 25 := by norm_num
    rw [this]
    exact dvd_sub (dvd_mul_of_dvd_right h0 9) (dvd_mul_of_dvd_right h3 5)
  exact isUnit_of_dvd_one h1

theorem ψZ_irreducible : Irreducible ψZ :=
  ψZ_isEisensteinAt.irreducible ((Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two)
    ψZ_isPrimitive (by rw [ψZ_natDegree]; norm_num)

theorem ψ_irreducible : Irreducible ψ := by
  have := (ψZ_isPrimitive.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp ψZ_irreducible
  rwa [algebraMap_int_eq] at this

theorem h_natDegree : h.natDegree = 8 := by
  rw [h, natDegree_map_eq_of_injective (RingHom.injective_int _), hZ_natDegree]

theorem ψ_natDegree : ψ.natDegree = 3 := by
  rw [ψ, natDegree_map_eq_of_injective (RingHom.injective_int _), ψZ_natDegree]

/-! ## The field `L₈` -/

instance : Fact (Irreducible h) := ⟨h_irreducible⟩

/-- Putz's octic field `L₈ = ℚ[x]/(h)`. -/
abbrev L8 := AdjoinRoot h

/-- The root `a` of `h`. -/
def a : L8 := AdjoinRoot.root h

theorem h_ne_zero : h ≠ 0 := h_irreducible.ne_zero

instance : FiniteDimensional ℚ L8 := (AdjoinRoot.powerBasis h_ne_zero).finite

instance : NumberField L8 := ⟨⟩

theorem L8_finrank : Module.finrank ℚ L8 = 8 := by
  rw [(AdjoinRoot.powerBasis h_ne_zero).finrank, AdjoinRoot.powerBasis_dim, h_natDegree]

/-! ## The field `L₂₄` -/

/-- `ψ` over `L₈`. -/
def ψL8 : L8[X] := ψ.map (algebraMap ℚ L8)

theorem ψL8_natDegree : ψL8.natDegree = 3 := by
  rw [ψL8, natDegree_map_eq_of_injective (algebraMap ℚ L8).injective, ψ_natDegree]

/-- A root of `ψ` in `L₈` would have a cubic minimal polynomial over `ℚ`, whose degree divides 8. -/
theorem ψL8_no_root (β : L8) : ¬ IsRoot ψL8 β := by
  intro hβ
  have hx : aeval β ψ = 0 := by
    rw [IsRoot, ψL8, eval_map_algebraMap] at hβ
    exact hβ
  have key := minpoly.Irreducible.eq_minpoly ψ_irreducible hx
  have hint : IsIntegral ℚ β := Algebra.IsIntegral.isIntegral β
  have hd := minpoly.degree_dvd hint
  have hψ0 : ψ ≠ 0 := ψ_irreducible.ne_zero
  have hdeg : (minpoly ℚ β).natDegree = 3 := by
    rw [← ψ_natDegree, key, natDegree_C_mul (leadingCoeff_ne_zero.mpr hψ0)]
  rw [hdeg, L8_finrank] at hd
  norm_num at hd

theorem ψL8_irreducible : Irreducible ψL8 :=
  irreducible_of_degree_le_three_of_not_isRoot (by rw [ψL8_natDegree]; decide) ψL8_no_root

instance : Fact (Irreducible ψL8) := ⟨ψL8_irreducible⟩

/-- The field `L₂₄ = L₈(b)` of degree 24. -/
abbrev L24 := AdjoinRoot ψL8

/-- The root `b` of `ψ` in `L₂₄`. -/
def b : L24 := AdjoinRoot.root ψL8

theorem ψL8_ne_zero : ψL8 ≠ 0 := ψL8_irreducible.ne_zero

instance : FiniteDimensional L8 L24 := (AdjoinRoot.powerBasis ψL8_ne_zero).finite

instance : FiniteDimensional ℚ L24 := Module.Finite.trans L8 L24

instance : CharZero L24 := charZero_of_injective_algebraMap (algebraMap ℚ L24).injective

instance : NumberField L24 := ⟨⟩

theorem L24_finrank_over_L8 : Module.finrank L8 L24 = 3 := by
  rw [(AdjoinRoot.powerBasis ψL8_ne_zero).finrank, AdjoinRoot.powerBasis_dim, ψL8_natDegree]

theorem L24_finrank : Module.finrank ℚ L24 = 24 := by
  rw [← Module.finrank_mul_finrank ℚ L8 L24, L8_finrank, L24_finrank_over_L8]

theorem b_root : aeval b ψ = 0 := by
  have h1 : eval₂ (AdjoinRoot.of ψL8) (AdjoinRoot.root ψL8) (ψ.map (algebraMap ℚ L8)) = 0 :=
    AdjoinRoot.eval₂_root ψL8
  rw [eval₂_map] at h1
  rw [aeval_def, b, IsScalarTower.algebraMap_eq ℚ L8 L24]
  exact h1

end

end X2Y5Z7
