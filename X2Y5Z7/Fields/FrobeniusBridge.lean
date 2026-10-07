module

public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! # Irreducibility of a degree-8 polynomial over a finite field

`irreducible_of_natDegree_eight`: a polynomial `f` of degree 8 over a finite field with `q` elements is irreducible
if `f ∣ X^(q^8) - X` and `f` is coprime to `X^(q^4) - X`. Both conditions are checked through exact polynomial
identities (`Frobenius17.lean`). -/

namespace X2Y5Z7

open Polynomial

noncomputable section

/-- An irreducible polynomial of degree `d` over a finite field with `q` elements divides `X^(q^n) - X` when
`d ∣ n` (the converse of Mathlib's `Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`). -/
theorem dvd_X_pow_card_pow_sub_X_of_natDegree_dvd {K : Type*} [Field K] [Fintype K] {g : K[X]}
    (hg : Irreducible g) {n : ℕ} (hd : g.natDegree ∣ n) : g ∣ X ^ (Fintype.card K) ^ n - X := by
  have : Fact (Irreducible g) := ⟨hg⟩
  have hg0 : g ≠ 0 := hg.ne_zero
  let pb := AdjoinRoot.powerBasis hg0
  have : Module.Finite K (AdjoinRoot g) := pb.finite
  have : Finite (AdjoinRoot g) := Module.finite_of_finite K
  let _ : Fintype (AdjoinRoot g) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot g) = Fintype.card K ^ g.natDegree := by
    rw [Module.card_eq_pow_finrank (K := K), pb.finrank, AdjoinRoot.powerBasis_dim]
  obtain ⟨m, rfl⟩ := hd
  have hroot : AdjoinRoot.root g ^ (Fintype.card K) ^ (g.natDegree * m) = AdjoinRoot.root g := by
    rw [pow_mul, ← hcard]
    exact FiniteField.pow_card_pow m _
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, hroot, sub_self]

/-- Irreducibility of a degree-8 polynomial from two Frobenius conditions. -/
theorem irreducible_of_natDegree_eight {K : Type*} [Field K] [Fintype K] {f : K[X]}
    (hdeg : f.natDegree = 8) (h8 : f ∣ X ^ (Fintype.card K) ^ 8 - X)
    (R u v : K[X]) (h4 : f ∣ X ^ (Fintype.card K) ^ 4 - R) (hb : u * f + v * (R - X) = 1) :
    Irreducible f := by
  have hpos : 0 < f.natDegree := by omega
  have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt hpos
  obtain ⟨g, hg, hgf⟩ := exists_irreducible_of_natDegree_pos hpos
  have hgdiv : g.natDegree ∣ 8 :=
    hg.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X (by rw [Nat.card_eq_fintype_card]; exact dvd_trans hgf h8)
  by_cases hg8 : g.natDegree = 8
  · exact (associated_of_dvd_of_natDegree_le hgf hf0 (by omega)).irreducible hg
  · have hg4 : g.natDegree ∣ 4 := by
      have hle : g.natDegree ≤ 8 := Nat.le_of_dvd (by norm_num) hgdiv
      interval_cases h : g.natDegree <;> omega
    have hgX : g ∣ X ^ (Fintype.card K) ^ 4 - X := dvd_X_pow_card_pow_sub_X_of_natDegree_dvd hg hg4
    have hgR : g ∣ R - X := by
      have h := dvd_sub hgX (dvd_trans hgf h4)
      rwa [show (X ^ (Fintype.card K) ^ 4 - X) - (X ^ (Fintype.card K) ^ 4 - R) = R - X by ring] at h
    have hg1 : g ∣ 1 := by
      rw [← hb]
      exact dvd_add (dvd_mul_of_dvd_right hgf u) (dvd_mul_of_dvd_right hgR v)
    exact absurd (isUnit_of_dvd_one hg1) hg.not_isUnit

/-- The same criterion with quantified exponents, so that elaboration never unfolds a large power. -/
theorem irreducible_of_natDegree_eight' {K : Type*} [Field K] [Fintype K] {f : K[X]}
    (hdeg : f.natDegree = 8) (h8 : ∀ m : ℕ, m = (Fintype.card K) ^ 8 → f ∣ X ^ m - X)
    (R u v : K[X]) (h4 : ∀ m : ℕ, m = (Fintype.card K) ^ 4 → f ∣ X ^ m - R) (hb : u * f + v * (R - X) = 1) :
    Irreducible f :=
  irreducible_of_natDegree_eight hdeg (h8 _ rfl) R u v (h4 _ rfl) hb

/-! ## The polynomial `h` modulo 17 -/

abbrev P17 := Polynomial (ZMod 17)

/-- `h` reduced modulo 17. -/
def h17 : P17 := X^8 + 4*X^7 + (-28)*X^6 + (-168)*X^5 + (-140)*X^4 + 560*X^3 + 840*X^2 + (-480)*X + (-940)

theorem char17 : (17 : P17) = 0 := by
  change Polynomial.C (17 : ZMod 17) = 0
  rw [show (17 : ZMod 17) = 0 from by decide]
  exact Polynomial.C_0

/-- One squaring step of a Frobenius certificate. -/
theorem certificate_step (f r s q : P17) (n b : ℕ) (h : f ∣ X ^ n - r) (hc : r ^ 2 * X ^ b - s = f * q) :
    f ∣ X ^ (n * 2 + b) - s := by
  have hpow : f ∣ (X ^ n) ^ 2 - r ^ 2 := dvd_trans h (sub_dvd_pow_sub_pow _ _ 2)
  have hm : f ∣ ((X ^ n) ^ 2 - r ^ 2) * X ^ b := dvd_mul_of_dvd_left hpow _
  have hcert : f ∣ r ^ 2 * X ^ b - s := ⟨q, hc⟩
  have ht := dvd_add hm hcert
  convert ht using 1
  ring

/-- The last step moves the exponent to its closed form without unfolding the huge power. -/
theorem certificate_finish (f r : P17) (n m : ℕ) (he : n = m) (hr : r = X) (h : f ∣ X ^ m - r) :
    f ∣ X ^ n - X := by
  subst m
  subst r
  exact h

end

end X2Y5Z7
