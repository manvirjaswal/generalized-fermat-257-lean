import X2Y5Z7.Fields.Basic
import X2Y5Z7.Selmer.SIntegerSelmer
import Mathlib.NumberTheory.NumberField.ClassNumber

/-! # The `S`-integers of `L₂₄` at 2, 5, 7 and the Selmer group `L₂₄(S, 5)`

Let `𝓞 = 𝓞 L₂₄` be the ring of integers of `L₂₄` (`Integers`), let `S` be the set of height-one
primes of `𝓞` above 2, 5 and 7 (`Sprimes`), and let `𝓞_S = 𝓞[1/70]` be the ring of `S`-integers
(`SIntegers`). The file proves:

* `invertedPrimes_eq_Sprimes`: `S` is exactly the set of primes of `𝓞` inverted in `𝓞[1/70]`;
  `Sprimes_finite`: `S` is finite;
* `𝓞_S` is a Dedekind domain (instances `sIntegers_isDomain`, `sIntegers_isDedekindDomain`) with
  fraction field `L₂₄` (instance `sIntegers_isFractionRing`, for the embedding `sIntegerToField`,
  which extends the inclusion `𝓞 → L₂₄`);
* `selmerGroup_localization_eq`: the Selmer group `L₂₄(∅, 5)` computed over `𝓞_S` equals
  `L₂₄(S, 5)` computed over `𝓞`;
* `mem_selmer_iff_outside_counts`: the class of `x ∈ L₂₄ˣ` lies in `L₂₄(S, 5)` if and only if 5
  divides the exponent of every prime `v ∉ S` in the fractional ideal `(x)`;
* `unitsModFifthPowersEquivSelmer`: if the class group of `𝓞` has no nontrivial 5-torsion (for
  instance, if 5 does not divide the class number of `L₂₄`), then `𝓞_Sˣ/(𝓞_Sˣ)⁵ ≃* L₂₄(S, 5)`.

The class-group condition is an explicit hypothesis of the last result, and nothing else is assumed.
-/

namespace X2Y5Z7.Selmer.L24SIntegers

noncomputable section
open scoped NumberField nonZeroDivisors
open IsDedekindDomain

/-- The ring of integers of `L₂₄`. -/
abbrev Integers := 𝓞 L24

/-- The height-one primes of `𝓞 L₂₄` above 2, 5 and 7. -/
def Sprimes : Set (HeightOneSpectrum Integers) :=
  {v | (2 : Integers) ∈ v.asIdeal ∨ (5 : Integers) ∈ v.asIdeal ∨ (7 : Integers) ∈ v.asIdeal}

/-- The ring of `S`-integers `𝓞 L₂₄[1/70]`: denominators supported at 2, 5 and 7 are allowed. -/
abbrev SIntegers := Localization.Away (70 : Integers)

theorem denominator_ne_zero : (70 : Integers) ≠ 0 := by norm_num

theorem denominator_powers_nonzero : Submonoid.powers (70 : Integers) ≤ Integers⁰ :=
  powers_le_nonZeroDivisors_of_noZeroDivisors denominator_ne_zero

/-- The primes inverted in `𝓞 L₂₄[1/70]` are exactly the primes above 2, 5 and 7. -/
theorem invertedPrimes_eq_Sprimes :
    SIntegerSelmer.invertedPrimes (Submonoid.powers (70 : Integers)) = Sprimes := by
  rw [SIntegerSelmer.invertedPrimes_powers, SIntegerSelmer.support70_eq]
  rfl

/-- There are only finitely many primes of `𝓞 L₂₄` above 2, 5 and 7. -/
theorem Sprimes_finite : Sprimes.Finite := by
  rw [← invertedPrimes_eq_Sprimes]
  exact SIntegerSelmer.invertedPrimes_powers_finite denominator_ne_zero

/-- The ring of `S`-integers is a domain. -/
instance sIntegers_isDomain : IsDomain SIntegers :=
  IsLocalization.isDomain_of_le_nonZeroDivisors SIntegers denominator_powers_nonzero

/-- The ring of `S`-integers is a Dedekind domain. -/
instance sIntegers_isDedekindDomain : IsDedekindDomain SIntegers :=
  IsLocalization.isDedekindDomain Integers denominator_powers_nonzero SIntegers

theorem denominator_units (y : Submonoid.powers (70 : Integers)) :
    IsUnit (algebraMap Integers L24 y) := by
  apply isUnit_iff_ne_zero.mpr
  simpa only [map_zero] using (IsFractionRing.injective Integers L24).ne
    (nonZeroDivisors.ne_zero (denominator_powers_nonzero y.2))

/-- The embedding of the `S`-integers in `L₂₄`, extending the inclusion `𝓞 L₂₄ → L₂₄`. -/
def sIntegerToField : SIntegers →+* L24 := IsLocalization.lift denominator_units

instance sIntegers_algebra : Algebra SIntegers L24 := sIntegerToField.toAlgebra

instance sIntegers_isScalarTower : IsScalarTower Integers SIntegers L24 :=
  IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.lift_eq denominator_units x).symm

/-- `L₂₄` is the fraction field of the ring of `S`-integers. -/
instance sIntegers_isFractionRing : IsFractionRing SIntegers L24 :=
  IsFractionRing.isFractionRing_of_isLocalization
    (Submonoid.powers (70 : Integers)) SIntegers L24 denominator_powers_nonzero

/-- Equality of subgroups of `L₂₄ˣ/(L₂₄ˣ)⁵`; it requires no class-group hypothesis. -/
theorem selmerGroup_localization_eq :
    (@IsDedekindDomain.selmerGroup SIntegers _ _ L24 _ _ _ ∅ 5) =
      (@IsDedekindDomain.selmerGroup Integers _ _ L24 _ _ _ Sprimes 5) := by
  rw [← invertedPrimes_eq_Sprimes]
  exact SIntegerSelmer.selmerGroup_localization_eq
    (Submonoid.powers (70 : Integers)) SIntegers denominator_powers_nonzero 5

/-- Membership in `L₂₄(S, 5)` is divisibility by 5 of every prime exponent outside `S`. -/
theorem mem_selmer_iff_outside_counts (x : L24ˣ) :
    (QuotientGroup.mk x ∈
      @IsDedekindDomain.selmerGroup Integers _ _ L24 _ _ _ Sprimes 5) ↔
    ∀ v : HeightOneSpectrum Integers, v ∉ Sprimes →
      (5 : ℤ) ∣ FractionalIdeal.count L24 v
        (FractionalIdeal.spanSingleton Integers⁰ (x : L24)) := by
  change (∀ v : HeightOneSpectrum Integers, v ∉ Sprimes →
    v.valuationOfNeZeroMod 5 (QuotientGroup.mk x) = 1) ↔ _
  simp only [SUnitSequence.valuationOfNeZeroMod_eq_one_iff, Nat.cast_ofNat]

/-- Fifth powers of `S`-units compute `L₂₄(S, 5)`, assuming only that the class group of `𝓞 L₂₄`
has no nontrivial 5-torsion. -/
def unitsModFifthPowersEquivSelmer
    (hclass : ∀ c : ClassGroup Integers, c ^ 5 = 1 → c = 1) :
    (SIntegersˣ ⧸ (powMonoidHom 5 : SIntegersˣ →* SIntegersˣ).range) ≃*
      (@IsDedekindDomain.selmerGroup Integers _ _ L24 _ _ _ Sprimes 5) :=
  letI : Fact (0 < 5) := ⟨by norm_num⟩
  SIntegerSelmer.away70UnitsModPowersEquivSelmer hclass

end

end X2Y5Z7.Selmer.L24SIntegers
