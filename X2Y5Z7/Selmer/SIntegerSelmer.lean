module

public import X2Y5Z7.Selmer.SUnitSequence
public import Mathlib.RingTheory.DedekindDomain.SInteger

@[expose] public section

/-! # Selmer groups over a localization: `S`-units modulo `n`-th powers and `K(S, n)`

Let `R` be a Dedekind domain with fraction field `K`, and let `A` be the localization of `R` at a
submonoid `M ≤ R⁰` (for instance the ring of S-integers `R[1/d]`). Let `S = invertedPrimes M` be
the set of height-one primes of `R` that meet `M`. The file proves:

* `primeEquiv`: the height-one primes of `A` are in bijection with the height-one primes of `R`
  outside `S`; for `M` the powers of `d`, `S` is the set of primes containing `d`
  (`invertedPrimes_powers`), which is finite when `d ≠ 0` (`invertedPrimes_powers_finite`);
* `valuation_extendPrime`: at a prime outside `S`, the valuations of `K` defined over `R` and
  over `A` agree;
* `selmerGroup_localization_eq`: the Selmer group `K(∅, n)` computed over `A` equals the Selmer
  group `K(S, n)` computed over `R`;
* `unitsModPowersEquivOutsideSelmer`: `Aˣ/(Aˣ)ⁿ ≃* K(S, n)` when the class group of `A` has no
  nontrivial `n`-torsion; the same holds when the class group of `R` is finite without nontrivial
  `n`-torsion (`localizationUnitsModPowersEquivOutsideSelmer`, for the canonical localization
  `canonicalLocalizationUnitsModPowersEquivOutsideSelmer`, and for `A = R[1/d]` with any nonzero
  `d`, `awayUnitsModPowersEquivSelmer`), and for `n = 5` when the class group of `R` has exponent
  two (the `…FifthPowers…OfSquareEqOne` variants);
* `support70_eq`: the height-one primes containing `70 = 2 · 5 · 7` are exactly those containing
  2, 5 or 7; hence `away70UnitsModPowersEquivSelmer`: `R[1/70]ˣ/(R[1/70]ˣ)ⁿ ≃* K(S, n)` for `S` the
  primes above 2, 5 and 7, when `R` has characteristic zero and a finite class group without
  nontrivial `n`-torsion.
-/

noncomputable section
open scoped nonZeroDivisors
open IsDedekindDomain

namespace X2Y5Z7.Selmer.SIntegerSelmer

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (M : Submonoid R) (A : Type*) [CommRing A] [IsDedekindDomain A]
  [Algebra R A] [IsLocalization M A]

/-- The primes removed by localization are exactly those meeting the denominator monoid. -/
def invertedPrimes : Set (HeightOneSpectrum R) :=
  {v | ¬ Disjoint (M : Set R) (v.asIdeal : Set R)}

omit [IsDedekindDomain R] in
/-- Inverting one element removes exactly the primes containing that element. -/
theorem invertedPrimes_powers (d : R) :
    invertedPrimes (Submonoid.powers d) = {v : HeightOneSpectrum R | d ∈ v.asIdeal} := by
  ext v
  simp only [invertedPrimes, Set.mem_ofPred_eq,
    Ideal.disjoint_powers_iff_notMem_of_isPrime, not_not]

/-- The removed primes of a nonzero principal denominator form a finite set. -/
theorem invertedPrimes_powers_finite {d : R} (hd : d ≠ 0) :
    (invertedPrimes (Submonoid.powers d)).Finite := by
  rw [invertedPrimes_powers]
  simpa only [Ideal.dvd_span_singleton] using
    (Ideal.finite_factors
      (show (Ideal.span {d} : Ideal R) ≠ 0 by
        exact Submodule.span_singleton_eq_bot.mp.mt hd))

/-- Extension of a surviving nonzero prime to the localization. -/
def extendPrime (hM : M ≤ R⁰) (v : HeightOneSpectrum R)
    (hv : Disjoint (M : Set R) (v.asIdeal : Set R)) : HeightOneSpectrum A where
  asIdeal := v.asIdeal.map (algebraMap R A)
  isPrime := IsLocalization.isPrime_of_isPrime_disjoint M A v.asIdeal v.isPrime hv
  ne_bot := by
    intro hzero
    have hc := IsLocalization.under_map_of_isPrime_disjoint M A v.isPrime hv
    rw [hzero, Ideal.under, Ideal.comap_bot_of_injective _
      (IsLocalization.injective A hM)] at hc
    exact v.ne_bot hc.symm

/-- Contraction of a nonzero prime from the localization. -/
def contractPrime (hM : M ≤ R⁰) (w : HeightOneSpectrum A) : HeightOneSpectrum R where
  asIdeal := w.asIdeal.under R
  isPrime := (IsLocalization.isPrime_iff_isPrime_disjoint M A w.asIdeal).mp w.isPrime |>.1
  ne_bot := ne_of_gt (IsLocalization.bot_lt_under_prime M A hM w.asIdeal w.ne_bot)

omit [IsDedekindDomain A] in
theorem contractPrime_disjoint (hM : M ≤ R⁰) (w : HeightOneSpectrum A) :
    Disjoint (M : Set R) ((contractPrime M A hM w).asIdeal : Set R) :=
  (IsLocalization.isPrime_iff_isPrime_disjoint M A w.asIdeal).mp w.isPrime |>.2

/-- Localization identifies its height-one spectrum with the surviving primes. -/
def primeEquiv (hM : M ≤ R⁰) :
    HeightOneSpectrum A ≃ {v : HeightOneSpectrum R // v ∉ invertedPrimes M} where
  toFun w := ⟨contractPrime M A hM w, by
    simpa [invertedPrimes] using contractPrime_disjoint M A hM w⟩
  invFun v := extendPrime M A hM v.1 (by simpa [invertedPrimes] using v.2)
  left_inv w := HeightOneSpectrum.ext (IsLocalization.map_under M A w.asIdeal)
  right_inv v := by
    apply Subtype.ext
    apply HeightOneSpectrum.ext
    exact IsLocalization.under_map_of_isPrime_disjoint M A v.1.isPrime
      (by simpa [invertedPrimes] using v.2)

omit [IsDedekindDomain A] in
/-- Powers of surviving primes contract without change. -/
theorem algebraMap_mem_prime_pow_iff (hM : M ≤ R⁰) (v : HeightOneSpectrum R)
    (hv : Disjoint (M : Set R) (v.asIdeal : Set R)) (r : R) (n : ℕ) :
    algebraMap R A r ∈ (extendPrime M A hM v hv).asIdeal ^ n ↔ r ∈ v.asIdeal ^ n := by
  change algebraMap R A r ∈ (v.asIdeal.map (algebraMap R A)) ^ n ↔ _
  rw [← Ideal.map_pow, IsLocalization.algebraMap_mem_map_algebraMap_iff M A]
  constructor
  · rintro ⟨m, hm, hmr⟩
    have hmval : v.intValuation m = 1 := by
      apply (v.intValuation_eq_one_iff_mem_primeCompl m).mpr
      exact Set.disjoint_left.mp hv hm
    rw [← v.intValuation_le_pow_iff_mem, map_mul, hmval, one_mul] at hmr
    exact (v.intValuation_le_pow_iff_mem r n).mp hmr
  · intro hr
    exact ⟨1, M.one_mem, by simpa using hr⟩

/-- Adic valuations of original integral elements are unchanged at surviving primes. -/
theorem intValuation_extendPrime (hM : M ≤ R⁰) (v : HeightOneSpectrum R)
    (hv : Disjoint (M : Set R) (v.asIdeal : Set R)) (r : R) :
    (extendPrime M A hM v hv).intValuation (algebraMap R A r) = v.intValuation r := by
  classical
  by_cases hr : r = 0
  · simp [hr]
  have har : algebraMap R A r ≠ 0 := by simpa using (IsLocalization.injective A hM).ne hr
  have hb (n : ℕ) :
      (extendPrime M A hM v hv).intValuation (algebraMap R A r) ≤ WithZero.exp (-(n : ℤ)) ↔
      v.intValuation r ≤ WithZero.exp (-(n : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem,
      algebraMap_mem_prime_pow_iff M A hM v hv,
      HeightOneSpectrum.intValuation_le_pow_iff_mem]
  rw [HeightOneSpectrum.intValuation_if_neg _ har, v.intValuation_if_neg hr]
  apply congrArg WithZero.exp
  apply congrArg Neg.neg
  apply congrArg (Nat.cast : ℕ → ℤ)
  apply Nat.le_antisymm
  swap
  · have hh := (hb ((Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span {r} : Ideal R)).factors)).mpr (by
          rw [v.intValuation_if_neg hr])
    rw [HeightOneSpectrum.intValuation_if_neg _ har, WithZero.exp_le_exp,
      neg_le_neg_iff, Int.ofNat_le] at hh
    exact hh
  · have hh := (hb ((Associates.mk (extendPrime M A hM v hv).asIdeal).count
        (Associates.mk (Ideal.span {algebraMap R A r} : Ideal A)).factors)).mp (by
          rw [HeightOneSpectrum.intValuation_if_neg _ har])
    rw [v.intValuation_if_neg hr, WithZero.exp_le_exp, neg_le_neg_iff, Int.ofNat_le] at hh
    exact hh

section FractionField

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  [Algebra A K] [IsFractionRing A K] [IsScalarTower R A K]

/-- The normalized adic valuations agree in the common fraction field. -/
theorem valuation_extendPrime (hM : M ≤ R⁰) (v : HeightOneSpectrum R)
    (hv : Disjoint (M : Set R) (v.asIdeal : Set R)) (x : K) :
    (extendPrime M A hM v hv).valuation K x = v.valuation K x := by
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq R⁰ x
  rw [IsFractionRing.mk'_eq_div, map_div₀, map_div₀]
  have hh (a : R) : (extendPrime M A hM v hv).valuation K (algebraMap R K a) =
      v.valuation K (algebraMap R K a) := by
    rw [IsScalarTower.algebraMap_apply R A K]
    rw [HeightOneSpectrum.valuation_of_algebraMap, intValuation_extendPrime M A hM v hv]
    rw [← IsScalarTower.algebraMap_apply R A K, HeightOneSpectrum.valuation_of_algebraMap]
  rw [hh, hh]

/-- The valuations on nonzero elements agree before passage to powers. -/
theorem valuationOfNeZero_extendPrime (hM : M ≤ R⁰) (v : HeightOneSpectrum R)
    (hv : Disjoint (M : Set R) (v.asIdeal : Set R)) (x : Kˣ) :
    (extendPrime M A hM v hv).valuationOfNeZero x = v.valuationOfNeZero x := by
  apply WithZero.coe_injective
  rw [HeightOneSpectrum.valuationOfNeZero_eq, HeightOneSpectrum.valuationOfNeZero_eq,
    valuation_extendPrime M A hM v hv]

/-- The induced valuations modulo powers agree on the identical ambient quotient. -/
theorem valuationOfNeZeroMod_extendPrime (hM : M ≤ R⁰) (v : HeightOneSpectrum R)
    (hv : Disjoint (M : Set R) (v.asIdeal : Set R)) (n : ℕ)
    (x : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) :
    (extendPrime M A hM v hv).valuationOfNeZeroMod n x = v.valuationOfNeZeroMod n x := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  unfold HeightOneSpectrum.valuationOfNeZeroMod
  erw [MonoidHom.comp_apply, QuotientGroup.map_mk, MonoidHom.comp_apply,
    QuotientGroup.map_mk]
  rw [valuationOfNeZero_extendPrime M A hM v hv]

/-- Empty-S Selmer over the localization is exactly outside-S Selmer over the original ring. -/
theorem selmerGroup_localization_eq (hM : M ≤ R⁰) (n : ℕ) :
    (@IsDedekindDomain.selmerGroup A _ _ K _ _ _ ∅ n) =
      (@IsDedekindDomain.selmerGroup R _ _ K _ _ _ (invertedPrimes M) n) := by
  ext x
  change (∀ w : HeightOneSpectrum A, w ∉ ∅ → w.valuationOfNeZeroMod n x = 1) ↔
    (∀ v : HeightOneSpectrum R, v ∉ invertedPrimes M → v.valuationOfNeZeroMod n x = 1)
  constructor
  · intro h v hv
    have hd : Disjoint (M : Set R) (v.asIdeal : Set R) := by
      simpa [invertedPrimes] using hv
    rw [← valuationOfNeZeroMod_extendPrime M A hM v hd n x]
    exact h _ (Set.notMem_empty _)
  · intro h w _
    have hd := contractPrime_disjoint M A hM w
    have he : extendPrime M A hM (contractPrime M A hM w) hd = w :=
      HeightOneSpectrum.ext (IsLocalization.map_under M A w.asIdeal)
    rw [← he, valuationOfNeZeroMod_extendPrime M A hM]
    exact h _ (by simpa [invertedPrimes] using hd)

/-- Units of a localization modulo powers compute the original outside-S Selmer group. -/
def unitsModPowersEquivOutsideSelmer (hM : M ≤ R⁰) {n : ℕ} [Fact (0 < n)]
    (hclass : ∀ c : ClassGroup A, c ^ n = 1 → c = 1) :
    (Aˣ ⧸ (powMonoidHom n : Aˣ →* Aˣ).range) ≃*
      (@IsDedekindDomain.selmerGroup R _ _ K _ _ _ (invertedPrimes M) n) :=
  (SUnitSequence.unitsModPowersEquivSelmer hclass).trans
    (MulEquiv.subgroupCongr (selmerGroup_localization_eq M A hM n))

/-- A finite class group without n-torsion before localization suffices for the n-th power
bridge. -/
def localizationUnitsModPowersEquivOutsideSelmer
    [Module.IsTorsionFree R A] [Finite (ClassGroup R)] (hM : M ≤ R⁰) {n : ℕ} [Fact (0 < n)]
    (hclass : ∀ c : ClassGroup R, c ^ n = 1 → c = 1) :
    (Aˣ ⧸ (powMonoidHom n : Aˣ →* Aˣ).range) ≃*
      (@IsDedekindDomain.selmerGroup R _ _ K _ _ _ (invertedPrimes M) n) :=
  unitsModPowersEquivOutsideSelmer M A hM
    (SUnitSequence.classGroup_localization_no_torsion M A hclass)

/-- An exponent-two class group before localization suffices for the fifth-power bridge. -/
def localizationUnitsModFifthPowersEquivOutsideSelmer
    [Module.IsTorsionFree R A] (hM : M ≤ R⁰)
    (hsquare : ∀ c : ClassGroup R, c ^ 2 = 1) :
    (Aˣ ⧸ (powMonoidHom 5 : Aˣ →* Aˣ).range) ≃*
      (@IsDedekindDomain.selmerGroup R _ _ K _ _ _ (invertedPrimes M) 5) :=
  (SUnitSequence.localizationUnitsModFifthPowersEquivSelmerOfSquareEqOne M A hsquare).trans
    (MulEquiv.subgroupCongr (selmerGroup_localization_eq M A hM 5))

end FractionField

section CanonicalLocalization

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- Canonical localization, including the compatible fraction-field structure, computes Selmer,
when the class group of the original ring is finite without n-torsion. -/
def canonicalLocalizationUnitsModPowersEquivOutsideSelmer [Finite (ClassGroup R)]
    (hM : M ≤ R⁰) {n : ℕ} [Fact (0 < n)] (hclass : ∀ c : ClassGroup R, c ^ n = 1 → c = 1) :
    ((Localization M)ˣ ⧸ (powMonoidHom n : (Localization M)ˣ →* (Localization M)ˣ).range) ≃*
      (@IsDedekindDomain.selmerGroup R _ _ K _ _ _ (invertedPrimes M) n) := by
  letI localizationDomain : IsDomain (Localization M) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization M) hM
  letI localizationDedekind : IsDedekindDomain (Localization M) :=
    IsLocalization.isDedekindDomain R hM (Localization M)
  have hUnits : ∀ y : M, IsUnit (algebraMap R K y) := by
    intro y
    exact isUnit_iff_ne_zero.mpr
      ((IsFractionRing.injective R K).ne (nonZeroDivisors.ne_zero (hM y.2)) |>.trans_eq
        (map_zero (algebraMap R K)))
  letI localizationToField : Algebra (Localization M) K :=
    (IsLocalization.lift hUnits).toAlgebra
  letI localizationTower : IsScalarTower R (Localization M) K :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hUnits x).symm
  letI localizationFraction : IsFractionRing (Localization M) K :=
    IsFractionRing.isFractionRing_of_isLocalization M (Localization M) K hM
  letI localizationTorsionFree : Module.IsTorsionFree R (Localization M) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (IsLocalization.injective (Localization M) hM)
  exact localizationUnitsModPowersEquivOutsideSelmer M (Localization M) hM hclass

/-- Canonical localization, including the compatible fraction-field structure, computes Selmer. -/
def canonicalLocalizationUnitsModFifthPowersEquivOutsideSelmer
    (hM : M ≤ R⁰) (hsquare : ∀ c : ClassGroup R, c ^ 2 = 1) :
    ((Localization M)ˣ ⧸ (powMonoidHom 5 : (Localization M)ˣ →* (Localization M)ˣ).range) ≃*
      (@IsDedekindDomain.selmerGroup R _ _ K _ _ _ (invertedPrimes M) 5) := by
  letI localizationDomain : IsDomain (Localization M) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization M) hM
  letI localizationDedekind : IsDedekindDomain (Localization M) :=
    IsLocalization.isDedekindDomain R hM (Localization M)
  have hUnits : ∀ y : M, IsUnit (algebraMap R K y) := by
    intro y
    exact isUnit_iff_ne_zero.mpr
      ((IsFractionRing.injective R K).ne (nonZeroDivisors.ne_zero (hM y.2)) |>.trans_eq
        (map_zero (algebraMap R K)))
  letI localizationToField : Algebra (Localization M) K :=
    (IsLocalization.lift hUnits).toAlgebra
  letI localizationTower : IsScalarTower R (Localization M) K :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hUnits x).symm
  letI localizationFraction : IsFractionRing (Localization M) K :=
    IsFractionRing.isFractionRing_of_isLocalization M (Localization M) K hM
  letI localizationTorsionFree : Module.IsTorsionFree R (Localization M) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (IsLocalization.injective (Localization M) hM)
  exact localizationUnitsModFifthPowersEquivOutsideSelmer M (Localization M) hM hsquare

/-- Inverting a nonzero denominator gives the expected outside-support n-th power Selmer group,
when the class group of the original ring is finite without n-torsion. -/
def awayUnitsModPowersEquivSelmer [Finite (ClassGroup R)] (d : R) (hd : d ≠ 0)
    {n : ℕ} [Fact (0 < n)] (hclass : ∀ c : ClassGroup R, c ^ n = 1 → c = 1) :
    ((Localization.Away d)ˣ ⧸
      (powMonoidHom n : (Localization.Away d)ˣ →* (Localization.Away d)ˣ).range) ≃*
      (@IsDedekindDomain.selmerGroup R _ _ K _ _ _
        {v : HeightOneSpectrum R | d ∈ v.asIdeal} n) :=
  (canonicalLocalizationUnitsModPowersEquivOutsideSelmer (Submonoid.powers d)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hd) hclass).trans
    (MulEquiv.subgroupCongr (by rw [invertedPrimes_powers]))

/-- Inverting a nonzero denominator gives the expected outside-support fifth Selmer group. -/
def awayUnitsModFifthPowersEquivSelmer (d : R) (hd : d ≠ 0)
    (hsquare : ∀ c : ClassGroup R, c ^ 2 = 1) :
    ((Localization.Away d)ˣ ⧸
      (powMonoidHom 5 : (Localization.Away d)ˣ →* (Localization.Away d)ˣ).range) ≃*
      (@IsDedekindDomain.selmerGroup R _ _ K _ _ _
        {v : HeightOneSpectrum R | d ∈ v.asIdeal} 5) := by
  rw [← invertedPrimes_powers]
  exact canonicalLocalizationUnitsModFifthPowersEquivOutsideSelmer (Submonoid.powers d)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hd) hsquare

omit [IsDedekindDomain R] in
/-- The primes containing 70 = 2 * 5 * 7 are exactly the primes containing 2, 5 or 7. -/
theorem support70_eq :
    {v : HeightOneSpectrum R | (70 : R) ∈ v.asIdeal} =
      {v : HeightOneSpectrum R | (2 : R) ∈ v.asIdeal ∨ (5 : R) ∈ v.asIdeal ∨
        (7 : R) ∈ v.asIdeal} := by
  ext v
  change (70 : R) ∈ v.asIdeal ↔
    (2 : R) ∈ v.asIdeal ∨ (5 : R) ∈ v.asIdeal ∨ (7 : R) ∈ v.asIdeal
  have heq : (70 : R) = 2 * 5 * 7 := by norm_num
  rw [heq, v.isPrime.mul_mem_iff_mem_or_mem, v.isPrime.mul_mem_iff_mem_or_mem, or_assoc]

/-- The denominator 70 produces the outside-{2,5,7} n-th power Selmer equivalence, when the class
group is finite without n-torsion. -/
def away70UnitsModPowersEquivSelmer [CharZero R] [Finite (ClassGroup R)]
    {n : ℕ} [Fact (0 < n)] (hclass : ∀ c : ClassGroup R, c ^ n = 1 → c = 1) :
    ((Localization.Away (70 : R))ˣ ⧸
      (powMonoidHom n : (Localization.Away (70 : R))ˣ →*
        (Localization.Away (70 : R))ˣ).range) ≃*
      (@IsDedekindDomain.selmerGroup R _ _ K _ _ _
        {v : HeightOneSpectrum R | (2 : R) ∈ v.asIdeal ∨ (5 : R) ∈ v.asIdeal ∨
          (7 : R) ∈ v.asIdeal} n) :=
  (awayUnitsModPowersEquivSelmer (70 : R) (by norm_num) hclass).trans
    (MulEquiv.subgroupCongr (by rw [support70_eq]))

end CanonicalLocalization

end X2Y5Z7.Selmer.SIntegerSelmer
