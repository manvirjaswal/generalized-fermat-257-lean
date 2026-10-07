module

public import Mathlib.RingTheory.DedekindDomain.SelmerGroup
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.ClassGroup.ExtendedHom
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.GroupTheory.Index

@[expose] public section

/-! # Units modulo `n`-th powers and the Selmer group `K(∅, n)`

Ideal-theoretic descent from divisible valuations to powers times units.
The ring is any Dedekind domain `R` with fraction field `K`, so it may in particular be a ring of
S-integers. The file proves:

* `exists_unit_mul_pow_of_counts`: if the class group of `R` has no nontrivial `n`-torsion and `n`
  divides the exponent of every prime in the fractional ideal `(x)`, `x ∈ Kˣ`, then `x = u * yⁿ`
  with `u ∈ Rˣ` and `y ∈ Kˣ`;
* `valuationOfNeZeroMod_eq_one_iff`: the Selmer condition at `v` holds exactly when `n` divides
  the exponent of `v` in `(x)`;
* `unitsModPowersEquivSelmer`: without `n`-torsion in the class group,
  `Rˣ/(Rˣ)ⁿ ≃* K(∅, n)` (also under "class number prime to `n`", and for `n = 5` under
  "class group of exponent two");
* for a localization `A` of `R` (section `Localization`): the extension map on class groups is
  surjective (`classGroup_localization_surjective`); so each of these class-group hypotheses on
  `R` passes to `A` (for "no `n`-torsion" this needs the class group of `R` to be finite,
  `classGroup_localization_no_torsion`), and then `Aˣ/(Aˣ)ⁿ ≃* K(∅, n)` over `A`.
-/

noncomputable section
open scoped nonZeroDivisors
open IsDedekindDomain FractionalIdeal

namespace X2Y5Z7.Selmer.SUnitSequence

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Nonzero fractional ideals are determined by their prime exponents. -/
theorem fractionalIdeal_eq_of_counts {I J : FractionalIdeal R⁰ K}
    (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, count K v I = count K v J) : I = J := by
  rw [← finprod_heightOneSpectrum_factorization' K hI,
    ← finprod_heightOneSpectrum_factorization' K hJ]
  exact finprod_congr fun v => congrArg ((v.asIdeal : FractionalIdeal R⁰ K) ^ ·) (h v)

/-- Divisibility of all prime exponents constructs an actual fractional-ideal root. -/
theorem exists_fractionalIdeal_pow_eq {n : ℕ} {I : FractionalIdeal R⁰ K}
    (hI : I ≠ 0) (h : ∀ v : HeightOneSpectrum R, (n : ℤ) ∣ count K v I) :
    ∃ J : FractionalIdeal R⁰ K, J ≠ 0 ∧ J ^ n = I := by
  classical
  let exps : HeightOneSpectrum R → ℤ := fun v => count K v I / (n : ℤ)
  have hfinite : ∀ᶠ v in Filter.cofinite, exps v = 0 :=
    (finite_factors I).mono fun v hv => by simp [exps, hv]
  let J : FractionalIdeal R⁰ K := ∏ᶠ v : HeightOneSpectrum R,
    (v.asIdeal : FractionalIdeal R⁰ K) ^ exps v
  have hJ : J ≠ 0 := finprod_ne_zero fun v =>
    zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)
  refine ⟨J, hJ, fractionalIdeal_eq_of_counts (pow_ne_zero _ hJ) hI ?_⟩
  intro v
  rw [count_pow, count_finprod K v exps hfinite]
  exact Int.mul_ediv_cancel' (h v)

/-- A principal n-th power has principal root if the class group has no n-torsion. -/
theorem fractionalIdeal_principal_of_pow
    {n : ℕ} (hclass : ∀ c : ClassGroup R, c ^ n = 1 → c = 1)
    (J : (FractionalIdeal R⁰ K)ˣ) (x : Kˣ)
    (hpow : J ^ n = toPrincipalIdeal R K x) :
    ∃ y : Kˣ, toPrincipalIdeal R K y = J := by
  have hp : ClassGroup.mk K (toPrincipalIdeal R K x) = 1 := by
    apply ClassGroup.mk_eq_one_iff.mpr
    rw [coe_toPrincipalIdeal]
    exact (FractionalIdeal.isPrincipal_iff _).mpr ⟨(x : K), rfl⟩
  have hj : ClassGroup.mk K J = 1 := hclass _ (by rw [← map_pow, hpow, hp])
  have hprincipal := ClassGroup.mk_eq_one_iff.mp hj
  obtain ⟨y, hy⟩ := (FractionalIdeal.isPrincipal_iff (J : FractionalIdeal R⁰ K)).mp hprincipal
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, spanSingleton_zero] at hy
    exact J.ne_zero hy
  exact ⟨Units.mk0 y hy0, toPrincipalIdeal_eq_iff.mpr hy.symm⟩

/-- The ideal-class obstruction is the only obstruction to a power-times-unit expression. -/
theorem exists_unit_mul_pow_of_counts
    {n : ℕ} (hclass : ∀ c : ClassGroup R, c ^ n = 1 → c = 1)
    (x : Kˣ)
    (hval : ∀ v : HeightOneSpectrum R,
      (n : ℤ) ∣ count K v (spanSingleton R⁰ (x : K))) :
    ∃ (u : Rˣ) (y : Kˣ), x = Units.map (algebraMap R K) u * y ^ n := by
  obtain ⟨J, hJ, hpow⟩ := exists_fractionalIdeal_pow_eq
    (spanSingleton_ne_zero_iff.mpr x.ne_zero) hval
  let Junit : (FractionalIdeal R⁰ K)ˣ := Units.mk0 J hJ
  have hpow' : Junit ^ n = toPrincipalIdeal R K x := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_mk0, coe_toPrincipalIdeal, Junit] using hpow
  obtain ⟨y, hy⟩ := fractionalIdeal_principal_of_pow hclass Junit x hpow'
  have heq : spanSingleton R⁰ ((y : K) ^ n) = spanSingleton R⁰ (x : K) := by
    have hh : toPrincipalIdeal R K (y ^ n) = toPrincipalIdeal R K x := by
      rw [map_pow, hy, hpow']
    simpa only [coe_toPrincipalIdeal, Units.val_pow_eq_pow_val] using congrArg Units.val hh
  obtain ⟨u, hu⟩ := spanSingleton_eq_spanSingleton.mp heq
  refine ⟨u, y, Units.ext ?_⟩
  change (x : K) = algebraMap R K (u : R) * (y : K) ^ n
  simpa only [Units.smul_def, Algebra.smul_def] using hu.symm

/-- Prime-to-n class number is sufficient for the obstruction to vanish. -/
theorem exists_unit_mul_pow_of_classNumber_coprime
    {n : ℕ} (hclass : (Nat.card (ClassGroup R)).Coprime n)
    (x : Kˣ)
    (hval : ∀ v : HeightOneSpectrum R,
      (n : ℤ) ∣ count K v (spanSingleton R⁰ (x : K))) :
    ∃ (u : Rˣ) (y : Kˣ), x = Units.map (algebraMap R K) u * y ^ n := by
  apply exists_unit_mul_pow_of_counts (fun c hc => ?_) x hval
  apply hclass.pow_left_bijective.injective
  simpa using hc

/-- The Selmer valuation convention is the negative of the ideal exponent. -/
theorem valuationOfNeZero_eq_neg_count (v : HeightOneSpectrum R) (x : Kˣ) :
    (v.valuationOfNeZero x).toAdd = -count K v (spanSingleton R⁰ (x : K)) := by
  classical
  let sec := IsLocalization.sec R⁰ (x : K)
  have hx : spanSingleton R⁰ (x : K) =
      spanSingleton R⁰ ((algebraMap R K) (sec.2 : R))⁻¹ *
        ↑(Ideal.span {sec.1} : Ideal R) := by
    rw [coeIdeal_span_singleton, spanSingleton_mul_spanSingleton]
    congr 1
    rw [← IsLocalization.mk'_sec (M := R⁰) K (x : K), IsFractionRing.mk'_eq_div,
      div_eq_mul_inv, mul_comm]
  rw [count_well_defined K v (spanSingleton_ne_zero_iff.mpr x.ne_zero) hx]
  change -(_ : ℤ) - -(_ : ℤ) = -(_ - _)
  dsimp [sec]
  omega

/-- Membership in the valuation kernel is precisely divisibility of the ideal exponent. -/
theorem valuationOfNeZeroMod_eq_one_iff (v : HeightOneSpectrum R) (x : Kˣ) (n : ℕ) :
    v.valuationOfNeZeroMod n (QuotientGroup.mk x) = 1 ↔
      (n : ℤ) ∣ count K v (spanSingleton R⁰ (x : K)) := by
  unfold HeightOneSpectrum.valuationOfNeZeroMod
  erw [MonoidHom.comp_apply, QuotientGroup.map_mk]
  erw [MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  change (v.valuationOfNeZero x).toAdd ∈ AddSubgroup.zmultiples (n : ℤ) ↔ _
  rw [Int.mem_zmultiples_iff, valuationOfNeZero_eq_neg_count, dvd_neg]

/-- Empty-S Selmer classes are represented by ring units when the class obstruction vanishes.
This applies to an S-integer ring itself, with its own height-one spectrum. -/
theorem selmer_fromUnit_surjective {n : ℕ}
    (hclass : ∀ c : ClassGroup R, c ^ n = 1 → c = 1) :
    Function.Surjective (@selmerGroup.fromUnit R _ _ K _ _ _ n) := by
  intro a
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (a :
    Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)
  have hv : ∀ v : HeightOneSpectrum R,
      (n : ℤ) ∣ count K v (spanSingleton R⁰ (x : K)) := by
    intro v
    apply (valuationOfNeZeroMod_eq_one_iff v x n).mp
    rw [hx]
    exact a.property v (Set.notMem_empty v)
  obtain ⟨u, y, hxy⟩ := exists_unit_mul_pow_of_counts hclass x hv
  refine ⟨u, Subtype.ext ?_⟩
  change QuotientGroup.mk (Units.map (algebraMap R K).toMonoidHom u) = _
  rw [← hx, hxy, QuotientGroup.mk_mul]
  have hy : (QuotientGroup.mk (y ^ n) :
      Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨y, rfl⟩
  rw [hy]
  exact (mul_one (QuotientGroup.mk (Units.map (algebraMap R K).toMonoidHom u) :
    Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)).symm

/-- The unit quotient maps onto the empty-S Selmer group. -/
theorem selmer_fromUnitLift_surjective {n : ℕ} [Fact (0 < n)]
    (hclass : ∀ c : ClassGroup R, c ^ n = 1 → c = 1) :
    Function.Surjective (@selmerGroup.fromUnitLift R _ _ K _ _ _ n _) := by
  intro a
  obtain ⟨u, hu⟩ := selmer_fromUnit_surjective hclass a
  refine ⟨QuotientGroup.mk u, ?_⟩
  exact hu

/-- The complete unit/Selmer equivalence under the absence of class-group n-torsion. -/
def unitsModPowersEquivSelmer {n : ℕ} [Fact (0 < n)]
    (hclass : ∀ c : ClassGroup R, c ^ n = 1 → c = 1) :
    (Rˣ ⧸ (powMonoidHom n : Rˣ →* Rˣ).range) ≃*
      (@IsDedekindDomain.selmerGroup R _ _ K _ _ _ ∅ n) :=
  MulEquiv.ofBijective selmerGroup.fromUnitLift
    ⟨selmerGroup.fromUnitLift_injective, selmer_fromUnitLift_surjective hclass⟩

/-- The unit/Selmer equivalence when the class number is prime to the power. -/
def unitsModPowersEquivSelmerOfClassNumberCoprime {n : ℕ} [Fact (0 < n)]
    (hclass : (Nat.card (ClassGroup R)).Coprime n) :
    (Rˣ ⧸ (powMonoidHom n : Rˣ →* Rˣ).range) ≃*
      (@IsDedekindDomain.selmerGroup R _ _ K _ _ _ ∅ n) :=
  unitsModPowersEquivSelmer fun _ hc =>
    hclass.pow_left_bijective.injective (hc.trans (one_pow n).symm)

/-- Exponent dividing two excludes fifth torsion; no exact group cardinal is required. -/
theorem no_fifth_torsion_of_square_eq_one {G : Type*} [Monoid G]
    (hsquare : ∀ c : G, c ^ 2 = 1) (c : G) (hfifth : c ^ 5 = 1) : c = 1 := by
  have h : c ^ 5 = c := by
    calc
      c ^ 5 = (c ^ 2) ^ 2 * c := by simp only [← pow_mul, ← pow_succ]
      _ = c := by rw [hsquare]; simp
  exact h.symm.trans hfifth

/-- A genuine quotient of an exponent-two group also has exponent dividing two. -/
theorem square_eq_one_of_surjective {G H : Type*} [Monoid G] [Monoid H]
    (f : G →* H) (hf : Function.Surjective f) (hsquare : ∀ g : G, g ^ 2 = 1) :
    ∀ h : H, h ^ 2 = 1 := by
  intro h
  obtain ⟨g, rfl⟩ := hf h
  rw [← map_pow, hsquare, map_one]

/-- A quotient of a finite commutative group without `n`-torsion is again without `n`-torsion:
`n`-th powering is injective, hence surjective, on the finite group; it stays surjective on the
quotient, which is finite, so it is injective there too. -/
theorem no_torsion_of_surjective {G H : Type*} [CommGroup G] [Finite G] [Monoid H]
    (f : G →* H) (hf : Function.Surjective f) {n : ℕ}
    (htors : ∀ g : G, g ^ n = 1 → g = 1) :
    ∀ h : H, h ^ n = 1 → h = 1 := by
  have : Finite H := Finite.of_surjective f hf
  have hinjG : Function.Injective fun g : G => g ^ n := by
    intro a b hab
    have hab' : a ^ n = b ^ n := hab
    exact div_eq_one.mp (htors _ (by rw [div_pow, hab', div_self']))
  have hsurjH : Function.Surjective fun h : H => h ^ n := by
    intro h
    obtain ⟨g, rfl⟩ := hf h
    obtain ⟨g', rfl⟩ := Finite.injective_iff_surjective.mp hinjG g
    exact ⟨f g', (map_pow f g' n).symm⟩
  intro h hh
  exact Finite.injective_iff_surjective.mpr hsurjH (hh.trans (one_pow n).symm)

/-- Exponent-two class-group evidence suffices for the fifth-power unit/Selmer equivalence. -/
def unitsModFifthPowersEquivSelmerOfSquareEqOne
    (hsquare : ∀ c : ClassGroup R, c ^ 2 = 1) :
    (Rˣ ⧸ (powMonoidHom 5 : Rˣ →* Rˣ).range) ≃*
      (@IsDedekindDomain.selmerGroup R _ _ K _ _ _ ∅ 5) := by
  letI : Fact (0 < 5) := ⟨by decide⟩
  exact unitsModPowersEquivSelmer (no_fifth_torsion_of_square_eq_one hsquare)

section Localization

variable (M : Submonoid R) (A : Type*) [CommRing A] [IsDedekindDomain A]
  [Algebra R A] [IsLocalization M A] [Module.IsTorsionFree R A]

include M

/-- The actual class-group extension map onto a localization is surjective. -/
theorem classGroup_localization_surjective :
    Function.Surjective (ClassGroup.extendedHom R A) := by
  intro c
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  have hI : I.1.under R ≠ 0 := by
    intro hzero
    have hm := IsLocalization.map_under M A I.1
    rw [hzero, Ideal.zero_eq_bot, Ideal.map_bot] at hm
    exact (mem_nonZeroDivisors_iff_ne_zero.mp I.2) hm.symm
  let J : (Ideal R)⁰ := ⟨I.1.under R, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  refine ⟨ClassGroup.mk0 J, ?_⟩
  rw [ClassGroup.extendedHom_mk0]
  congr 1
  apply Subtype.ext
  exact IsLocalization.map_under M A I.1

/-- Class-number coprimality passes to an actual localization, by the ideal extension map. -/
theorem classNumber_localization_coprime {n : ℕ}
    (hclass : (Nat.card (ClassGroup R)).Coprime n) :
    (Nat.card (ClassGroup A)).Coprime n :=
  Nat.Coprime.of_dvd_left
    (Subgroup.card_dvd_of_surjective (ClassGroup.extendedHom R A)
      (classGroup_localization_surjective M A)) hclass

/-- For a finite class group, the absence of `n`-torsion passes to an actual localization,
by the ideal extension map. -/
theorem classGroup_localization_no_torsion [Finite (ClassGroup R)] {n : ℕ}
    (hclass : ∀ c : ClassGroup R, c ^ n = 1 → c = 1) :
    ∀ c : ClassGroup A, c ^ n = 1 → c = 1 :=
  no_torsion_of_surjective (ClassGroup.extendedHom R A)
    (classGroup_localization_surjective M A) hclass

/-- The Selmer group over a localization is completely represented by its units
when the original class number is prime to n. This covers rings of S-integers. -/
def localizationUnitsModPowersEquivSelmer
    [Algebra A K] [IsFractionRing A K] {n : ℕ} [Fact (0 < n)]
    (hclass : (Nat.card (ClassGroup R)).Coprime n) :
    (Aˣ ⧸ (powMonoidHom n : Aˣ →* Aˣ).range) ≃*
      (@IsDedekindDomain.selmerGroup A _ _ K _ _ _ ∅ n) :=
  unitsModPowersEquivSelmerOfClassNumberCoprime
    (classNumber_localization_coprime M A hclass)

/-- The Selmer group over a localization is completely represented by its units
when the original class group is finite without n-torsion. This covers rings of S-integers
of number fields. -/
def localizationUnitsModPowersEquivSelmerOfNoTorsion
    [Algebra A K] [IsFractionRing A K] [Finite (ClassGroup R)] {n : ℕ} [Fact (0 < n)]
    (hclass : ∀ c : ClassGroup R, c ^ n = 1 → c = 1) :
    (Aˣ ⧸ (powMonoidHom n : Aˣ →* Aˣ).range) ≃*
      (@IsDedekindDomain.selmerGroup A _ _ K _ _ _ ∅ n) :=
  unitsModPowersEquivSelmer (classGroup_localization_no_torsion M A hclass)

/-- The quotient-only exponent-two premise remains sufficient after localization. -/
def localizationUnitsModFifthPowersEquivSelmerOfSquareEqOne
    [Algebra A K] [IsFractionRing A K]
    (hsquare : ∀ c : ClassGroup R, c ^ 2 = 1) :
    (Aˣ ⧸ (powMonoidHom 5 : Aˣ →* Aˣ).range) ≃*
      (@IsDedekindDomain.selmerGroup A _ _ K _ _ _ ∅ 5) :=
  unitsModFifthPowersEquivSelmerOfSquareEqOne
    (square_eq_one_of_surjective (ClassGroup.extendedHom R A)
      (classGroup_localization_surjective M A) hsquare)

end Localization

end X2Y5Z7.Selmer.SUnitSequence
