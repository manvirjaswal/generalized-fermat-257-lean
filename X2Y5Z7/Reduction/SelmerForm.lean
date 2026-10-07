module

public import X2Y5Z7.Selmer.L24SIntegers

@[expose] public section

/-! # Elements of the Selmer group as products of `S`-units

Let `B₁, …, B₂₄ ∈ 𝓞 L₂₄` be nonzero, with `B₁₃, …, B₂₄` units, `(B₁), …, (B₁₂)` prime ideals above
`2, 5, 7`, and every prime above `2, 5, 7` one of the `(Bᵢ)` (`SUnitFacts`; proved for the paper's
Table 4 in `SUnits/`). If `x ∈ L₂₄ˣ` has exponent divisible by `5` at every prime outside `S` and the class
group of `𝓞 L₂₄` has no element of order `5`, then `x = ∏ Bⱼ^{eⱼ} · u · y⁵` with `u` a unit of `𝓞 L₂₄`
(`selmer_form`).

Proof: divide `x` by `∏ Bᵢ^{eᵢ}`, where `eᵢ` is the exponent of `(Bᵢ)` in `x` when `i` is the first index
with this ideal and `eᵢ = 0` otherwise (so equalities between the ideals `(Bᵢ)` need not be decided). The
quotient has exponent divisible by `5` at every prime, so it is `u · y⁵`
(`Selmer.SUnitSequence.exists_unit_mul_pow_of_counts`). -/

namespace X2Y5Z7.SelmerForm

open IsDedekindDomain FractionalIdeal NumberField Selmer.L24SIntegers
open scoped nonZeroDivisors

noncomputable section

/-- The ring of integers of `L₂₄`. -/
abbrev R := 𝓞 L24

/-- The exponent of the prime `v` in the principal fractional ideal `(x)`. -/
abbrev cnt (v : HeightOneSpectrum R) (x : L24ˣ) : ℤ := count L24 v (spanSingleton R⁰ (x : L24))

theorem cnt_eq_neg (v : HeightOneSpectrum R) (x : L24ˣ) :
    cnt v x = -(v.valuationOfNeZero x).toAdd := by
  rw [Selmer.SUnitSequence.valuationOfNeZero_eq_neg_count, neg_neg]

theorem cnt_mul (v : HeightOneSpectrum R) (x y : L24ˣ) : cnt v (x * y) = cnt v x + cnt v y := by
  simp only [cnt_eq_neg, map_mul, toAdd_mul]; ring

theorem cnt_inv (v : HeightOneSpectrum R) (x : L24ˣ) : cnt v x⁻¹ = -cnt v x := by
  simp only [cnt_eq_neg, map_inv, toAdd_inv]

theorem cnt_prod_zpow (v : HeightOneSpectrum R) (B : Fin 24 → L24ˣ) (e : Fin 24 → ℤ) :
    cnt v (∏ j, B j ^ e j) = ∑ j, e j * cnt v (B j) := by
  simp only [cnt_eq_neg, map_prod, map_zpow, toAdd_prod, toAdd_zpow, smul_eq_mul, mul_neg,
    Finset.sum_neg_distrib]

/-- The facts about the `S`-unit basis used by the reduction. -/
structure SUnitFacts (Bint : Fin 24 → R) : Prop where
  ne_zero : ∀ j, Bint j ≠ 0
  isUnit : ∀ j : Fin 24, 12 ≤ j.val → IsUnit (Bint j)
  isPrime : ∀ i : Fin 24, i.val < 12 → (Ideal.span {Bint i}).IsPrime
  mem_S : ∀ i : Fin 24, i.val < 12 → ∀ v : HeightOneSpectrum R,
    v.asIdeal = Ideal.span {Bint i} → v ∈ Sprimes
  classify : ∀ v ∈ Sprimes, ∃ i : Fin 24, i.val < 12 ∧ v.asIdeal = Ideal.span {Bint i}

variable {Bint : Fin 24 → R} (hB : SUnitFacts Bint)
include hB

theorem algebraMap_ne_zero (j : Fin 24) : algebraMap R L24 (Bint j) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective R L24)).mpr (hB.ne_zero j)

/-- `Bⱼ` as a unit of `L₂₄`. -/
def Bu (j : Fin 24) : L24ˣ := Units.mk0 _ (algebraMap_ne_zero hB j)

/-- The prime `(Bᵢ)` for `i < 12`. -/
def Pv (i : Fin 24) (hi : i.val < 12) : HeightOneSpectrum R where
  asIdeal := Ideal.span {Bint i}
  isPrime := hB.isPrime i hi
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hB.ne_zero i

theorem cnt_Bu (v : HeightOneSpectrum R) (j : Fin 24) [Decidable (v.asIdeal = Ideal.span {Bint j})] :
    cnt v (Bu hB j) = if v.asIdeal = Ideal.span {Bint j} then 1 else 0 := by
  have hcoe : spanSingleton R⁰ ((Bu hB j : L24ˣ) : L24) =
      ((Ideal.span {Bint j} : Ideal R) : FractionalIdeal R⁰ L24) :=
    (coeIdeal_span_singleton (Bint j)).symm
  rw [cnt, hcoe]
  by_cases hj : j.val < 12
  · have hP : Ideal.span {Bint j} = (Pv hB j hj).asIdeal := rfl
    split_ifs with hv
    · have : v = Pv hB j hj := HeightOneSpectrum.ext hv
      rw [hP, ← this, count_self]
    · rw [hP]
      exact count_maximal_coprime L24 v (fun h => hv (by rw [← h]; rfl))
  · have htop : Ideal.span {Bint j} = ⊤ :=
      Ideal.span_singleton_eq_top.mpr (hB.isUnit j (by omega))
    rw [ite_eq_right (by rw [htop]; exact v.isPrime.ne_top), htop, coeIdeal_top, count_one]

/-- **Selmer reduction.** -/
theorem selmer_form (hclass : ∀ c : ClassGroup R, c ^ 5 = 1 → c = 1) (E : L24ˣ)
    (hE : ∀ v : HeightOneSpectrum R, v ∉ Sprimes → (5 : ℤ) ∣ cnt v E) :
    ∃ e : Fin 24 → ℤ, ∃ u : Rˣ, ∃ y : L24ˣ,
      E = (∏ j, Bu hB j ^ e j) * Units.map (algebraMap R L24 : R →* L24) u * y ^ 5 := by
  classical
  let P : Fin 24 → Ideal R := fun i => Ideal.span {Bint i}
  let first : Fin 24 → Prop := fun i => ∀ j < i, P j ≠ P i
  let e : Fin 24 → ℤ := fun i =>
    if h : i.val < 12 ∧ first i then cnt (Pv hB i h.1) E else 0
  let E' := E * (∏ j, Bu hB j ^ e j)⁻¹
  have hcnt : ∀ v, cnt v E' = cnt v E - ∑ j, e j * (if v.asIdeal = P j then 1 else 0) := by
    intro v
    simp only [E', cnt_mul, cnt_inv, cnt_prod_zpow, cnt_Bu hB]
    ring
  have hval : ∀ v : HeightOneSpectrum R, (5 : ℤ) ∣ cnt v E' := by
    intro v
    rw [hcnt]
    by_cases hv : v ∈ Sprimes
    · -- the least index `i*` with `v = (B_{i*})`
      let F := Finset.univ.filter (fun j : Fin 24 => j.val < 12 ∧ v.asIdeal = P j)
      have hF : F.Nonempty := by
        obtain ⟨i, hi, hvi⟩ := hB.classify v hv
        exact ⟨i, by simp [F, hi, hvi, P]⟩
      let i := F.min' hF
      have hiF : i ∈ F := F.min'_mem hF
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hiF
      have hfirst : first i := by
        intro j hj hPj
        have hjF : j ∈ F := by
          simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨by omega, hiF.2.trans hPj.symm⟩
        exact absurd (F.min'_le j hjF) (not_le.mpr hj)
      have hsum : ∑ j, e j * (if v.asIdeal = P j then 1 else 0) = cnt v E := by
        rw [Finset.sum_eq_single i]
        · have hvi : Pv hB i hiF.1 = v := (HeightOneSpectrum.ext hiF.2).symm
          simp only [e, dite_eq_left (And.intro hiF.1 hfirst), ite_eq_left hiF.2, mul_one, hvi]
        · intro j _ hji
          by_cases hvj : v.asIdeal = P j
          · rw [ite_eq_left hvj, mul_one]
            simp only [e]
            rw [dite_eq_right]
            rintro ⟨hj12, hfj⟩
            have hjF : j ∈ F := by
              simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨hj12, hvj⟩
            have hij : i < j := lt_of_le_of_ne (F.min'_le j hjF) (Ne.symm hji)
            exact hfj i hij (hiF.2.symm.trans hvj)
          · rw [ite_eq_right hvj, mul_zero]
        · simp
      rw [hsum, sub_self]
      exact dvd_zero _
    · have hsum : ∑ j, e j * (if v.asIdeal = P j then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        by_cases hvj : v.asIdeal = P j
        · simp only [e]
          rw [dite_eq_right, zero_mul]
          rintro ⟨hj12, -⟩
          exact hv (hB.mem_S j hj12 v hvj)
        · rw [ite_eq_right hvj, mul_zero]
      rw [hsum, sub_zero]
      exact hE v hv
  obtain ⟨u, y, huy⟩ := Selmer.SUnitSequence.exists_unit_mul_pow_of_counts hclass E' hval
  refine ⟨e, u, y, ?_⟩
  have : E = E' * ∏ j, Bu hB j ^ e j := by simp [E']
  rw [this, huy]
  ac_rfl

end

end X2Y5Z7.SelmerForm
