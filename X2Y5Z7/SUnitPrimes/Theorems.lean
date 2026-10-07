module

public import X2Y5Z7.SUnitPrimes.Cert0
public import X2Y5Z7.SUnitPrimes.Cert1
public import X2Y5Z7.SUnitPrimes.Cert2
public import X2Y5Z7.SUnitPrimes.Cert3
public import X2Y5Z7.Main.SUnitFacts

@[expose] public section

/-! # Proposition 6.2(i): the primes `(B₁), …, (B₁₂)` are distinct, and `v_{P_i}(B_j) = δ_{ij}`

* `span_Bint_injective`: `(B_i) = (B_j)` with `i, j ≤ 12` implies `i = j`. Primes above different rational
  primes have different norms (`absNorm_span_Bint_eq_Sp`); for the `21 + 6` pairs above `5` and `7` see
  `Cert0`–`Cert3`.
* `count_B`, `cnt_Bu_eq`: for `P_i = (B_i)` (`i ≤ 12`) and every `j`, the exponent of `P_i` in `(B_j)` is `δ_{ij}`
  (Table 2 of the paper). -/

namespace X2Y5Z7.SUnitPrimes

open IsDedekindDomain NumberField
open scoped nonZeroDivisors

/-- The pairs `i < j` of indices of primes above the same rational prime (`5` or `7`). -/
def pairs : List (Fin 24 × Fin 24) :=
  [(1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6),
    (3, 7), (4, 5), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7), (8, 9), (8, 10), (8, 11), (9, 10), (9, 11), (10, 11)]

theorem span_ne_of_mem_pairs : ∀ p ∈ pairs, Ideal.span {Bint p.1} ≠ Ideal.span {Bint p.2} := by
  simp only [pairs, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨span_ne_1_2, span_ne_1_3, span_ne_1_4, span_ne_1_5, span_ne_1_6, span_ne_1_7, span_ne_2_3, span_ne_2_4,
    span_ne_2_5, span_ne_2_6, span_ne_2_7, span_ne_3_4, span_ne_3_5, span_ne_3_6, span_ne_3_7, span_ne_4_5,
    span_ne_4_6, span_ne_4_7, span_ne_5_6, span_ne_5_7, span_ne_6_7, span_ne_8_9, span_ne_8_10, span_ne_8_11,
    span_ne_9_10, span_ne_9_11, span_ne_10_11⟩

theorem mem_pairs : ∀ i j : Fin 24, i < j → j.val < 12 → Sp i = Sp j → (i, j) ∈ pairs := by
  decide +kernel

theorem span_Bint_ne_of_lt {i j : Fin 24} (hij : i < j) (hj : j.val < 12) :
    Ideal.span {Bint i} ≠ Ideal.span {Bint j} := by
  intro h
  have hS : Sp i = Sp j := by rw [← absNorm_span_Bint_eq_Sp, ← absNorm_span_Bint_eq_Sp, h]
  exact span_ne_of_mem_pairs _ (mem_pairs i j hij hj hS) h

/-- **Proposition 6.2(i)**: the prime ideals `(B₁), …, (B₁₂)` are pairwise distinct. -/
theorem span_Bint_injective {i j : Fin 24} (hi : i.val < 12) (hj : j.val < 12)
    (h : Ideal.span {Bint i} = Ideal.span {Bint j}) : i = j := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact absurd h (span_Bint_ne_of_lt hlt hj)
  · exact heq
  · exact absurd h.symm (span_Bint_ne_of_lt hgt hi)

/-- **Proposition 6.2(i)**, valuations: `v_{P_i}(B_j) = δ_{ij}` (in the form used by the Selmer reduction). -/
theorem cnt_Bu_eq (v : HeightOneSpectrum (𝓞 L24)) (i : Fin 24) (hi : i.val < 12)
    (hv : v.asIdeal = Ideal.span {Bint i}) (j : Fin 24) :
    SelmerForm.cnt v (SelmerForm.Bu Main.sUnitFacts j) = if i = j then 1 else 0 := by
  classical
  rw [SelmerForm.cnt_Bu]
  by_cases hij : i = j
  · subst hij
    simp [hv]
  · have hne : v.asIdeal ≠ Ideal.span {Bint j} := by
      intro h
      by_cases hj : j.val < 12
      · exact hij (span_Bint_injective hi hj (hv.symm.trans h))
      · rw [Ideal.span_singleton_eq_top.mpr (Bint_isUnit j (by omega))] at h
        exact v.isPrime.ne_top h
    simp [hij, hne]

/-- **Proposition 6.2(i)**, valuations: the exponent of `P_i = (B_i)` in the principal fractional ideal `(B_j)` is
`δ_{ij}`. -/
theorem count_B (v : HeightOneSpectrum (𝓞 L24)) (i : Fin 24) (hi : i.val < 12)
    (hv : v.asIdeal = Ideal.span {Bint i}) (j : Fin 24) :
    FractionalIdeal.count L24 v (FractionalIdeal.spanSingleton (𝓞 L24)⁰ (B j)) = if i = j then 1 else 0 :=
  cnt_Bu_eq v i hi hv j

end X2Y5Z7.SUnitPrimes
