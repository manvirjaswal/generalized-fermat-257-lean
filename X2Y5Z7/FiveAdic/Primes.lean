module

public import X2Y5Z7.FiveAdic.Valuation
public import X2Y5Z7.SUnitPrimes.Theorems
public import X2Y5Z7.Descent.Valuations
public import Mathlib.RingTheory.FractionalIdeal.Norm
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

@[expose] public section

/-! # The seven primes of `L₂₄` above 5 (Lemma 2.5, Table 2)

`Q k = (B_{k+2})` for `k = 0, …, 6` are the paper's `P₂, …, P₈` (the `Bint` indices `1, …, 7`). They are distinct
(Proposition 6.2(i), `SUnitPrimes.span_Bint_injective`) and they are all the primes containing 5 (`Sprimes_eq`).

* `prodF` (the product formula): `v₅(N_{L₂₄/ℚ}(x)) = Σ_k ν_{Q k}(x)` for `x ≠ 0`, from the factorization of the
  fractional ideal `(x)` and the multiplicativity of the absolute norm (all `Q k` have norm 5, and the norm of any
  other prime is prime to 5).
* `ν_five`: `ν_{Q k}(5) = e_k` with `e = (2, 1, 2, 2, 10, 5, 2)` (the ramification indices of Table 2): from
  `∏ B_i^{e_i} ∈ 5 𝓞` (`dvd_five`) each `ν_{Q k}(5) ≤ e_k`, and both sides add up to `v₅(N(5)) = 24`.
* `ν_intCast`, `ν_ratCast`: `ν_{Q k}(q) = e_k v₅(q)` for rational `q`. -/

namespace X2Y5Z7.FiveAdic

open IsDedekindDomain NumberField
open scoped nonZeroDivisors

noncomputable section

/-- The `Bint` index of the `k`-th prime above 5. -/
def idx (k : Fin 7) : Fin 24 := ⟨k.val + 1, by omega⟩

theorem idx_lt (k : Fin 7) : (idx k).val < 12 := by simp only [idx]; omega

/-- The primes `P₂, …, P₈` of `L₂₄` above 5 (Table 2). -/
def Q (k : Fin 7) : HeightOneSpectrum (𝓞 L24) where
  asIdeal := Ideal.span {Bint (idx k)}
  isPrime := Bint_span_isPrime _ (idx_lt k)
  ne_bot := Bint_span_ne_bot _

/-- The ramification indices `e(P/5)` of the primes above 5 (Table 2). -/
def eQ : Fin 7 → ℤ := ![2, 1, 2, 2, 10, 5, 2]

theorem Q_asIdeal (k : Fin 7) : (Q k).asIdeal = Ideal.span {Bint (idx k)} := rfl

theorem Q_injective : Function.Injective Q := by
  intro k l h
  have h' : Ideal.span {Bint (idx k)} = Ideal.span {Bint (idx l)} := congrArg HeightOneSpectrum.asIdeal h
  have := SUnitPrimes.span_Bint_injective (idx_lt k) (idx_lt l) h'
  simp only [idx, Fin.mk.injEq] at this
  exact Fin.ext (by omega)

theorem eq_Q_of_asIdeal {v : HeightOneSpectrum (𝓞 L24)} {i : Fin 24} (hi : i.val < 12)
    (hv : v.asIdeal = Ideal.span {Bint i}) (h1 : 1 ≤ i.val) (h7 : i.val ≤ 7) :
    v = Q ⟨i.val - 1, by omega⟩ := by
  apply HeightOneSpectrum.ext
  rw [hv, Q_asIdeal]
  congr 2
  congr 1
  apply Fin.ext
  change i.val = i.val - 1 + 1
  omega

theorem five_mem (k : Fin 7) : (5 : 𝓞 L24) ∈ (Q k).asIdeal := by
  have := Sp_mem (idx k) (idx_lt k)
  rw [Q_asIdeal]
  convert this using 1
  fin_cases k <;> rfl

theorem one_not_mem_of {v : HeightOneSpectrum (𝓞 L24)} {x : 𝓞 L24} (hx : x ∈ v.asIdeal) (hu : IsUnit x) :
    False :=
  v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)

/-- The primes containing 5 are the `Q k`. -/
theorem eq_Q_of_five_mem (v : HeightOneSpectrum (𝓞 L24)) (h5 : (5 : 𝓞 L24) ∈ v.asIdeal) : ∃ k, v = Q k := by
  obtain ⟨i, hi, hv⟩ := Sprimes_eq v (Or.inr (Or.inl (by exact_mod_cast h5)))
  have hSp := Sp_mem i hi
  rw [← hv] at hSp
  have hone : ∀ c : ℕ, c = 2 ∨ c = 7 → (c : 𝓞 L24) ∈ v.asIdeal → False := by
    intro c hc hcm
    have h1 : (1 : 𝓞 L24) ∈ v.asIdeal := by
      rcases hc with rfl | rfl
      · have := v.asIdeal.sub_mem (v.asIdeal.mul_mem_left 3 h5) (v.asIdeal.mul_mem_left 7 hcm)
        convert this using 1; norm_num
      · have := v.asIdeal.sub_mem (v.asIdeal.mul_mem_left 3 h5) (v.asIdeal.mul_mem_left 2 hcm)
        convert this using 1; norm_num
    exact one_not_mem_of h1 isUnit_one
  have h17 : 1 ≤ i.val ∧ i.val ≤ 7 := by
    fin_cases i
    all_goals first
      | exact absurd hi (by decide)
      | exact ⟨by decide, by decide⟩
      | exact (hone 2 (Or.inl rfl) hSp).elim
      | exact (hone 7 (Or.inr rfl) hSp).elim
  exact ⟨_, eq_Q_of_asIdeal hi hv h17.1 h17.2⟩

/-- The exponent of a prime in `(x)` is `ν`. -/
theorem count_eq_ν (v : HeightOneSpectrum (𝓞 L24)) {x : L24} (hx : x ≠ 0) :
    FractionalIdeal.count L24 v (FractionalIdeal.spanSingleton (𝓞 L24)⁰ x) = ν v x :=
  Prop31.count_eq_neg_log v hx

/-- `ν_{Q k}(B_j) = δ` (Proposition 6.2(i)). -/
theorem ν_B (k : Fin 7) (j : Fin 24) : ν (Q k) (B j) = if idx k = j then 1 else 0 := by
  have hB : B j ≠ 0 := by
    intro h0
    have hB0 : Bint j ≠ 0 := fun h => Bint_span_ne_bot j (by rw [h, Ideal.span_singleton_eq_bot])
    exact hB0 (RingOfIntegers.coe_injective (h0.trans (map_zero _).symm))
  rw [← count_eq_ν _ hB]
  exact SUnitPrimes.count_B (Q k) (idx k) (idx_lt k) rfl j

/-! ## Integers and the product formula -/

/-- An integer prime to 5 is not in `Q k`. -/
theorem int_not_mem (k : Fin 7) {m : ℤ} (hm : ¬ (5 : ℤ) ∣ m) : (m : 𝓞 L24) ∉ (Q k).asIdeal := by
  intro hmem
  have hp5 : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr Nat.prime_five
  have hcop : IsCoprime m 5 := (hp5.coprime_iff_not_dvd.mpr hm).symm
  obtain ⟨u, w, huw⟩ := hcop
  have h1 : ((u * m + w * 5 : ℤ) : 𝓞 L24) ∈ (Q k).asIdeal := by
    push_cast
    exact (Q k).asIdeal.add_mem ((Q k).asIdeal.mul_mem_left _ hmem) ((Q k).asIdeal.mul_mem_left _ (five_mem k))
  rw [huw, Int.cast_one] at h1
  exact one_not_mem_of h1 isUnit_one

theorem ν_int_prime_to_five (k : Fin 7) (m : ℤ) (hm : ¬ (5 : ℤ) ∣ m) : ν (Q k) (m : L24) = 0 := by
  have hm0 : (m : L24) ≠ 0 := Int.cast_ne_zero.mpr (by rintro rfl; exact hm (dvd_zero _))
  have h1 := ν_intCast_nonneg (v := Q k) (m : 𝓞 L24)
  have h2 : ¬ 0 < ν (Q k) ((m : 𝓞 L24) : L24) := by
    rw [ν_pos_iff_mem (by simpa using hm0)]
    exact int_not_mem k hm
  simp only [map_intCast] at h1 h2
  omega

/-- If `5` divides the absolute norm of a prime then the prime contains `5`. -/
theorem five_mem_of_dvd_absNorm (v : HeightOneSpectrum (𝓞 L24)) (h : 5 ∣ Ideal.absNorm v.asIdeal) :
    (5 : 𝓞 L24) ∈ v.asIdeal := by
  have hI0 : v.asIdeal ≠ ⊥ := v.ne_bot
  have : Finite (𝓞 L24 ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal hI0
  let _ := Fintype.ofFinite (𝓞 L24 ⧸ v.asIdeal)
  have hc : 5 ∣ Fintype.card (𝓞 L24 ⧸ v.asIdeal) := by
    rw [← Nat.card_eq_fintype_card, show Nat.card (𝓞 L24 ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]]
    exact h
  obtain ⟨z, hz⟩ := exists_prime_addOrderOf_dvd_card 5 hc
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, addOrderOf_zero] at hz
    exact absurd hz (by decide)
  have h5z : (5 : 𝓞 L24 ⧸ v.asIdeal) * z = 0 := by
    have := addOrderOf_nsmul_eq_zero z
    rw [hz, nsmul_eq_mul] at this
    exact_mod_cast this
  have : IsDomain (𝓞 L24 ⧸ v.asIdeal) := Ideal.Quotient.isDomain _
  have h50 : (5 : 𝓞 L24 ⧸ v.asIdeal) = 0 := (mul_eq_zero.mp h5z).resolve_right hz0
  rw [show (5 : 𝓞 L24 ⧸ v.asIdeal) = Ideal.Quotient.mk v.asIdeal 5 from (map_ofNat _ 5).symm] at h50
  exact Ideal.Quotient.eq_zero_iff_mem.mp h50

theorem absNorm_Q (k : Fin 7) : Ideal.absNorm (Q k).asIdeal = 5 := by
  rw [Q_asIdeal, absNorm_span_Bint_eq_Sp]
  fin_cases k <;> rfl

open Classical in
/-- `v₅` of the absolute norm of a prime: `1` at the `Q k` and `0` elsewhere. -/
theorem padicValRat_absNorm (v : HeightOneSpectrum (𝓞 L24)) :
    padicValRat 5 (Ideal.absNorm v.asIdeal : ℚ) = if v ∈ Finset.univ.image Q then 1 else 0 := by
  rw [← padicValRat_of_nat]
  split_ifs with h
  · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp h
    rw [absNorm_Q, padicValNat_self]
    rfl
  · have : ¬ 5 ∣ Ideal.absNorm v.asIdeal := by
      intro h5
      obtain ⟨k, rfl⟩ := eq_Q_of_five_mem v (five_mem_of_dvd_absNorm v h5)
      exact h (Finset.mem_image_of_mem _ (Finset.mem_univ k))
    rw [padicValNat.eq_zero_of_not_dvd this]
    rfl

theorem padicValRat_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat 5 (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat 5 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValRat.mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- **The product formula at 5**: `v₅(N_{L₂₄/ℚ}(x)) = Σ_k ν_{Q k}(x)`. -/
theorem prodF (x : L24) (hx : x ≠ 0) : padicValRat 5 (Algebra.norm ℚ x) = ∑ k : Fin 7, ν (Q k) x := by
  classical
  set I := FractionalIdeal.spanSingleton (𝓞 L24)⁰ x with hIdef
  have hI : I ≠ 0 := by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
  have hfac := FractionalIdeal.finprod_heightOneSpectrum_factorization' L24 hI
  have hfin : {v : HeightOneSpectrum (𝓞 L24) | FractionalIdeal.count L24 v I ≠ 0}.Finite := by
    have := FractionalIdeal.finite_factors (K := L24) I
    rwa [Filter.eventually_cofinite] at this
  set S : Finset (HeightOneSpectrum (𝓞 L24)) := hfin.toFinset ∪ Finset.univ.image Q with hS
  have hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 L24) =>
      (v.asIdeal : FractionalIdeal (𝓞 L24)⁰ L24) ^ FractionalIdeal.count L24 v I) ⊆ (S : Set _) := by
    intro v hv
    rw [Function.mem_mulSupport] at hv
    have : FractionalIdeal.count L24 v I ≠ 0 := by
      intro h0; rw [h0, zpow_zero] at hv; exact hv rfl
    simp only [hS, Finset.coe_union, Set.mem_union, Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
    exact Or.inl this
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub] at hfac
  have hN := congrArg FractionalIdeal.absNorm hfac
  rw [map_prod, hIdef, FractionalIdeal.absNorm_span_singleton] at hN
  simp only [map_zpow₀, FractionalIdeal.coeIdeal_absNorm] at hN
  have hne : ∀ v ∈ S, ((Ideal.absNorm v.asIdeal : ℚ) ^ FractionalIdeal.count L24 v I) ≠ 0 := by
    intro v _
    refine zpow_ne_zero _ (Nat.cast_ne_zero.mpr ?_)
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have hval := congrArg (padicValRat 5) hN
  rw [padicValRat_finset_prod S _ hne] at hval
  have habs : padicValRat 5 |Algebra.norm ℚ x| = padicValRat 5 (Algebra.norm ℚ x) := by
    rcases abs_choice (Algebra.norm ℚ x) with h | h <;> rw [h]
    exact padicValRat.neg _
  rw [habs] at hval
  rw [← hval]
  simp only [padicValRat.zpow, padicValRat_absNorm, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr Finset.subset_union_right,
    Finset.sum_image (fun k _ l _ h => Q_injective h)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hIdef, count_eq_ν _ hx]

/-! ## The ramification indices and the valuations of rational numbers -/

theorem B_ne_zero (j : Fin 24) : B j ≠ 0 := by
  intro h0
  have hB0 : Bint j ≠ 0 := fun h => Bint_span_ne_bot j (by rw [h, Ideal.span_singleton_eq_bot])
  exact hB0 (RingOfIntegers.coe_injective (h0.trans (map_zero _).symm))

theorem ν_list_prod (k : Fin 7) (L : List (Fin 24)) :
    ν (Q k) (L.map B).prod = (L.map fun j => if idx k = j then (1 : ℤ) else 0).sum := by
  induction L with
  | nil => simp [ν_one]
  | cons j L ih =>
    rw [List.map_cons, List.prod_cons, ν_mul (B_ne_zero j)
      (List.prod_ne_zero (by simp only [List.mem_map, not_exists, not_and]; exact fun i _ h => B_ne_zero i h)),
      ih, ν_B, List.map_cons, List.sum_cons]

theorem norm_five : Algebra.norm ℚ (5 : L24) = 5 ^ 24 := by
  rw [show (5 : L24) = algebraMap ℚ L24 5 by simp, Algebra.norm_algebraMap, L24_finrank]

/-- `ν_{Q k}(5) = e_k` (Table 2). -/
theorem ν_five (k : Fin 7) : ν (Q k) (5 : L24) = eQ k := by
  -- upper bounds from `∏ B_i^{e_i} = 5 W`
  have hup : ∀ l : Fin 7, ν (Q l) (5 : L24) ≤ eQ l := by
    intro l
    obtain ⟨W, hW⟩ := dvd_five
    have hW' : ((((List.replicate 5 SUnits.l_q2).flatten ++ SUnits.l_q3 ++
        (List.replicate 2 SUnits.l_q4).flatten).map B).prod : L24) = 5 * (W : L24) := by
      have := congrArg (algebraMap (𝓞 L24) L24) hW
      rw [map_list_prod, List.map_map, map_mul, map_natCast] at this
      exact this
    have hW0 : (W : L24) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hW'
      exact List.prod_ne_zero (by simp only [List.mem_map, not_exists, not_and]; exact fun i _ h => B_ne_zero i h) hW'
    have h := congrArg (ν (Q l)) hW'
    rw [ν_list_prod, ν_mul (by norm_num) hW0] at h
    have hWn := ν_intCast_nonneg (v := Q l) W
    have hs : (((List.replicate 5 SUnits.l_q2).flatten ++ SUnits.l_q3 ++
        (List.replicate 2 SUnits.l_q4).flatten).map fun j => if idx l = j then (1 : ℤ) else 0).sum = eQ l := by
      fin_cases l <;> decide
    rw [hs] at h
    omega
  -- the sum is `v₅(N(5)) = 24`
  have hsum := prodF (5 : L24) (by norm_num)
  rw [norm_five, padicValRat.pow] at hsum
  have h55 : padicValRat 5 (5 : ℚ) = 1 := by exact_mod_cast padicValRat.self (p := 5) (by norm_num)
  rw [h55] at hsum
  have hsumE : ∑ l : Fin 7, eQ l = 24 := by decide
  have h0 : ∑ l : Fin 7, (eQ l - ν (Q l) (5 : L24)) = 0 := by
    rw [Finset.sum_sub_distrib, hsumE, ← hsum]; push_cast
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => sub_nonneg.mpr (hup l))).mp h0 k (Finset.mem_univ k)
  omega

theorem eQ_pos (k : Fin 7) : 0 < eQ k := by fin_cases k <;> decide

/-- `ν_{Q k}(m) = e_k v₅(m)` for a nonzero integer `m`. -/
theorem ν_intCast (k : Fin 7) (m : ℤ) (hm : m ≠ 0) : ν (Q k) (m : L24) = eQ k * padicValInt 5 m := by
  obtain ⟨a, n, hn, hmn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hm) 5 (by norm_num)
  have hn' : ¬ (5 : ℤ) ∣ (n : ℤ) := by exact_mod_cast hn
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero _)
  have habs : ν (Q k) (m.natAbs : L24) = a * eQ k := by
    rw [hmn, Nat.cast_mul, Nat.cast_pow, ν_mul (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr hn0), ν_pow,
      show ((5 : ℕ) : L24) = 5 by norm_num, ν_five, show ((n : ℕ) : L24) = ((n : ℤ) : L24) by norm_cast,
      ν_int_prime_to_five k _ hn']
    ring
  have hval : padicValInt 5 m = a := by
    rw [padicValInt, hmn, padicValNat.mul (pow_ne_zero _ (by norm_num)) hn0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hn]
    simp
  rw [hval]
  rcases Int.natAbs_eq m with h | h
  · rw [h, Int.cast_natCast] at *
    rw [habs]; ring
  · rw [h, Int.cast_neg, Int.cast_natCast, ν_neg, habs]; ring

/-- `ν_{Q k}(q) = e_k v₅(q)` for a nonzero rational `q`. -/
theorem ν_ratCast (k : Fin 7) (q : ℚ) (hq : q ≠ 0) :
    ν (Q k) (algebraMap ℚ L24 q) = eQ k * padicValRat 5 q := by
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hden : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_nz
  rw [eq_ratCast, Rat.cast_def, ν_div (Int.cast_ne_zero.mpr hnum) (by exact_mod_cast q.den_nz),
    ν_intCast k _ hnum, show ((q.den : ℕ) : L24) = ((q.den : ℤ) : L24) by norm_cast, ν_intCast k _ hden,
    padicValRat, padicValInt.of_nat]
  ring

/-- The hypothesis of the local lemmas: integers prime to 5 have `ν = 0` at `Q k`. -/
theorem hZ_Q (k : Fin 7) : ∀ m : ℤ, ¬ (5 : ℤ) ∣ m → ν (Q k) (m : L24) = 0 := ν_int_prime_to_five k

end

end X2Y5Z7.FiveAdic
