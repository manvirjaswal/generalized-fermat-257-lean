import X2Y5Z7.SUnits.Collect
import X2Y5Z7.SUnits.ClassData
import X2Y5Z7.Selmer.L24SIntegers
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.NumberTheory.NumberField.Norm

/-! # The `S`-unit basis `B₁, …, B₂₄` of `L₂₄` (Table 4 of the paper)

* `B_isIntegral`, `B_norm` (`Collect.lean`): the `B_j` are algebraic integers with
  `N_{L₂₄/ℚ}(B_j) = -2, 5 (×7), -7 (×4), 1 (×12)`.
* `Bint_isUnit`: `B₁₃, …, B₂₄` are units; `Bint_span_isPrime`: `B₁, …, B₁₂` generate prime ideals (of prime
  norm `Sp i`), and `Sp i ∈ (B_i)` (`Sp_mem`).
* `Sprimes_eq`: every prime of `𝓞 L₂₄` above 2, 5 or 7 is one of the twelve `(B_i)`. For `p ∈ {2, 5, 7}` we show that
  `∏ B_i^{e(P_i/p)} ∈ p 𝓞` (`dvd_two`, `dvd_five`, `dvd_seven`), through the primes `q` of `L₈`:
  `∏_{P_i ∣ q} B_i^{e(P_i/q)} = Y_q · n_q` with `Y_q` integral and `∏_q n_q^{e(q/p)} = p · Z_p` with `Z_p` integral
  (`ClassData.lean`); a prime containing `p` then contains some `B_i`, and `(B_i)` is maximal. -/

namespace X2Y5Z7

open Integral SUnits NumberField

noncomputable section

/-- `B_j` as an element of the ring of integers. -/
def Bint (j : Fin 24) : 𝓞 L24 := ⟨B j, B_isIntegral j⟩

/-- The norms `N(B_j)`. -/
def Bnorm : Fin 24 → ℤ := ![-2, 5, 5, 5, 5, 5, 5, 5, -7, -7, -7, -7, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem Bint_norm (j : Fin 24) : Algebra.norm ℤ (Bint j) = Bnorm j := by
  have h := B_norm j
  rw [← show ((Bint j : 𝓞 L24) : L24) = B j from rfl, ← Algebra.coe_norm_int] at h
  have e : ((Bnorm j : ℤ) : ℚ) = ![-2, 5, 5, 5, 5, 5, 5, 5, -7, -7, -7, -7, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] j := by
    fin_cases j <;> simp [Bnorm]
  exact_mod_cast h.trans e.symm

theorem absNorm_span_Bint (j : Fin 24) : Ideal.absNorm (Ideal.span {Bint j}) = (Bnorm j).natAbs := by
  rw [Ideal.absNorm_span_singleton, Bint_norm]

theorem Bint_isUnit (j : Fin 24) (hj : 12 ≤ j.val) : IsUnit (Bint j) := by
  rw [← Ideal.span_singleton_eq_top, ← Ideal.absNorm_eq_one_iff, absNorm_span_Bint]
  fin_cases j <;> simp_all [Bnorm]

/-- The rational prime below `(B_i)` for `i < 12` (and `1` for the units). -/
def Sp : Fin 24 → ℕ := ![2, 5, 5, 5, 5, 5, 5, 5, 7, 7, 7, 7, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem absNorm_span_Bint_eq_Sp (i : Fin 24) : Ideal.absNorm (Ideal.span {Bint i}) = Sp i := by
  rw [absNorm_span_Bint]
  fin_cases i <;> rfl

theorem Bint_span_isPrime (i : Fin 24) (hi : i.val < 12) : (Ideal.span {Bint i}).IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [absNorm_span_Bint_eq_Sp, Nat.irreducible_iff_nat_prime]
  fin_cases i <;> first | exact Nat.prime_two | exact Nat.prime_five | exact (by decide : Nat.Prime 7) |
    (exfalso; simp at hi)

theorem Bint_span_ne_bot (i : Fin 24) : Ideal.span {Bint i} ≠ ⊥ := by
  intro h
  have := congrArg Ideal.absNorm h
  rw [absNorm_span_Bint, Ideal.absNorm_bot] at this
  fin_cases i <;> simp [Bnorm] at this

theorem Sp_mem (i : Fin 24) (_hi : i.val < 12) : (Sp i : 𝓞 L24) ∈ Ideal.span {Bint i} := by
  rw [← absNorm_span_Bint_eq_Sp]
  exact Ideal.absNorm_mem _

/-! ## Primes above 2, 5 and 7 -/

theorem exists_mem_of_prod_mem (v : Ideal (𝓞 L24)) (hv : v.IsPrime) :
    ∀ L : List (Fin 24), (L.map Bint).prod ∈ v → ∃ i ∈ L, Bint i ∈ v
  | [], h => absurd ((Ideal.eq_top_iff_one v).mpr (by simpa using h)) hv.ne_top
  | i :: L, h => by
    rw [List.map_cons, List.prod_cons] at h
    rcases hv.mem_or_mem h with h1 | h2
    · exact ⟨i, List.mem_cons_self, h1⟩
    · obtain ⟨k, hk, hk'⟩ := exists_mem_of_prod_mem v hv L h2
      exact ⟨k, List.mem_cons_of_mem _ hk, hk'⟩

theorem dvd_of_eq (L : List (Fin 24)) (p : ℕ) (w : L24) (hw : IsIntegral ℤ w) (h : (L.map B).prod = p * w) :
    ∃ W : 𝓞 L24, (L.map Bint).prod = p * W := by
  obtain ⟨W, hW⟩ : ∃ W : 𝓞 L24, algebraMap (𝓞 L24) L24 W = w := ⟨⟨w, hw⟩, rfl⟩
  refine ⟨W, ?_⟩
  apply RingOfIntegers.coe_injective
  rw [map_list_prod, map_mul, map_natCast, List.map_map, hW]
  exact h

/-- `Y_q`: integral elements of `L₂₄` with `Y_q · n_q = ∏_{P_i ∣ q} B_i^{e(P_i/q)}`. -/
def Yq (Ynum : P2) (Yden : ℕ) : L24 := ev Ynum / (Yden : L24)

/-- `n_a = N_{L₂₄/L₈}(B_a)`. -/
def nq (v : Fin 8 → ℤ) : L24 := algebraMap L8 L24 (evF v / 820)

/-- `Z_p = ∑ z_k ω_k`. -/
def Zp (z : List ℤ) : L24 := algebraMap L8 L24 (ev8 (wsum z Wω) / 820)

theorem Zp_isIntegral (z : List ℤ) : IsIntegral ℤ (Zp z) :=
  (isIntegral_wsum z Wω ω_isIntegral).map (IsScalarTower.toAlgHom ℤ L8 L24)

theorem Zrel' (p : ℕ) (z : List ℤ) (vs : List (Fin 8 → ℤ)) (hvs : vs ≠ [])
    (h : ev8 (P1.smul (p * 820 ^ (vs.length - 1)) (wsum z Wω)) = ev8 (prodList (vs.map List.ofFn))) :
    (p : L24) * Zp z = (vs.map nq).prod := by
  have := congrArg (algebraMap L8 L24) (Zrel p z vs hvs h)
  rw [map_mul, map_natCast, map_list_prod, List.map_map] at this
  exact this

theorem dvd_two : ∃ W : 𝓞 L24, ((List.replicate 8 l_q1).flatten.map Bint).prod = (2 : ℕ) * W := by
  have hY := Yrel Ynum_q1 Yden_q1 (by decide) v_0 l_q1 relY_q1
  have hZ := Zrel' 2 z_2 vs_2 (by simp [vs_2]) relZ_2
  refine dvd_of_eq _ 2 (Yq Ynum_q1 Yden_q1 ^ 8 * Zp z_2) ((isIntegral_q1.pow 8).mul (Zp_isIntegral _)) ?_
  simp only [vs_2, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil] at hZ
  rw [List.map_flatten, List.map_replicate, List.prod_flatten, List.map_replicate, List.prod_replicate, ← hY]
  simp only [Yq, nq] at hZ ⊢
  linear_combination (ev Ynum_q1 / (Yden_q1 : L24)) ^ 8 * hZ.symm

theorem dvd_five : ∃ W : 𝓞 L24, (((List.replicate 5 l_q2).flatten ++ l_q3 ++ (List.replicate 2 l_q4).flatten).map
    Bint).prod = (5 : ℕ) * W := by
  have hY2 := Yrel Ynum_q2 Yden_q2 (by decide) v_5 l_q2 relY_q2
  have hY3 := Yrel Ynum_q3 Yden_q3 (by decide) v_2 l_q3 relY_q3
  have hY4 := Yrel Ynum_q4 Yden_q4 (by decide) v_1 l_q4 relY_q4
  have hZ := Zrel' 5 z_5 vs_5 (by simp [vs_5]) relZ_5
  refine dvd_of_eq _ 5 (Yq Ynum_q2 Yden_q2 ^ 5 * Yq Ynum_q3 Yden_q3 * Yq Ynum_q4 Yden_q4 ^ 2 * Zp z_5)
    ((((isIntegral_q2.pow 5).mul isIntegral_q3).mul (isIntegral_q4.pow 2)).mul (Zp_isIntegral _)) ?_
  simp only [vs_5, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil] at hZ
  simp only [List.map_append, List.prod_append, List.map_flatten, List.map_replicate, List.prod_flatten,
    List.prod_replicate]
  rw [← hY2, ← hY3, ← hY4]
  simp only [Yq, nq] at hZ ⊢
  linear_combination (ev Ynum_q2 / (Yden_q2 : L24)) ^ 5 * (ev Ynum_q3 / (Yden_q3 : L24)) *
    (ev Ynum_q4 / (Yden_q4 : L24)) ^ 2 * hZ.symm

theorem dvd_seven : ∃ W : 𝓞 L24, ((l_q5 ++ (List.replicate 7 l_q6).flatten).map Bint).prod = (7 : ℕ) * W := by
  have hY5 := Yrel Ynum_q5 Yden_q5 (by decide) v_8 l_q5 relY_q5
  have hY6 := Yrel Ynum_q6 Yden_q6 (by decide) v_9 l_q6 relY_q6
  have hZ := Zrel' 7 z_7 vs_7 (by simp [vs_7]) relZ_7
  refine dvd_of_eq _ 7 (Yq Ynum_q5 Yden_q5 * Yq Ynum_q6 Yden_q6 ^ 7 * Zp z_7)
    ((isIntegral_q5.mul (isIntegral_q6.pow 7)).mul (Zp_isIntegral _)) ?_
  simp only [vs_7, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil] at hZ
  simp only [List.map_append, List.prod_append, List.map_flatten, List.map_replicate, List.prod_flatten,
    List.prod_replicate]
  rw [← hY5, ← hY6]
  simp only [Yq, nq] at hZ ⊢
  linear_combination (ev Ynum_q5 / (Yden_q5 : L24)) * (ev Ynum_q6 / (Yden_q6 : L24)) ^ 7 * hZ.symm

theorem eq_span_of_mem (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L24)) (i : Fin 24) (hi : i.val < 12)
    (h : Bint i ∈ v.asIdeal) : v.asIdeal = Ideal.span {Bint i} := by
  have hmax := (Bint_span_isPrime i hi).isMaximal_of_ne_bot (Bint_span_ne_bot i)
  refine (hmax.eq_of_le v.isPrime.ne_top ?_).symm
  rwa [Ideal.span_singleton_le_iff_mem]

theorem exists_of_dvd (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L24)) (p : ℕ) (L : List (Fin 24))
    (hL : ∀ i ∈ L, i.val < 12) (hd : ∃ W : 𝓞 L24, (L.map Bint).prod = p * W) (hp : (p : 𝓞 L24) ∈ v.asIdeal) :
    ∃ i : Fin 24, i.val < 12 ∧ v.asIdeal = Ideal.span {Bint i} := by
  obtain ⟨W, hW⟩ := hd
  have hm : (L.map Bint).prod ∈ v.asIdeal := hW ▸ v.asIdeal.mul_mem_right W hp
  obtain ⟨i, hiL, hi⟩ := exists_mem_of_prod_mem v.asIdeal v.isPrime L hm
  exact ⟨i, hL i hiL, eq_span_of_mem v i (hL i hiL) hi⟩

theorem Sprimes_eq (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L24)) (hv : v ∈ Selmer.L24SIntegers.Sprimes) :
    ∃ i : Fin 24, i.val < 12 ∧ v.asIdeal = Ideal.span {Bint i} := by
  rcases hv with h | h | h
  · exact exists_of_dvd v 2 _ (by decide) dvd_two (by exact_mod_cast h)
  · exact exists_of_dvd v 5 _ (by decide) dvd_five (by exact_mod_cast h)
  · exact exists_of_dvd v 7 _ (by decide) dvd_seven (by exact_mod_cast h)

end

end X2Y5Z7
