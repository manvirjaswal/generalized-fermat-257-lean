module

public import X2Y5Z7.SUnits.Theorems

@[expose] public section

/-! # Distinctness of the primes `(B_i)`: the general argument (Proposition 6.2(i))

If `(B_i) = (B_j)` then every `x = B_i + c B_j B_m` lies in the prime `(B_i)` of norm `Sp i`, so
`Sp i ∣ N_{L₂₄/ℚ}(x)` (`span_ne_of_norm`). The certificates in `Cert0`–`Cert3` exhibit, for each pair of primes
above `5` or `7`, such an `x` whose norm is prime to `5`, resp. `7`; `x` is written as `ev P / D` (`comb_eq`) and
its norm is computed through `L₈` (`norm_comb`). -/

namespace X2Y5Z7.SUnitPrimes

open Integral SUnits NumberField

noncomputable section

theorem ev_smul_const (k : ℤ) (P : P2) : ev (P2.smul [k] P) = (k : L24) * ev P := by
  simp [ev, P2.eval_smul, P1.eval]

theorem Bden_ne_zero (j : Fin 24) : (Bden j : L24) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  fin_cases j <;> decide

/-- `x = B_i + c B_j B_m` as `ev P / D`, from a certificate identity in `L₂₄`. -/
theorem comb_eq (i j m : Fin 24) (c : ℤ) (P : P2) (D : ℕ) (hD : D ≠ 0)
    (h : ev (P2.smul [((Bden i * Bden j * Bden m : ℕ) : ℤ)] P) =
      ev (P2.add (P2.smul [((D * Bden j * Bden m : ℕ) : ℤ)] (Bnum i))
        (P2.smul [(D : ℤ) * c * Bden i] (P2.mul (Bnum j) (Bnum m))))) :
    ev P / (D : L24) = B i + c * B j * B m := by
  rw [ev_smul_const, ev_add, ev_smul_const, ev_smul_const, ev_mul] at h
  have hi := Bden_ne_zero i
  have hj := Bden_ne_zero j
  have hm := Bden_ne_zero m
  have hD' : (D : L24) ≠ 0 := Nat.cast_ne_zero.mpr hD
  simp only [B]
  push_cast at h
  field_simp
  linear_combination h

theorem norm_comb (i j m : Fin 24) (c : ℤ) (P : P2) (D : ℕ) (hD : D ≠ 0)
    (h : ev (P2.smul [((Bden i * Bden j * Bden m : ℕ) : ℤ)] P) =
      ev (P2.add (P2.smul [((D * Bden j * Bden m : ℕ) : ℤ)] (Bnum i))
        (P2.smul [(D : ℤ) * c * Bden i] (P2.mul (Bnum j) (Bnum m)))))
    (value N : ℤ) (hn : Algebra.norm ℚ (ev P / (D : L24)) = (value : ℚ) / 820 ^ 8) (hN : value = N * 820 ^ 8) :
    Algebra.norm ℤ (Bint i + (c : 𝓞 L24) * Bint j * Bint m) = N := by
  have hx : ((Bint i + (c : 𝓞 L24) * Bint j * Bint m : 𝓞 L24) : L24) = ev P / (D : L24) := by
    rw [comb_eq i j m c P D hD h]
    push_cast
    rfl
  have := Algebra.coe_norm_int (Bint i + (c : 𝓞 L24) * Bint j * Bint m)
  rw [hx, hn, hN] at this
  push_cast at this
  have e : (N : ℚ) * 820 ^ 8 / 820 ^ 8 = N := by field_simp
  exact_mod_cast this.trans e

/-- If `(B_i) = (B_j)` then `Sp i ∣ N(B_i + c B_j B_m)`. -/
theorem span_ne_of_norm (i j m : Fin 24) (c : ℤ)
    (hn : ¬ ((Sp i : ℕ) : ℤ) ∣ Algebra.norm ℤ (Bint i + (c : 𝓞 L24) * Bint j * Bint m)) :
    Ideal.span {Bint i} ≠ Ideal.span {Bint j} := by
  intro h
  apply hn
  have hj : Bint j ∈ Ideal.span {Bint i} := h ▸ Ideal.mem_span_singleton_self _
  have hx : Bint i + (c : 𝓞 L24) * Bint j * Bint m ∈ Ideal.span {Bint i} :=
    Ideal.add_mem _ (Ideal.mem_span_singleton_self _)
      (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hj))
  have hle := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hx)
  rw [absNorm_span_Bint_eq_Sp, Ideal.absNorm_span_singleton] at hle
  exact Int.natCast_dvd.mpr hle

end

end X2Y5Z7.SUnitPrimes
