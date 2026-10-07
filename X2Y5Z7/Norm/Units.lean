module

public import X2Y5Z7.Norm.Local
public import X2Y5Z7.Integral.Basic

@[expose] public section

/-! # The elements `u₁, …, u₁₀` of `L₈` (Table 5 of the paper)

`u_i = D_i⁻¹ ∑ₖ n_{i,k} aᵏ`. The elements `u₁, …, u₆` generate the primes of `L₈` above 2, 5, 5, 5, 7, 7 and
`u₇, …, u₁₀` are units (not used here).

* `zpow_u`: `u_i^e = A/B` with `A, B` integer polynomials in `a` (`facA`, `facB`), so that `∏ u_i^{e_i}` is a quotient
  of two integer polynomials in `a` (`prod_u_zpow`), and an identity `x = s ∏ u_i^{e_i}` follows from an `ev8`
  certificate (`eq_mul_prod_u`), which is how Lemma 6.3(ii) is checked.
* `uCheck`: the computable test of the symbol of `u_i` at a model prime of `L₈` (`sym_u_of_uCheck`). -/

namespace X2Y5Z7.Norm

open NumberField FiniteFields Integral

noncomputable section

/-- The numerators `n_{i,0}, …, n_{i,7}` of Table 5. -/
def un : Fin 10 → P1 := ![
  [-11240, -3930, 11410, 4970, -2840, -1577, -13, 57],
  [144740, 4910, -112770, -20720, 23320, 7193, -443, -218],
  [-151490, -13740, 114790, 24900, -22370, -7289, 414, 219],
  [1109580, -63670, -958820, -114980, 233100, 65447, -4742, -2042],
  [428604, -30740, -362830, -41928, 87380, 24500, -1771, -766],
  [17800, 17460, -14690, -9890, 2430, 1782, 13, -57],
  [-1773690, 126310, 1512960, 175320, -366800, -103292, 7397, 3237],
  [-44757080, 5683670, 36575370, 3213340, -8812930, -2344379, 182619, 73674],
  [-49340, 25970, 28570, -7990, -5860, 363, 257, -23],
  [-744505, -1104185, 1381795, 632240, -360460, -164188, 5128, 5033]]

/-- The denominators `D_i` of Table 5. -/
def ud : Fin 10 → ℕ := ![820, 820, 410, 820, 164, 820, 410, 820, 820, 205]

/-- The elements `u_i = D_i⁻¹ ∑ₖ n_{i,k} aᵏ` of Table 5 (index `i - 1`). -/
def u (i : Fin 10) : L8 := ev8 (un i) / (ud i : L8)

theorem ud_ne_zero (i : Fin 10) : (ud i : L8) ≠ 0 := by
  have : ud i ≠ 0 := by fin_cases i <;> decide
  exact Nat.cast_ne_zero.mpr this

/-! ## Products of powers of the `u_i` -/

/-- `p^n` for an integer polynomial. -/
def powP (p : P1) : ℕ → P1
  | 0 => [1]
  | n + 1 => P1.mul p (powP p n)

theorem ev8_powP (p : P1) : ∀ n : ℕ, ev8 (powP p n) = ev8 p ^ n
  | 0 => by simp [powP, ev8, P1.eval]
  | n + 1 => by rw [powP, ev8_mul, ev8_powP p n, pow_succ, mul_comm]

theorem ev8_smul (c : ℤ) (p : P1) : ev8 (P1.smul c p) = c * ev8 p := P1.eval_smul a c p

/-- The numerator of `u_i^e`. -/
def facA (i : Fin 10) (e : ℤ) : P1 := P1.smul ((ud i : ℤ) ^ (-e).toNat) (powP (un i) e.toNat)

/-- The denominator of `u_i^e`. -/
def facB (i : Fin 10) (e : ℤ) : P1 := P1.smul ((ud i : ℤ) ^ e.toNat) (powP (un i) (-e).toNat)

theorem zpow_u (i : Fin 10) (e : ℤ) : u i ^ e = ev8 (facA i e) / ev8 (facB i e) := by
  simp only [facA, facB, ev8_smul, ev8_powP, Int.cast_pow, Int.cast_natCast]
  rcases Int.eq_nat_or_neg e with ⟨n, rfl | rfl⟩
  · simp [u, div_pow]
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h1 : (-(n : ℤ)).toNat = 0 := by omega
      simp only [h1, neg_neg, Int.toNat_natCast, pow_zero, one_mul, mul_one, zpow_neg, zpow_natCast, u, div_pow,
        inv_div]

/-- The numerator of `∏ u_i^{e_i}`. -/
def numA (e : Fin 10 → ℤ) : P1 := prodList (List.ofFn fun i => facA i (e i))

/-- The denominator of `∏ u_i^{e_i}`. -/
def numB (e : Fin 10 → ℤ) : P1 := prodList (List.ofFn fun i => facB i (e i))

theorem ev8_prodList_ofFn (f : Fin 10 → P1) : ev8 (prodList (List.ofFn f)) = ∏ i, ev8 (f i) := by
  rw [ev8_prodList, List.map_ofFn, List.prod_ofFn]
  rfl

theorem prod_u_zpow (e : Fin 10 → ℤ) : ∏ i, u i ^ e i = ev8 (numA e) / ev8 (numB e) := by
  rw [numA, numB, ev8_prodList_ofFn, ev8_prodList_ofFn, ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl fun i _ => zpow_u i (e i)

theorem numB_ne_zero (hu : ∀ i, ev8 (un i) ≠ 0) (e : Fin 10 → ℤ) : ev8 (numB e) ≠ 0 := by
  rw [numB, ev8_prodList_ofFn]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  simp only [facB, ev8_smul, ev8_powP, Int.cast_pow, Int.cast_natCast]
  exact mul_ne_zero (pow_ne_zero _ (ud_ne_zero i)) (pow_ne_zero _ (hu i))

/-- An identity `x = s ∏ u_i^{e_i}` for `x = p(a)/d`, from the certificate
`p · B - s d · A = k · h` in `ℤ[x]`, where `∏ u_i^{e_i} = A(a)/B(a)`. -/
theorem eq_mul_prod_u (hu : ∀ i, ev8 (un i) ≠ 0) (x : L8) (p : P1) (d : ℕ) (hd : d ≠ 0)
    (hx : x = ev8 p / d) (s : ℤ) (e : Fin 10 → ℤ) (k : P1)
    (hcert : P1.isZero (P1.sub (P1.smul 1 (P1.sub (P1.mul p (numB e)) (P1.smul (s * d) (numA e))))
      (P1.mul k hP1)) = true) :
    x = s * ∏ i, u i ^ e i := by
  have h := ev8_eq_of_cert _ _ k 1 one_ne_zero hcert
  rw [ev8_mul, ev8_smul] at h
  have hB := numB_ne_zero hu e
  have hd' : (d : L8) ≠ 0 := Nat.cast_ne_zero.mpr hd
  rw [prod_u_zpow, hx]
  field_simp
  push_cast at h
  linear_combination h

/-! ## Symbols of the `u_i` at model primes of `L₈` -/

/-- The computable test: `den` is invertible mod `q`, and the symbol of `num(x)/den` in `F_q[x]/(P)` is `s`. -/
def uCheck (q : ℕ) (P : List ℕ) (zeta : ℕ) (num : P1) (den : ℕ) (s : ℕ) : Bool :=
  den * (den ^ (q - 2) % q) % q == 1 &&
    symCheck q P zeta (smulL q (den ^ (q - 2) % q) (evalP1L q (ruleOf q P) [0, 1] num)) s

theorem sym_of_uCheck (D : L8Prime) (num : P1) (den : ℕ) (s : ℕ)
    (h : uCheck D.q D.P D.zeta num den s = true) :
    P1.eval D.x num ≠ 0 ∧ (den : D.K) ≠ 0 ∧ D.sym (P1.eval D.x num / den) = s := by
  simp only [uCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hinv, hs⟩ := h
  obtain ⟨hne, hsym⟩ := D.sym_of_symCheck _ _ hs
  obtain ⟨hd, hdiv⟩ := D.ev_div_natCast (evalP1L D.q (ruleOf D.q D.P) [0, 1] num) _ _ hinv
  rw [← hdiv, D.ev_evalP1L] at hne hsym
  exact ⟨fun h0 => hne (by rw [show D.ev [0, 1] = D.x from rfl, h0, zero_div]), hd, hsym⟩

/-- `p(a)` as an element of the ring of integers. -/
def evO (p : P1) : 𝓞 L8 := P1.eval a8 p

theorem coe_evO (p : P1) : algebraMap (𝓞 L8) L8 (evO p) = ev8 p := by
  rw [evO, ← P1_eval_ringHom]
  rfl

theorem res_evO (D : L8Prime) (p : P1) : D.res (evO p) = P1.eval D.x p := by
  rw [evO, ← P1_eval_ringHom, D.res_a8]

theorem un_ne_zero_of_uCheck (D : L8Prime) (i : Fin 10) (s : ℕ)
    (h : uCheck D.q D.P D.zeta (un i) (ud i) s = true) : ev8 (un i) ≠ 0 := by
  intro h0
  apply (sym_of_uCheck D _ _ _ h).1
  rw [← res_evO, ← map_zero D.res]
  congr 1
  apply IsFractionRing.injective (𝓞 L8) L8
  rw [coe_evO, h0, map_zero]

theorem u_ne_zero (hu : ∀ i, ev8 (un i) ≠ 0) (i : Fin 10) : u i ≠ 0 := div_ne_zero (hu i) (ud_ne_zero i)

/-- `u_i` as a unit, given `n_i(a) ≠ 0`. -/
def uU (hu : ∀ i, ev8 (un i) ≠ 0) (i : Fin 10) : L8ˣ := Units.mk0 (u i) (u_ne_zero hu i)

@[simp] theorem coe_uU (hu : ∀ i, ev8 (un i) ≠ 0) (i : Fin 10) : ((uU hu i : L8ˣ) : L8) = u i := rfl

/-- The symbol of `u_i` at a model prime of `L₈`, from `uCheck`. -/
theorem symL8_u (hu : ∀ i, ev8 (un i) ≠ 0) (D : L8Prime) (i : Fin 10) (s : ℕ)
    (h : uCheck D.q D.P D.zeta (un i) (ud i) s = true) :
    ∃ hmem : uU hu i ∈ unitsL8 D, Multiplicative.toAdd (symL8 D ⟨uU hu i, hmem⟩) = s := by
  obtain ⟨hn, hd, hs⟩ := sym_of_uCheck D _ _ _ h
  have hfrac : ((uU hu i : L8ˣ) : L8) * algebraMap (𝓞 L8) L8 (ud i : 𝓞 L8) = algebraMap (𝓞 L8) L8 (evO (un i)) := by
    rw [coe_uU, u, coe_evO, map_natCast]
    field_simp [ud_ne_zero i]
  have hdO : D.res (ud i : 𝓞 L8) ≠ 0 := by rw [map_natCast]; exact hd
  have hnO : D.res (evO (un i)) ≠ 0 := by rw [res_evO]; exact hn
  obtain ⟨hmem, hres⟩ := mem_unitsK_of_frac D.res (L8res_ker_ne_bot D) _ _ _ hnO hdO hfrac
  refine ⟨hmem, ?_⟩
  rw [symL8_apply, hres, res_evO, map_natCast]
  exact hs

end

end X2Y5Z7.Norm
