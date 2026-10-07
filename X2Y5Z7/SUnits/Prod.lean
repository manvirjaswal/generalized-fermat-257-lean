import X2Y5Z7.Integral.Basic
import X2Y5Z7.SUnits.Data

/-! # Products of the `B_j` as integer polynomials

`Bnumprod l` and `Bdenprod l` are the numerator and denominator of `∏_{i ∈ l} B_i`. The lemmas `Yrel` and `Zrel`
turn the kernel-checked certificates of `ClassData.lean` into identities in `L₂₄` and `L₈`. -/

namespace X2Y5Z7.SUnits

open Integral

noncomputable section

/-- The numerator `∏_{i ∈ l} Bnum i` of a product of `B_i`. -/
def Bnumprod (l : List (Fin 24)) : P2 := (l.map Bnum).foldr P2.mul [[1]]

/-- The denominator `∏_{i ∈ l} Bden i`. -/
def Bdenprod (l : List (Fin 24)) : ℤ := (l.map fun i => (Bden i : ℤ)).prod

theorem Bden_ne_zero (i : Fin 24) : (Bden i : L24) ≠ 0 := by
  have : Bden i ≠ 0 := by fin_cases i <;> decide
  exact Nat.cast_ne_zero.mpr this

theorem prod_B (l : List (Fin 24)) :
    (l.map B).prod = ev (Bnumprod l) / (Bdenprod l : L24) := by
  induction l with
  | nil => simp [Bnumprod, Bdenprod, ev, P2.eval, P1.eval]
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, ih, Bnumprod, Bdenprod, List.foldr_cons, ev_mul, B]
    simp only [Bnumprod, Bdenprod] at ih
    push_cast
    rw [div_mul_div_comm]

theorem ev_smul_const (c : ℤ) (P : P2) : ev (P2.smul [c] P) = (c : L24) * ev P := by
  simp [ev, P2.eval_smul, P1.eval]

theorem ev_ofFn (v : Fin 8 → ℤ) : ev [List.ofFn v] = algebraMap L8 L24 (evF v) := by
  simp only [ev, P2.eval_cons, P2.eval_nil, mul_zero, add_zero, aL24, P1_eval_ringHom]
  rw [← ev8_ofFn]
  rfl

theorem Yrel (Ynum : P2) (Yden : ℕ) (hY : Yden ≠ 0) (v : Fin 8 → ℤ) (l : List (Fin 24))
    (h : ev (P2.smul [Bdenprod l] (P2.mul Ynum [List.ofFn v])) =
      ev (P2.smul [(Yden : ℤ) * 820] (Bnumprod l))) :
    ev Ynum / (Yden : L24) * algebraMap L8 L24 (evF v / 820) = (l.map B).prod := by
  have hd : (Bdenprod l : L24) ≠ 0 := by
    simp only [Bdenprod, Int.cast_list_prod, List.map_map]
    refine List.prod_ne_zero ?_
    simp only [List.mem_map, not_exists, not_and]
    intro i _ hi
    exact Bden_ne_zero i (by simpa using hi)
  have hY' : (Yden : L24) ≠ 0 := Nat.cast_ne_zero.mpr hY
  rw [ev_smul_const, ev_smul_const, ev_mul, ev_ofFn] at h
  rw [prod_B, map_div₀, map_ofNat]
  field_simp
  push_cast at h
  linear_combination h

theorem Zrel (p : ℕ) (z : List ℤ) (vs : List (Fin 8 → ℤ)) (hvs : vs ≠ [])
    (h : ev8 (P1.smul (p * 820 ^ (vs.length - 1)) (wsum z Wω)) = ev8 (prodList (vs.map List.ofFn))) :
    (p : L8) * (ev8 (wsum z Wω) / 820) = (vs.map fun v => evF v / 820).prod := by
  have hsm : ∀ (c : ℤ) (q : P1), ev8 (P1.smul c q) = c * ev8 q := fun c q => P1.eval_smul a c q
  rw [hsm, ev8_prodList, List.map_map] at h
  have e : (vs.map fun v => evF v / 820).prod = (vs.map evF).prod / 820 ^ vs.length := by
    clear h hvs
    induction vs with
    | nil => simp
    | cons v vs ih => simp [ih, pow_succ]; ring
  have e2 : (vs.map (ev8 ∘ List.ofFn)) = vs.map evF := by
    congr 1
    funext v
    exact ev8_ofFn v
  rw [e2] at h
  rw [e, ← h]
  obtain ⟨n, hn⟩ : ∃ n, vs.length = n + 1 := Nat.exists_eq_succ_of_ne_zero (by simpa using hvs)
  rw [hn, Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

end

end X2Y5Z7.SUnits
