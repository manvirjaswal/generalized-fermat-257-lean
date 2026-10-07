module

public import X2Y5Z7.FiniteFields.Residue
public import X2Y5Z7.Residue.L24
public import X2Y5Z7.SUnits.Data

@[expose] public section

/-! # The residues of the S-unit basis at the model primes

For a model `D : FiniteFields.L24Prime` with residue map `D.res : 𝓞 L₂₄ →+* K` (`FiniteFields/Residue.lean`), an integral `B_j`
reduces to `D.imgB j = B_j(α, β)` (`res_B`), via `25·Bden_j·B_j = Σ_k n_{jk}(a) (5b)^k 5^{2-k}`, which lies
in `ℤ[a, 5b]`. -/

namespace X2Y5Z7.ResidueSymbols

open Polynomial NumberField X2Y5Z7.FiniteFields

noncomputable section

/-- A ring homomorphism commutes with `P1.eval`. -/
theorem map_P1_eval {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    ∀ p : P1, f (P1.eval x p) = P1.eval (f x) p
  | [] => by simp
  | c :: p => by simp [map_P1_eval f x p]

/-- `P2.eval` of a polynomial with at most three rows. -/
theorem P2_eval_three {R : Type*} [CommRing R] (x y : R) (P : P2) (hP : P.length ≤ 3) :
    P2.eval x y P = P1.eval x (P.getD 0 []) + y * P1.eval x (P.getD 1 []) + y ^ 2 * P1.eval x (P.getD 2 []) := by
  match P, hP with
  | [], _ => simp [P2.eval]
  | [r0], _ => simp [P2.eval]
  | [r0, r1], _ => simp [P2.eval]
  | [r0, r1, r2], _ => simp [P2.eval]; ring

/-- The element `Σ_k r_k(a) (5b)^k 5^{2-k}` of `ℤ[a, 5b] ⊆ 𝓞 L₂₄`. -/
def el3 (P : P2) : 𝓞 L24 :=
  25 * algebraMap (𝓞 L8) (𝓞 L24) (P1.eval a8 (P.getD 0 [])) +
    5 * algebraMap (𝓞 L8) (𝓞 L24) (P1.eval a8 (P.getD 1 [])) * b5 +
      algebraMap (𝓞 L8) (𝓞 L24) (P1.eval a8 (P.getD 2 [])) * b5 ^ 2

theorem coe_el3 (P : P2) (hP : P.length ≤ 3) : ((el3 P : 𝓞 L24) : L24) = 25 * ev P := by
  have hb : ((b5 : 𝓞 L24) : L24) = 5 * b := rfl
  have hA : ∀ p : P1, ((algebraMap (𝓞 L8) (𝓞 L24) (P1.eval a8 p) : 𝓞 L24) : L24) =
      P1.eval aL24 p := by
    intro p
    change algebraMap (𝓞 L24) L24 (algebraMap (𝓞 L8) (𝓞 L24) _) = _
    rw [← IsScalarTower.algebraMap_apply (𝓞 L8) (𝓞 L24) L24, IsScalarTower.algebraMap_apply (𝓞 L8) L8 L24,
      map_P1_eval, map_P1_eval]
    rfl
  simp only [el3, map_add, map_mul, map_pow, map_ofNat, hA, hb, ev, P2_eval_three _ _ P hP]
  ring

variable (D : L24Prime)

theorem five_ne : (5 : D.K) ≠ 0 := by
  intro h5
  have hq : D.q = 5 * (D.q / 5) + 1 := by have := D.q5; omega
  have h1 : ((D.q : ℕ) : D.K) = 5 * ((D.q / 5 : ℕ) : D.K) + 1 := by
    have := congrArg (fun n : ℕ => (n : D.K)) hq
    simpa using this
  rw [D.char, h5, zero_mul, zero_add] at h1
  exact zero_ne_one h1

theorem res_el3 (P : P2) (hP : P.length ≤ 3) : D.res (el3 P) = 25 * P2.eval D.α D.β P := by
  simp only [el3, map_add, map_mul, map_pow, map_ofNat, L24Prime.res_algebraMap, L24Prime.res_b5, L24Prime.res8, map_P1_eval,
    res8_a8, P2_eval_three _ _ P hP]
  ring

theorem Bnum_length (j : Fin 24) : (Bnum j).length ≤ 3 := by
  fin_cases j <;> decide

/-- **(a).** The residue of an integral `B_j` is `B_j(α, β)`. -/
theorem res_B (j : Fin 24) (x : 𝓞 L24) (hx : (x : L24) = B j) : D.res x = D.imgB j := by
  have hden : (Bden j : L24) ≠ 0 := by
    have : Bden j ≠ 0 := by fin_cases j <;> decide
    exact_mod_cast this
  have hel : el3 (Bnum j) = (25 * (Bden j : 𝓞 L24)) * x := by
    apply RingOfIntegers.ext
    rw [coe_el3 _ (Bnum_length j)]
    simp only [map_mul, map_ofNat, map_natCast, hx, B]
    field_simp
  have h := congrArg D.res hel
  rw [res_el3 _ _ (Bnum_length j), map_mul, map_mul, map_ofNat, map_natCast] at h
  have h25 : (25 : D.K) ≠ 0 := by
    have := five_ne D
    have : (25 : D.K) = 5 * 5 := by norm_num
    rw [this]; exact mul_ne_zero (five_ne D) (five_ne D)
  have h2 : 25 * P2.eval D.α D.β (Bnum j) = 25 * ((Bden j : D.K) * D.res x) := by rw [h]; ring
  rw [L24Prime.imgB, eq_div_iff (D.den_ne j), mul_left_cancel₀ h25 h2]
  ring

end

end X2Y5Z7.ResidueSymbols
