import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.ZMod.Basic

/-! # The fifth-power residue symbol on a field

For a field `K`, a primitive fifth root of unity `ζ ∈ K` and an exponent `e` with `x^(5e) = 1` for all `x ≠ 0`
(in a finite field with `Q ≡ 1 mod 5` elements, `e = (Q - 1)/5`), `symK ζ e x ∈ ZMod 5` is the `s` with
`x^e = ζ^s`. The character is defined by
choice from the existence of a discrete logarithm, and multiplicativity comes from uniqueness.

Main lemmas: `symK_spec`, `symK_eq_iff`, `symK_mul`, `symK_one`, `symK_inv`, `symK_div`, `symK_pow`,
`symK_pow_five`. -/

namespace X2Y5Z7.FiniteFields

variable {K : Type*} [Field K]

/-- The fifth-power residue symbol: `s` with `x^e = ζ^s` (and `0` if there is none, e.g. for `x = 0`). -/
noncomputable def symK (ζ : K) (e : ℕ) (x : K) : ZMod 5 :=
  open Classical in if h : ∃ s : ZMod 5, x ^ e = ζ ^ s.val then h.choose else 0

section

variable {ζ : K} {e : ℕ} (hζ : IsPrimitiveRoot ζ 5) (he : ∀ x : K, x ≠ 0 → x ^ (e * 5) = 1)
include hζ he

theorem symK_exists {x : K} (hx : x ≠ 0) : ∃ s : ZMod 5, x ^ e = ζ ^ s.val := by
  have h5 : (x ^ e) ^ 5 = 1 := by rw [← pow_mul]; exact he x hx
  obtain ⟨i, hi, hζi⟩ := hζ.eq_pow_of_pow_eq_one h5
  exact ⟨(i : ZMod 5), by rw [ZMod.val_cast_of_lt hi, hζi]⟩

theorem symK_spec {x : K} (hx : x ≠ 0) : x ^ e = ζ ^ (symK ζ e x).val := by
  have h := symK_exists hζ he hx
  rw [symK, dite_eq_left h]
  exact h.choose_spec

theorem symK_eq_iff {x : K} (hx : x ≠ 0) (s : ZMod 5) : symK ζ e x = s ↔ x ^ e = ζ ^ s.val := by
  constructor
  · rintro rfl; exact symK_spec hζ he hx
  · intro h
    have h2 := (symK_spec hζ he hx).symm.trans h
    exact ZMod.val_injective 5 (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2)

omit he in
theorem pow_val_add (a b : ZMod 5) : ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) 5, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

theorem symK_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : symK ζ e (x * y) = symK ζ e x + symK ζ e y := by
  rw [symK_eq_iff hζ he (mul_ne_zero hx hy), mul_pow, symK_spec hζ he hx, symK_spec hζ he hy,
    pow_val_add hζ]

theorem symK_one : symK ζ e (1 : K) = 0 := by
  rw [symK_eq_iff hζ he one_ne_zero]; simp

theorem symK_inv {x : K} (hx : x ≠ 0) : symK ζ e x⁻¹ = - symK ζ e x := by
  have h := symK_mul hζ he hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, symK_one hζ he] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem symK_div {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : symK ζ e (x / y) = symK ζ e x - symK ζ e y := by
  rw [div_eq_mul_inv, symK_mul hζ he hx (inv_ne_zero hy), symK_inv hζ he hy, sub_eq_add_neg]

theorem symK_pow {x : K} (hx : x ≠ 0) : ∀ n : ℕ, symK ζ e (x ^ n) = n * symK ζ e x
  | 0 => by simp [symK_one hζ he]
  | n + 1 => by
    rw [pow_succ, symK_mul hζ he (pow_ne_zero n hx) hx, symK_pow hx n]; push_cast; ring

theorem symK_pow_five {x : K} (hx : x ≠ 0) : symK ζ e (x ^ 5) = 0 := by
  rw [symK_pow hζ he hx]
  have : ((5 : ℕ) : ZMod 5) = 0 := by decide
  rw [this, zero_mul]

end

end X2Y5Z7.FiniteFields
