import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.Ring

/-! # Integer polynomials as lists, for kernel-checked identities

Identities in `L8` and `L24` are proved by exhibiting integer polynomials: an identity `P(a, b) = Q(a, b)` follows
from `c · (P - Q) = K₁ · h(x) + K₂ · ψ(y)` in `ℤ[x, y]` with `c ≠ 0`, since `h(a) = ψ(b) = 0`. The polynomial
identity is checked by evaluation in the kernel (`decide`), on lists of integers, which is fast.

* `P1 = List ℤ`: `c₀ + c₁ x + …` (lowest degree first).
* `P2 = List P1`: `r₀ + r₁ y + …`, each row a polynomial in `x`.

The evaluation maps `P1.eval`, `P2.eval` into any commutative ring respect `add`, `mul`, `smul`, and `isZero`
polynomials evaluate to `0`. -/

namespace X2Y5Z7

/-- Univariate integer polynomials, lowest degree first. -/
abbrev P1 := List ℤ

/-- Bivariate integer polynomials: rows indexed by the power of `y`, each a polynomial in `x`. -/
abbrev P2 := List P1

namespace P1

def add : P1 → P1 → P1
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

def smul (c : ℤ) : P1 → P1
  | [] => []
  | a :: p => (c * a) :: smul c p

def neg (p : P1) : P1 := smul (-1) p

def sub (p q : P1) : P1 := add p (neg q)

def mul : P1 → P1 → P1
  | [], _ => []
  | a :: p, q => add (smul a q) (0 :: mul p q)

def isZero : P1 → Bool
  | [] => true
  | a :: p => a == 0 && isZero p

/-- Evaluation at `x` (Horner). -/
def eval {R : Type*} [CommRing R] (x : R) : P1 → R
  | [] => 0
  | a :: p => (a : R) + x * eval x p

variable {R : Type*} [CommRing R] (x : R)

@[simp] theorem eval_nil : eval x [] = 0 := rfl
@[simp] theorem eval_cons (a : ℤ) (p : P1) : eval x (a :: p) = (a : R) + x * eval x p := rfl

theorem eval_add : ∀ p q : P1, eval x (add p q) = eval x p + eval x q
  | [], q => by simp [add]
  | a :: p, [] => by simp [add]
  | a :: p, b :: q => by simp only [add, eval_cons, eval_add p q, Int.cast_add]; ring

theorem eval_smul (c : ℤ) : ∀ p : P1, eval x (smul c p) = c * eval x p
  | [] => by simp [smul]
  | a :: p => by simp only [smul, eval_cons, eval_smul c p, Int.cast_mul]; ring

theorem eval_neg (p : P1) : eval x (neg p) = - eval x p := by
  simp [neg, eval_smul]

theorem eval_sub (p q : P1) : eval x (sub p q) = eval x p - eval x q := by
  simp [sub, eval_add, eval_neg, sub_eq_add_neg]

theorem eval_mul : ∀ p q : P1, eval x (mul p q) = eval x p * eval x q
  | [], q => by simp [mul]
  | a :: p, q => by simp only [mul, eval_add, eval_smul, eval_cons, eval_mul p q, Int.cast_zero]; ring

theorem eval_of_isZero : ∀ p : P1, isZero p = true → eval x p = 0
  | [], _ => rfl
  | a :: p, h => by
    simp only [isZero, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, eval_of_isZero p h.2]

end P1

namespace P2

def add : P2 → P2 → P2
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => P1.add a b :: add p q

/-- Multiplication of every row by a polynomial in `x`. -/
def smul (c : P1) : P2 → P2
  | [] => []
  | a :: p => P1.mul c a :: smul c p

def neg (p : P2) : P2 := smul [-1] p

def sub (p q : P2) : P2 := add p (neg q)

def mul : P2 → P2 → P2
  | [], _ => []
  | a :: p, q => add (smul a q) ([] :: mul p q)

def isZero : P2 → Bool
  | [] => true
  | a :: p => P1.isZero a && isZero p

/-- Evaluation at `(x, y)`. -/
def eval {R : Type*} [CommRing R] (x y : R) : P2 → R
  | [] => 0
  | a :: p => P1.eval x a + y * eval x y p

variable {R : Type*} [CommRing R] (x y : R)

@[simp] theorem eval_nil : eval x y [] = 0 := rfl
@[simp] theorem eval_cons (a : P1) (p : P2) : eval x y (a :: p) = P1.eval x a + y * eval x y p := rfl

theorem eval_add : ∀ p q : P2, eval x y (add p q) = eval x y p + eval x y q
  | [], q => by simp [add]
  | a :: p, [] => by simp [add]
  | a :: p, b :: q => by simp only [add, eval_cons, eval_add p q, P1.eval_add]; ring

theorem eval_smul (c : P1) : ∀ p : P2, eval x y (smul c p) = P1.eval x c * eval x y p
  | [] => by simp [smul]
  | a :: p => by simp only [smul, eval_cons, eval_smul c p, P1.eval_mul]; ring

theorem eval_neg (p : P2) : eval x y (neg p) = - eval x y p := by
  simp [neg, eval_smul]

theorem eval_sub (p q : P2) : eval x y (sub p q) = eval x y p - eval x y q := by
  simp [sub, eval_add, eval_neg, sub_eq_add_neg]

theorem eval_mul : ∀ p q : P2, eval x y (mul p q) = eval x y p * eval x y q
  | [], q => by simp [mul]
  | a :: p, q => by simp only [mul, eval_add, eval_smul, eval_cons, eval_mul p q, P1.eval_nil]; ring

theorem eval_of_isZero : ∀ p : P2, isZero p = true → eval x y p = 0
  | [], _ => rfl
  | a :: p, h => by
    simp only [isZero, Bool.and_eq_true] at h
    simp [P1.eval_of_isZero x a h.1, eval_of_isZero p h.2]

/-- The certificate lemma: if `c · (P - Q) - (K₁ H + K₂ Ψ)` is the zero polynomial, `H(x, y) = Ψ(x, y) = 0` and
`c ≠ 0` in a ring without `ℤ`-torsion, then `P(x, y) = Q(x, y)`. -/
theorem eval_eq_of_certificate [IsDomain R] [CharZero R] (P Q H Ψ K₁ K₂ : P2) (c : ℤ) (hc : c ≠ 0)
    (hH : eval x y H = 0) (hΨ : eval x y Ψ = 0)
    (hcert : isZero (sub (smul [c] (sub P Q)) (add (mul K₁ H) (mul K₂ Ψ))) = true) :
    eval x y P = eval x y Q := by
  have h := eval_of_isZero x y _ hcert
  rw [eval_sub, eval_smul, eval_sub, eval_add, eval_mul, eval_mul, hH, hΨ] at h
  simp only [P1.eval_cons, P1.eval_nil, mul_zero, add_zero, sub_zero] at h
  have hc' : (c : R) ≠ 0 := Int.cast_ne_zero.mpr hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hc')

end P2

end X2Y5Z7
