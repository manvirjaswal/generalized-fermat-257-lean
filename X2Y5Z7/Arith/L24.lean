import X2Y5Z7.Arith.Poly
import X2Y5Z7.Fields.Basic

/-! # Evaluating integer polynomials in `L8` and `L24`

`ev8 p = p(a) ∈ L8` and `ev P = P(a, b) ∈ L24`. An identity between such values follows from a certificate
`c · (P - Q) = K₁ · h + K₂ · ψ` in `ℤ[x, y]` (`ev_eq_of_cert`, `ev8_eq_of_cert`), checked in the kernel. -/

namespace X2Y5Z7

open Polynomial

noncomputable section

/-- The coefficients of `h`, lowest degree first. -/
def hP1 : P1 := [-940, -480, 840, 560, -140, -168, -28, 4, 1]

/-- `h` as a polynomial in `x` only. -/
def hP2 : P2 := [hP1]

/-- `ψ` as a polynomial in `y` only. -/
def ψP2 : P2 := [[14], [14], [20], [25]]

/-- `a` viewed in `L24`. -/
def aL24 : L24 := algebraMap L8 L24 a

/-- `p(a)` in `L8`. -/
def ev8 (p : P1) : L8 := P1.eval a p

/-- `P(a, b)` in `L24`. -/
def ev (P : P2) : L24 := P2.eval aL24 b P

theorem aeval_a_h : aeval a h = 0 := by
  have : aeval (AdjoinRoot.root h) h = 0 := AdjoinRoot.aeval_eq h ▸ AdjoinRoot.mk_self
  exact this

theorem P1_eval_hP1 {R : Type*} [CommRing R] (x : R) :
    P1.eval x hP1 = x^8 + 4*x^7 - 28*x^6 - 168*x^5 - 140*x^4 + 560*x^3 + 840*x^2 - 480*x - 940 := by
  simp [hP1, P1.eval]
  ring

theorem aeval_h_eq {R : Type*} [CommRing R] [Algebra ℚ R] (x : R) :
    aeval x h = x^8 + 4*x^7 - 28*x^6 - 168*x^5 - 140*x^4 + 560*x^3 + 840*x^2 - 480*x - 940 := by
  simp [h, hZ, aeval_def]

theorem ev8_hP1 : ev8 hP1 = 0 := by
  rw [ev8, P1_eval_hP1, ← aeval_h_eq, aeval_a_h]

theorem ev_hP2 : ev hP2 = 0 := by
  have h1 : P1.eval aL24 hP1 = algebraMap L8 L24 (P1.eval a hP1) := by
    rw [P1_eval_hP1, P1_eval_hP1, aL24]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  simp only [ev, hP2, P2.eval_cons, P2.eval_nil, mul_zero, add_zero, h1]
  rw [show P1.eval a hP1 = ev8 hP1 from rfl, ev8_hP1, map_zero]

theorem aeval_ψ_eq {R : Type*} [CommRing R] [Algebra ℚ R] (y : R) :
    aeval y ψ = 25*y^3 + 20*y^2 + 14*y + 14 := by
  simp [ψ, ψZ, aeval_def]

theorem ev_ψP2 : ev ψP2 = 0 := by
  have : ev ψP2 = 25*b^3 + 20*b^2 + 14*b + 14 := by
    simp [ev, ψP2, P2.eval, P1.eval]; ring
  rw [this, ← aeval_ψ_eq, b_root]

/-- The certificate lemma in `L24`. -/
theorem ev_eq_of_cert (P Q K₁ K₂ : P2) (c : ℤ) (hc : c ≠ 0)
    (hcert : P2.isZero (P2.sub (P2.smul [c] (P2.sub P Q)) (P2.add (P2.mul K₁ hP2) (P2.mul K₂ ψP2))) = true) :
    ev P = ev Q :=
  P2.eval_eq_of_certificate aL24 b P Q hP2 ψP2 K₁ K₂ c hc ev_hP2 ev_ψP2 hcert

/-- The certificate lemma in `L8`. -/
theorem ev8_eq_of_cert (p q k : P1) (c : ℤ) (hc : c ≠ 0)
    (hcert : P1.isZero (P1.sub (P1.smul c (P1.sub p q)) (P1.mul k hP1)) = true) :
    ev8 p = ev8 q := by
  have hz := P1.eval_of_isZero a _ hcert
  rw [P1.eval_sub, P1.eval_smul, P1.eval_sub, P1.eval_mul] at hz
  rw [show P1.eval a hP1 = ev8 hP1 from rfl, ev8_hP1, mul_zero, sub_zero] at hz
  have hc' : (c : L8) ≠ 0 := Int.cast_ne_zero.mpr hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hc')

/-! ## Evaluation is a ring homomorphism on the list operations -/

theorem ev_add (P Q : P2) : ev (P2.add P Q) = ev P + ev Q := P2.eval_add _ _ P Q
theorem ev_mul (P Q : P2) : ev (P2.mul P Q) = ev P * ev Q := P2.eval_mul _ _ P Q
theorem ev_sub (P Q : P2) : ev (P2.sub P Q) = ev P - ev Q := P2.eval_sub _ _ P Q
theorem ev8_add (p q : P1) : ev8 (P1.add p q) = ev8 p + ev8 q := P1.eval_add _ p q
theorem ev8_mul (p q : P1) : ev8 (P1.mul p q) = ev8 p * ev8 q := P1.eval_mul _ p q

/-- A constant polynomial evaluates to the integer. -/
theorem ev_const (c : ℤ) : ev [[c]] = (c : L24) := by simp [ev, P2.eval, P1.eval]

theorem ev8_const (c : ℤ) : ev8 [c] = (c : L8) := by simp [ev8, P1.eval]

end

end X2Y5Z7
