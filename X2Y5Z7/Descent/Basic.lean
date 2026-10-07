import X2Y5Z7.Fields.Basic

/-! # Solutions, the fibre polynomial and the descent element (Sections 1–3 of the paper)

* A solution of `X⁵ + Y² = Z⁷` (the paper's normalization of `x² + y⁵ = z⁷`): nonzero integers with `X`, `Z`
  coprime. Coprimality of the other pairs follows from the equation.
* `fpoly s = 4t⁵ψ(t) - s(4t - 1) = 100t⁸ + 80t⁷ + 56t⁶ + 56t⁵ - 4st + s`, and `η = X⁵/Z⁷`.
* `Edesc θ = 80000 (θ - b) ψ(θ)³ ∈ L24`, the descent element of Section 3. -/

namespace X2Y5Z7

open Polynomial

noncomputable section

/-- A solution of `X⁵ + Y² = Z⁷` in nonzero integers with `X` and `Z` coprime. -/
structure Solution where
  X : ℤ
  Y : ℤ
  Z : ℤ
  X_ne : X ≠ 0
  Y_ne : Y ≠ 0
  Z_ne : Z ≠ 0
  coprime : IsCoprime X Z
  eq : X ^ 5 + Y ^ 2 = Z ^ 7

namespace Solution

variable (s : Solution)

/-- `η = X⁵/Z⁷`. -/
def η : ℚ := (s.X : ℚ) ^ 5 / (s.Z : ℚ) ^ 7

theorem coprime_XY : IsCoprime s.X s.Y := by
  have h := (s.coprime.pow_right (n := 7)).add_mul_left_right (-(s.X ^ 4))
  have e : s.Z ^ 7 + s.X * -(s.X ^ 4) = s.Y ^ 2 := by linear_combination -s.eq
  rw [e] at h
  exact (IsCoprime.pow_right_iff two_pos).mp h

theorem coprime_YZ : IsCoprime s.Y s.Z := by
  have h := (s.coprime.symm.pow_right (n := 5)).add_mul_left_right (-(s.Z ^ 6))
  have e : s.X ^ 5 + s.Z * -(s.Z ^ 6) = -(s.Y ^ 2) := by linear_combination s.eq
  rw [e, IsCoprime.neg_right_iff] at h
  exact ((IsCoprime.pow_right_iff two_pos).mp h).symm

end Solution

/-- The fibre polynomial `f_s(t) = 4t⁵ψ(t) - s(4t - 1)`. -/
def fpoly (s : ℚ) : ℚ[X] := C 4 * X ^ 5 * ψ - C s * (C 4 * X - 1)

theorem aeval_fpoly {R : Type*} [CommRing R] [Algebra ℚ R] (s : ℚ) (t : R) :
    aeval t (fpoly s) = 100 * t ^ 8 + 80 * t ^ 7 + 56 * t ^ 6 + 56 * t ^ 5 - 4 * algebraMap ℚ R s * t +
      algebraMap ℚ R s := by
  simp only [fpoly, ψ, ψZ, map_sub, map_mul, map_pow, aeval_X, aeval_C, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_ofNat, map_add, map_ofNat, map_one]
  ring

/-- The descent element `E = 80000 (θ - b) ψ(θ)³`. -/
def Edesc (θ : L24) : L24 := 80000 * (θ - b) * (aeval θ ψ) ^ 3

end

end X2Y5Z7
