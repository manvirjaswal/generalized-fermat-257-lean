module

public import X2Y5Z7.Integral.Basic
public import X2Y5Z7.Descent.Basic

@[expose] public section

/-! # Proposition 3.2: the norm of the descent element

For `θ ∈ L₈` with `ψ(θ) ≠ 0`,
`N_{L₂₄/L₈}(80000 (θ - b) ψ(θ)³) = 2²¹ · 5¹⁰ · ψ(θ)¹⁰ = 2 · (2⁴ · 5² · ψ(θ)²)⁵`.

By `Integral.norm_rel`, `N_{L₂₄/L₈}(θ - b) = ψ(θ)/25`, while `80000 = 2⁷ · 5⁴` and `ψ(θ)` lie in `L₈`, so their norms
are their cubes. -/

namespace X2Y5Z7

open Polynomial Integral

noncomputable section

namespace Norm

theorem aeval_ψ_L8 (t : L8) : aeval t ψ = 25 * t ^ 3 + 20 * t ^ 2 + 14 * t + 14 := by
  simp [ψ, ψZ, aeval_def]

/-- The norm of an element of `L₈` is its cube. -/
theorem norm_algebraMap_L8 (x : L8) : Algebra.norm L8 (algebraMap L8 L24 x) = x ^ 3 := by
  rw [Algebra.norm_algebraMap, L24_finrank_over_L8]

/-- `N_{L₂₄/L₈}(θ - b) = ψ(θ)/25`. -/
theorem norm_sub_b (θ : L8) : Algebra.norm L8 (algebraMap L8 L24 θ - b) = aeval θ ψ / 25 := by
  have h := norm_rel θ (-1) 0
  rw [map_neg, map_one, map_zero, zero_mul, add_zero, neg_one_mul, ← sub_eq_add_neg] at h
  rw [h, aeval_ψ_L8, Nf]
  ring

/-- `E = 80000 ψ(θ)³ · (θ - b)` with the first factor in `L₈`. -/
theorem Edesc_algebraMap (θ : L8) :
    Edesc (algebraMap L8 L24 θ) = algebraMap L8 L24 (80000 * aeval θ ψ ^ 3) * (algebraMap L8 L24 θ - b) := by
  rw [Edesc, aeval_algebraMap_apply, map_mul, map_pow, map_ofNat]
  ring

/-- **Proposition 3.2.** `N_{L₂₄/L₈}(E) = 2²¹ · 5¹⁰ · ψ(θ)¹⁰`. -/
theorem norm_Edesc (θ : L8) (_hθ : aeval θ ψ ≠ 0) :
    Algebra.norm L8 (Edesc (algebraMap L8 L24 θ)) = 2 ^ 21 * 5 ^ 10 * (aeval θ ψ) ^ 10 := by
  rw [Edesc_algebraMap, map_mul, norm_algebraMap_L8, norm_sub_b]
  ring

/-- **Proposition 3.2**, second form: `N_{L₂₄/L₈}(E) = 2 · (2⁴ · 5² · ψ(θ)²)⁵`. -/
theorem norm_Edesc_eq_two_mul_pow (θ : L8) (hθ : aeval θ ψ ≠ 0) :
    Algebra.norm L8 (Edesc (algebraMap L8 L24 θ)) = 2 * (2 ^ 4 * 5 ^ 2 * (aeval θ ψ) ^ 2) ^ 5 := by
  rw [norm_Edesc θ hθ]
  ring

end Norm

end

end X2Y5Z7
