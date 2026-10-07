import X2Y5Z7.Auxiliary.Generators

/-! # The case `q ∣ Y`: the generators `τ_d`

`Ψ(t) = 10t⁴ + 4t³ + 2t² + 2t - 1` satisfies `4t⁵ψ(t) - (4t - 1) = Ψ(t)²`, so
`Z⁷ Ψ(θ)² = (X⁵ - Z⁷)(4θ - 1) = -Y²(4θ - 1)`. With `σ = Ψ(θ)/Y` we get `Z⁷σ² = 1 - 4θ` and `Ψ((1 - Z⁷σ²)/4) = Yσ`.
For `d ∈ ℤ` put `τ_d = 5 Z⁴ d σ`. It is a root of the monic

  `G_d = T⁸ - 140Zd²T⁶ + 8750Z²d⁴T⁴ - 437500Z³d⁶T² - 2000000Yd⁷T - 2734375Z⁴d⁸`,

and `G_d(τ_d) = 10⁷ Z⁴ d⁸ (Ψ((1 - Z⁷σ²)/4) - Yσ)`. Modulo `Y`, `G_d` becomes `P_c` with `c = Z d²`, where

  `P_c(T) = T⁸ - 140cT⁶ + 8750c²T⁴ - 437500c³T² - 2734375c⁴ = 10⁷ c⁴ Ψ((25c - T²)/(100c))`.

`P_c(T) = Q_c(T²)` and `(-4x² + 520cx - 40500c²) Q_c + (x³ - 165cx² + 15375c²x - 546875c³) Q_c' = 350000000000 c⁶`,
`Q_c(0) = -2734375 c⁴ = -5⁸·7·c⁴`, so `P_c` is separable when `70c ≠ 0`. -/

namespace X2Y5Z7.Aux

open Polynomial NumberField

noncomputable section

variable {s : Solution}

variable (s) in
/-- `G_d = T⁸ - 140Zd²T⁶ + 8750Z²d⁴T⁴ - 437500Z³d⁶T² - 2000000Yd⁷T - 2734375Z⁴d⁸`. -/
def Gd (d : ℤ) : ℤ[X] := X ^ 8 - C (140 * s.Z * d ^ 2) * X ^ 6 + C (8750 * s.Z ^ 2 * d ^ 4) * X ^ 4 -
  C (437500 * s.Z ^ 3 * d ^ 6) * X ^ 2 - C (2000000 * s.Y * d ^ 7) * X - C (2734375 * s.Z ^ 4 * d ^ 8)

variable (s) in
theorem Gd_natDegree (d : ℤ) : (Gd s d).natDegree = 8 := by unfold Gd; compute_degree!

variable (s) in
theorem Gd_monic (d : ℤ) : (Gd s d).Monic := by unfold Gd; monicity!

theorem aeval_Gd {A : Type*} [CommRing A] [Algebra ℤ A] (d : ℤ) (y : A) :
    aeval y (Gd s d) = y ^ 8 - 140 * s.Z * d ^ 2 * y ^ 6 + 8750 * s.Z ^ 2 * d ^ 4 * y ^ 4 -
      437500 * s.Z ^ 3 * d ^ 6 * y ^ 2 - 2000000 * s.Y * d ^ 7 * y - 2734375 * s.Z ^ 4 * d ^ 8 := by
  simp only [Gd, map_add, map_sub, map_mul, map_pow, aeval_X, eq_intCast, map_intCast]
  push_cast
  ring

theorem aeval_Gd_derivative {A : Type*} [CommRing A] [Algebra ℤ A] (d : ℤ) (y : A) :
    aeval y (derivative (Gd s d)) = 8 * y ^ 7 - 840 * s.Z * d ^ 2 * y ^ 5 + 35000 * s.Z ^ 2 * d ^ 4 * y ^ 3 -
      875000 * s.Z ^ 3 * d ^ 6 * y - 2000000 * s.Y * d ^ 7 := by
  simp only [Gd, derivative_add, derivative_sub, derivative_mul, derivative_C, derivative_X_pow, derivative_X,
    zero_mul, zero_add, mul_one]
  simp only [map_add, map_sub, map_mul, map_pow, aeval_X, eq_intCast, map_intCast, map_natCast, sub_zero]
  push_cast
  ring

/-- `P_c(T) = T⁸ - 140cT⁶ + 8750c²T⁴ - 437500c³T² - 2734375c⁴`, the reduction of `G_d` modulo `Y`, `c = Zd²`. -/
def Pc {k : Type*} [Field k] (c : k) : k[X] :=
  X ^ 8 - C (140 * c) * X ^ 6 + C (8750 * c ^ 2) * X ^ 4 - C (437500 * c ^ 3) * X ^ 2 - C (2734375 * c ^ 4)

theorem eval_Pc {k : Type*} [Field k] (c y : k) :
    eval y (Pc c) = y ^ 8 - 140 * c * y ^ 6 + 8750 * c ^ 2 * y ^ 4 - 437500 * c ^ 3 * y ^ 2 - 2734375 * c ^ 4 := by
  simp [Pc]

/-- `P_c(T) = 10⁷ c⁴ Ψ((25c - T²)/(100c))`, `Ψ(t) = 10t⁴ + 4t³ + 2t² + 2t - 1`. -/
theorem eval_Pc_eq_Psi {k : Type*} [Field k] [CharZero k] (c y : k) (hc : c ≠ 0) :
    eval y (Pc c) = 10 ^ 7 * c ^ 4 * (10 * ((25 * c - y ^ 2) / (100 * c)) ^ 4 +
      4 * ((25 * c - y ^ 2) / (100 * c)) ^ 3 + 2 * ((25 * c - y ^ 2) / (100 * c)) ^ 2 +
      2 * ((25 * c - y ^ 2) / (100 * c)) - 1) := by
  rw [eval_Pc]
  field_simp
  ring

/-- Modulo `Y`, `G_d` becomes `P_c` with `c = Z d²`. -/
theorem Gd_map {k : Type*} [Field k] (d : ℤ) (hY : (s.Y : k) = 0) :
    (Gd s d).map (Int.castRingHom k) = Pc ((s.Z : k) * (d : k) ^ 2) := by
  have hY' : ((s.Y : ℤ) : k[X]) = 0 := by rw [← map_intCast (C : k →+* k[X]) s.Y, hY, map_zero]
  simp only [Gd, Pc, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, eq_intCast, Polynomial.map_intCast, Polynomial.map_ofNat, map_mul, map_pow, map_ofNat,
    map_intCast]
  rw [hY']
  ring

namespace Root

variable (R : Root s)

/-- `Ψ(θ) = 10θ⁴ + 4θ³ + 2θ² + 2θ - 1`. -/
def Psi : L8 := 10 * R.θ ^ 4 + 4 * R.θ ^ 3 + 2 * R.θ ^ 2 + 2 * R.θ - 1

/-- `Z⁷ Ψ(θ)² = -Y² (4θ - 1)`. -/
theorem Psi_sq : (s.Z : L8) ^ 7 * R.Psi ^ 2 = -(s.Y : L8) ^ 2 * (4 * R.θ - 1) := by
  have heq := eq_cast (s := s) (k := L8)
  rw [Psi]
  linear_combination R.key + (4 * R.θ - 1) * heq

/-- `σ = Ψ(θ)/Y`. -/
def σ : L8 := R.Psi / s.Y

theorem σ_sq : (s.Z : L8) ^ 7 * R.σ ^ 2 = 1 - 4 * R.θ := by
  have hY := Y_ne' (s := s)
  rw [σ]
  field_simp
  linear_combination R.Psi_sq

/-- `τ_d = 5 Z⁴ d σ`. -/
def τ (d : ℤ) : L8 := 5 * (s.Z : L8) ^ 4 * d * R.σ

theorem aeval_τ (d : ℤ) : aeval (R.τ d) (Gd s d) = 0 := by
  have hY := Y_ne' (s := s)
  have hθ : R.θ = (1 - (s.Z : L8) ^ 7 * R.σ ^ 2) / 4 := by linear_combination R.σ_sq / 4
  have hΨ : R.Psi = s.Y * R.σ := by rw [σ]; field_simp
  rw [Psi, hθ] at hΨ
  rw [τ, aeval_Gd]
  linear_combination 10000000 * (s.Z : L8) ^ 4 * (d : L8) ^ 8 * hΨ

/-- `τ_d` as an algebraic integer. -/
def τI (d : ℤ) : 𝓞 L8 := mkInt (R.τ d) (Gd s d) (Gd_monic s d) (R.aeval_τ d)

@[simp] theorem coe_τI (d : ℤ) : (R.τI d : L8) = 5 * (s.Z : L8) ^ 4 * d * (R.Psi / s.Y) := rfl

theorem aeval_τI (d : ℤ) : aeval (R.τI d) (Gd s d) = 0 := aeval_mkInt _ _ _ _

theorem adjoin_τI (d : ℤ) (hd : d ≠ 0) : Algebra.adjoin ℚ {(R.τI d : L8)} = ⊤ := by
  refine adjoin_eq_top_of_mem R.gen (mem_adjoin_of_eq
    (C (1 / 4 : ℚ) - C (100 * (s.Z : ℚ) * (d : ℚ) ^ 2)⁻¹ * X ^ 2) ?_)
  have hZ := Z_ne' (s := s)
  have hY := Y_ne' (s := s)
  have hd' : (d : L8) ≠ 0 := Int.cast_ne_zero.mpr hd
  have h := R.Psi_sq
  simp only [coe_τI, map_mul, map_sub, map_pow, aeval_C, aeval_X, map_inv₀, map_div₀, map_one, map_ofNat,
    map_intCast]
  field_simp
  linear_combination 100 * h

theorem minpoly_τI (d : ℤ) (hd : d ≠ 0) : minpoly ℤ (R.τI d) = Gd s d :=
  minpoly_eq_of_gen _ _ (Gd_monic s d) (Gd_natDegree s d) (R.aeval_τI d) (R.adjoin_τI d hd)

variable {k : Type*} [Field k] (r : 𝓞 L8 →+* k)

theorem aeval_res_τI (d : ℤ) : aeval (r (R.τI d)) (Gd s d) = 0 := by
  rw [← ringHom_aeval, R.aeval_τI, map_zero]

/-- Modulo `q ∣ Y`, the residue of `τ_d` is a root of `P_c`, `c = Z d²`. -/
theorem eval_Pc_res_τI (d : ℤ) (hY : (s.Y : k) = 0) :
    eval (r (R.τI d)) (Pc ((s.Z : k) * (d : k) ^ 2)) = 0 := by
  rw [← Gd_map d hY, eval_map, ← algebraMap_int_eq, ← aeval_def, R.aeval_res_τI]

/-- `q ∣ Y`, `r(70 Z d) ≠ 0`: `G_d'(τ_d)` survives. -/
theorem τI_derivative_ne_zero (d : ℤ) (hY : (s.Y : k) = 0) (h : (70 : k) * s.Z * d ≠ 0) :
    r (aeval (R.τI d) (derivative (Gd s d))) ≠ 0 := by
  have h70 : (70 : k) ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul h)
  have hZ : (s.Z : k) ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul h)
  have hd : (d : k) ≠ 0 := right_ne_zero_of_mul h
  have hG := R.aeval_res_τI r d
  rw [aeval_Gd] at hG
  rw [ringHom_aeval, aeval_Gd_derivative]
  set y := r (R.τI d)
  intro hD
  have hy : y ≠ 0 := by
    intro h0
    rw [h0] at hG
    have h1 : ((2 : k) ^ 0 * 5 ^ 8 * 7 ^ 1) * ((s.Z : k) ^ 4 * (d : k) ^ 8) = 0 := by
      linear_combination -hG
    exact mul_ne_zero (ne_zero_257 h70 0 8 1) (mul_ne_zero (pow_ne_zero _ hZ) (pow_ne_zero _ hd)) h1
  have h0 : ((2 : k) ^ 11 * 5 ^ 11 * 7 ^ 1) * (y * (s.Z : k) ^ 6 * (d : k) ^ 12) = 0 := by
    linear_combination
      (2 * y * (-4 * y ^ 4 + 520 * s.Z * d ^ 2 * y ^ 2 - 40500 * s.Z ^ 2 * d ^ 4)) * hG +
      (y ^ 6 - 165 * s.Z * d ^ 2 * y ^ 4 + 15375 * s.Z ^ 2 * d ^ 4 * y ^ 2 - 546875 * s.Z ^ 3 * d ^ 6) * hD +
      (2000000 * (d : k) ^ 7 * (2 * y ^ 2 * (-4 * y ^ 4 + 520 * s.Z * d ^ 2 * y ^ 2 - 40500 * s.Z ^ 2 * d ^ 4) +
        (y ^ 6 - 165 * s.Z * d ^ 2 * y ^ 4 + 15375 * s.Z ^ 2 * d ^ 4 * y ^ 2 - 546875 * s.Z ^ 3 * d ^ 6))) * hY
  exact mul_ne_zero (ne_zero_257 h70 11 11 1)
    (mul_ne_zero (mul_ne_zero hy (pow_ne_zero _ hZ)) (pow_ne_zero _ hd)) h0

end Root

end

end X2Y5Z7.Aux
