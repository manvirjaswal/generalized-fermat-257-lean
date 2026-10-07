import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Exact rational LU certificates checked through integer identities. -/
namespace X2Y5Z7.Integral.LU
open Matrix
noncomputable section

structure Certificate {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (value : ℤ) where
  permutation : Equiv.Perm (Fin n)
  denominator : ℤ
  denominator_ne_zero : denominator ≠ 0
  lower : Matrix (Fin n) (Fin n) ℤ
  upper : Matrix (Fin n) (Fin n) ℤ
  product : ∀ i j, M (permutation i) j * denominator^2 = ∑ k, lower i k * upper k j
  lower_zero : ∀ i j, i < j → lower i j = 0
  upper_zero : ∀ i j, j < i → upper i j = 0
  lower_diag : ∀ i, lower i i = denominator
  diagonal_product : (∏ i, upper i i) = (permutation.sign : ℤ)*value*denominator^n

namespace Certificate
variable {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} {value : ℤ} (C : Certificate M value)

def L : Matrix (Fin n) (Fin n) ℚ := fun i j => (C.lower i j : ℚ)/(C.denominator : ℚ)
def U : Matrix (Fin n) (Fin n) ℚ := fun i j => (C.upper i j : ℚ)/(C.denominator : ℚ)

private theorem den_ne_zero : (C.denominator : ℚ) ≠ 0 := Int.cast_ne_zero.mpr C.denominator_ne_zero

theorem factorization : Matrix.submatrix (fun i j => (M i j : ℚ)) C.permutation id = C.L*C.U := by
  ext i j
  change (M (C.permutation i) j : ℚ) = _
  simp only [Matrix.mul_apply, L, U, div_mul_div_comm, ← Finset.sum_div]
  apply (eq_div_iff (mul_ne_zero C.den_ne_zero C.den_ne_zero)).mpr
  have h := congrArg (Int.castRingHom ℚ) (C.product i j)
  simpa only [map_mul, map_pow, map_sum, Int.coe_castRingHom, pow_two] using h

theorem L_lower : C.L.BlockTriangular OrderDual.toDual := by
  intro i j hij
  change i < j at hij
  simp only [L, C.lower_zero i j hij, Int.cast_zero, zero_div]

theorem U_upper : C.U.BlockTriangular id := by
  intro i j hij
  simp only [U, C.upper_zero i j hij, Int.cast_zero, zero_div]

theorem L_det : C.L.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ C.L_lower]
  simp only [L, C.lower_diag, div_self C.den_ne_zero, Finset.prod_const_one]

theorem U_det : C.U.det = ((C.permutation.sign : ℤ) : ℚ)*(value : ℚ) := by
  rw [Matrix.det_of_isUpperTriangular C.U_upper]
  simp only [U, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  apply (div_eq_iff (pow_ne_zero n C.den_ne_zero)).mpr
  have h := congrArg (Int.castRingHom ℚ) C.diagonal_product
  simpa only [map_prod, map_mul, map_pow, Int.coe_castRingHom] using h

include C in
/-- The target determinant follows solely from the finite integer certificate. -/
theorem determinant : Matrix.det (fun i j => (M i j : ℚ)) = (value : ℚ) := by
  have h := congrArg Matrix.det C.factorization
  erw [Matrix.det_permute] at h
  rw [Matrix.det_mul, C.L_det, C.U_det, one_mul] at h
  exact mul_left_cancel₀ (Int.cast_ne_zero.mpr C.permutation.sign.ne_zero) h

end Certificate
end
end X2Y5Z7.Integral.LU
