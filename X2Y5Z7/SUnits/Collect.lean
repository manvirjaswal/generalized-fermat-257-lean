/-
Generated from Table 4 of the paper.
-/
import X2Y5Z7.SUnits.Cert0
import X2Y5Z7.SUnits.Cert1
import X2Y5Z7.SUnits.Cert2

/-! # Integrality and norms of `B₁, …, B₂₄` (collected from `Cert0`–`Cert2`) -/

namespace X2Y5Z7

open Integral SUnits

theorem norm_of_tower (x : L24) (y : L8) (value : ℤ) (h₁ : Algebra.norm L8 x = y)
    (h₂ : Algebra.norm ℚ y = (value : ℚ) / 820 ^ 8) : Algebra.norm ℚ x = (value : ℚ) / 820 ^ 8 := by
  rw [← Algebra.norm_norm (S := L8), h₁, h₂]

theorem B_isIntegral (j : Fin 24) : IsIntegral ℤ (B j) := by
  fin_cases j
  exacts [isIntegral_0, isIntegral_1, isIntegral_2, isIntegral_3, isIntegral_4, isIntegral_5, isIntegral_6, isIntegral_7, isIntegral_8, isIntegral_9, isIntegral_10, isIntegral_11, isIntegral_12, isIntegral_13, isIntegral_14, isIntegral_15, isIntegral_16, isIntegral_17, isIntegral_18, isIntegral_19, isIntegral_20, isIntegral_21, isIntegral_22, isIntegral_23]

theorem B_norm_0 : Algebra.norm ℚ (B 0) = -2 :=
  (norm_of_tower _ _ _ normL8_0 norm_0).trans (by norm_num)

theorem B_norm_1 : Algebra.norm ℚ (B 1) = 5 :=
  (norm_of_tower _ _ _ normL8_1 norm_1).trans (by norm_num)

theorem B_norm_2 : Algebra.norm ℚ (B 2) = 5 :=
  (norm_of_tower _ _ _ normL8_2 norm_2).trans (by norm_num)

theorem B_norm_3 : Algebra.norm ℚ (B 3) = 5 :=
  (norm_of_tower _ _ _ normL8_3 norm_3).trans (by norm_num)

theorem B_norm_4 : Algebra.norm ℚ (B 4) = 5 :=
  (norm_of_tower _ _ _ normL8_4 norm_4).trans (by norm_num)

theorem B_norm_5 : Algebra.norm ℚ (B 5) = 5 :=
  (norm_of_tower _ _ _ normL8_5 norm_5).trans (by norm_num)

theorem B_norm_6 : Algebra.norm ℚ (B 6) = 5 :=
  (norm_of_tower _ _ _ normL8_6 norm_6).trans (by norm_num)

theorem B_norm_7 : Algebra.norm ℚ (B 7) = 5 :=
  (norm_of_tower _ _ _ normL8_7 norm_7).trans (by norm_num)

theorem B_norm_8 : Algebra.norm ℚ (B 8) = -7 :=
  (norm_of_tower _ _ _ normL8_8 norm_8).trans (by norm_num)

theorem B_norm_9 : Algebra.norm ℚ (B 9) = -7 :=
  (norm_of_tower _ _ _ normL8_9 norm_9).trans (by norm_num)

theorem B_norm_10 : Algebra.norm ℚ (B 10) = -7 :=
  (norm_of_tower _ _ _ normL8_10 norm_10).trans (by norm_num)

theorem B_norm_11 : Algebra.norm ℚ (B 11) = -7 :=
  (norm_of_tower _ _ _ normL8_11 norm_11).trans (by norm_num)

theorem B_norm_12 : Algebra.norm ℚ (B 12) = 1 :=
  (norm_of_tower _ _ _ normL8_12 norm_12).trans (by norm_num)

theorem B_norm_13 : Algebra.norm ℚ (B 13) = 1 :=
  (norm_of_tower _ _ _ normL8_13 norm_13).trans (by norm_num)

theorem B_norm_14 : Algebra.norm ℚ (B 14) = 1 :=
  (norm_of_tower _ _ _ normL8_14 norm_14).trans (by norm_num)

theorem B_norm_15 : Algebra.norm ℚ (B 15) = 1 :=
  (norm_of_tower _ _ _ normL8_15 norm_15).trans (by norm_num)

theorem B_norm_16 : Algebra.norm ℚ (B 16) = 1 :=
  (norm_of_tower _ _ _ normL8_16 norm_16).trans (by norm_num)

theorem B_norm_17 : Algebra.norm ℚ (B 17) = 1 :=
  (norm_of_tower _ _ _ normL8_17 norm_17).trans (by norm_num)

theorem B_norm_18 : Algebra.norm ℚ (B 18) = 1 :=
  (norm_of_tower _ _ _ normL8_18 norm_18).trans (by norm_num)

theorem B_norm_19 : Algebra.norm ℚ (B 19) = 1 :=
  (norm_of_tower _ _ _ normL8_19 norm_19).trans (by norm_num)

theorem B_norm_20 : Algebra.norm ℚ (B 20) = 1 :=
  (norm_of_tower _ _ _ normL8_20 norm_20).trans (by norm_num)

theorem B_norm_21 : Algebra.norm ℚ (B 21) = 1 :=
  (norm_of_tower _ _ _ normL8_21 norm_21).trans (by norm_num)

theorem B_norm_22 : Algebra.norm ℚ (B 22) = 1 :=
  (norm_of_tower _ _ _ normL8_22 norm_22).trans (by norm_num)

theorem B_norm_23 : Algebra.norm ℚ (B 23) = 1 :=
  (norm_of_tower _ _ _ normL8_23 norm_23).trans (by norm_num)

theorem B_norm (j : Fin 24) :
    Algebra.norm ℚ (B j) = ![-2, 5, 5, 5, 5, 5, 5, 5, -7, -7, -7, -7, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] j := by
  fin_cases j
  exacts [B_norm_0, B_norm_1, B_norm_2, B_norm_3, B_norm_4, B_norm_5, B_norm_6, B_norm_7, B_norm_8, B_norm_9, B_norm_10, B_norm_11, B_norm_12, B_norm_13, B_norm_14, B_norm_15, B_norm_16, B_norm_17, B_norm_18, B_norm_19, B_norm_20, B_norm_21, B_norm_22, B_norm_23]

end X2Y5Z7
