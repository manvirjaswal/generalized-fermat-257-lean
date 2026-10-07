module

public import X2Y5Z7.FiniteFields.Model
public import X2Y5Z7.Residue.L24

@[expose] public section

/-! # Residue maps from the finite-field models

The facts of `L8Prime` and `L24Prime` in the form required by `res8` and `res24` (`X2Y5Z7/Residue/L8.lean`,
`X2Y5Z7/Residue/L24.lean`): `h(α) = 0`, `h'(α) ≠ 0` as `eval₂ (Int.castRingHom K) α hZ`, and `m₅(β₅) = 0`,
`m₅'(β₅) ≠ 0` for `β₅ = 5β`. The conversion lemmas `eval₂_hZ`, `eval₂_derivative_hZ`, `eval₂_m5Z_five`,
`eval₂_derivative_m5Z` relate them to `P1.eval`. Each model gives the residue maps `L8Prime.res : 𝓞 L8 →+* k` and
`L24Prime.res8 : 𝓞 L8 →+* K`, `L24Prime.res : 𝓞 L24 →+* K` (`a ↦ α`, `5b ↦ 5β`). -/

namespace X2Y5Z7.FiniteFields

open Polynomial NumberField

section Conversion

variable {R : Type*} [CommRing R]

theorem eval₂_hZ (x : R) : eval₂ (Int.castRingHom R) x hZ = P1.eval x hP1 := by
  rw [P1_eval_hP1]; simp [hZ, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_ofNat]

theorem eval₂_derivative_hZ (x : R) : eval₂ (Int.castRingHom R) x (derivative hZ) = P1.eval x hP1d := by
  simp [hZ, hP1d, P1.eval, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X]
  ring

theorem eval₂_m5Z_five (y : R) : eval₂ (Int.castRingHom R) (5 * y) m5Z = 5 * P1.eval y psiP1 := by
  rw [eval₂_m5Z]; simp [psiP1, P1.eval]; ring

theorem eval₂_derivative_m5Z (y : R) : eval₂ (Int.castRingHom R) y (derivative m5Z) = P1.eval y m5dP1 := by
  simp [m5Z, m5dP1, P1.eval, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X]
  ring

end Conversion

namespace L8Prime

variable (D : L8Prime)

theorem hZ_x : eval₂ (Int.castRingHom D.K) D.x hZ = 0 := by rw [eval₂_hZ]; exact D.h_x

theorem hZd_x : eval₂ (Int.castRingHom D.K) D.x (derivative hZ) ≠ 0 := by
  rw [eval₂_derivative_hZ]; exact D.hd_x

/-- The residue map `𝓞 L8 → k_i`, `a ↦ x`. -/
noncomputable def res : 𝓞 L8 →+* D.K := res8 D.x D.hZ_x D.hZd_x

theorem res_a8 : D.res a8 = D.x := res8_a8 _ _ _

end L8Prime

namespace L24Prime

variable (D : L24Prime)

theorem hZ_α : eval₂ (Int.castRingHom D.K) D.α hZ = 0 := by rw [eval₂_hZ]; exact D.h_α

theorem hZd_α : eval₂ (Int.castRingHom D.K) D.α (derivative hZ) ≠ 0 := by
  rw [eval₂_derivative_hZ]; exact D.hd_α

theorem m5Z_β5 : eval₂ (Int.castRingHom D.K) (5 * D.β) m5Z = 0 := by
  rw [eval₂_m5Z_five, D.psi_β, mul_zero]

theorem m5Zd_β5 : eval₂ (Int.castRingHom D.K) (5 * D.β) (derivative m5Z) ≠ 0 := by
  rw [eval₂_derivative_m5Z]; exact D.m5d_β

/-- The residue map `𝓞 L8 → K`, `a ↦ α`. -/
noncomputable def res8 : 𝓞 L8 →+* D.K := X2Y5Z7.res8 D.α D.hZ_α D.hZd_α

/-- The residue map `𝓞 L24 → K`, extending `res8`, with `5b ↦ 5β`. -/
noncomputable def res : 𝓞 L24 →+* D.K := res24 D.res8 (5 * D.β) D.m5Z_β5 D.m5Zd_β5

theorem res_b5 : D.res b5 = 5 * D.β := res24_b5 _ _ _ _

theorem res_algebraMap (y : 𝓞 L8) : D.res (algebraMap (𝓞 L8) (𝓞 L24) y) = D.res8 y := res24_algebraMap _ _ _ _ y

theorem res_a8 : D.res (algebraMap (𝓞 L8) (𝓞 L24) a8) = D.α := by
  rw [res_algebraMap]; exact res8_a8 _ _ _

end L24Prime

end X2Y5Z7.FiniteFields
