import X2Y5Z7.ResidueSymbols.Symbols
import X2Y5Z7.Auxiliary.Generators
import X2Y5Z7.Descent.Valuations
import X2Y5Z7.Units.RealRoots

/-! # The descent element modulo a model prime

For a solution with Putz root `θ ∈ L₈` and `w = 10Zθ ∈ 𝓞 L₈`,
`E · (10Z)^{10} = 80000 (w − 2Z·5b) (25w³ + 200Zw² + 1400Z²w + 14000Z³)³` in `𝓞 L₂₄`.
So at a model prime `D` of `L₂₄` with `10Z ≢ 0`, the residue of `E` is `80000 (t − β) ψ(t)³` with
`t = r(w)/(10Z)` (`locRes_E`), and if this is nonzero, `E` is a `𝔔`-unit whose symbol is the symbol of
that residue (`E_mem_vU`, `symU_E`). -/

namespace X2Y5Z7.ResidueSymbols

open NumberField X2Y5Z7.FiniteFields Polynomial

noncomputable section

variable {s : Solution} (R : Aux.Root s)

/-- The Putz root in `L₂₄`. -/
def θ24 : L24 := algebraMap L8 L24 R.θ

theorem θ24_root : aeval (θ24 R) (fpoly s.η) = 0 := by
  rw [θ24, aeval_algebraMap_apply, R.root, map_zero]

/-- The descent element as a unit. -/
def Eu : L24ˣ := Units.mk0 (Edesc (θ24 R)) (Edesc_ne_zero s.η (Prop31.η_ne_zero s) _ (θ24_root R))

/-- `w = 10Zθ` in `𝓞 L₂₄`. -/
def W : 𝓞 L24 := algebraMap (𝓞 L8) (𝓞 L24) R.wI

/-- The numerator of `E`. -/
def En : 𝓞 L24 :=
  80000 * (W R - 2 * (s.Z : 𝓞 L24) * b5) *
    (25 * W R ^ 3 + 200 * (s.Z : 𝓞 L24) * W R ^ 2 + 1400 * (s.Z : 𝓞 L24) ^ 2 * W R +
      14000 * (s.Z : 𝓞 L24) ^ 3) ^ 3

/-- The denominator of `E`. -/
def Ed : 𝓞 L24 := (10 * (s.Z : 𝓞 L24)) ^ 10

theorem coe_W : algebraMap (𝓞 L24) L24 (W R) = 10 * s.Z * θ24 R := by
  rw [W, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 L8) L8 L24]
  change algebraMap L8 L24 (R.wI : L8) = _
  rw [Aux.Root.coe_wI, θ24, map_mul, map_mul, map_ofNat, map_intCast]

theorem E_mul : Edesc (θ24 R) * algebraMap (𝓞 L24) L24 (Ed (s := s)) = algebraMap (𝓞 L24) L24 (En R) := by
  have hb : algebraMap (𝓞 L24) L24 b5 = 5 * b := rfl
  simp only [En, Ed, Edesc, map_mul, map_pow, map_sub, map_add, map_ofNat, map_intCast, coe_W, hb, aeval_ψ]
  ring

variable (D : L24Prime)

/-- The residue of `w/(10Z)` at `D`. -/
def tres : D.K := D.res8 R.wI / (10 * s.Z)

theorem res_W : D.res (W R) = D.res8 R.wI := by rw [W, L24Prime.res_algebraMap]

/-- The residue of `E` at `D`. -/
theorem locRes_E (h10 : (10 : D.K) * s.Z ≠ 0) :
    locRes D.res (res_ker_ne_bot D) (Edesc (θ24 R)) =
      80000 * (tres R D - D.β) * (25 * tres R D ^ 3 + 20 * tres R D ^ 2 + 14 * tres R D + 14) ^ 3 := by
  have hd : D.res (Ed (s := s)) ≠ 0 := by
    rw [Ed, map_pow, map_mul, map_ofNat, map_intCast]; exact pow_ne_zero _ h10
  rw [locRes_eq _ _ _ (En R) (Ed (s := s)) hd (E_mul R)]
  have h10' : (10 : D.K) ≠ 0 := left_ne_zero_of_mul h10
  have hZ : (s.Z : D.K) ≠ 0 := right_ne_zero_of_mul h10
  simp only [En, Ed, map_mul, map_pow, map_sub, map_add, map_ofNat, map_intCast, res_W, L24Prime.res_b5, tres]
  field_simp
  ring

/-- If the residue of `E` is nonzero, `E` is a `𝔔`-unit with that residue. -/
theorem E_mem_vU (h10 : (10 : D.K) * s.Z ≠ 0)
    (hne : 80000 * (tres R D - D.β) * (25 * tres R D ^ 3 + 20 * tres R D ^ 2 + 14 * tres R D + 14) ^ 3 ≠ 0) :
    Eu R ∈ vU D := by
  have hd : D.res (Ed (s := s)) ≠ 0 := by
    rw [Ed, map_pow, map_mul, map_ofNat, map_intCast]; exact pow_ne_zero _ h10
  have hle := vRes_le_one_of_mul_eq D.res (res_ker_ne_bot D) _ _ _ hd (E_mul R)
  rw [mem_vUnits]
  exact (locRes_ne_zero_iff _ _ _ hle).mp (by rw [locRes_E R D h10]; exact hne)

theorem symU_E (h10 : (10 : D.K) * s.Z ≠ 0) (h : Eu R ∈ vU D) :
    Multiplicative.toAdd (symU D ⟨Eu R, h⟩) =
      D.sym (80000 * (tres R D - D.β) * (25 * tres R D ^ 3 + 20 * tres R D ^ 2 + 14 * tres R D + 14) ^ 3) := by
  rw [symU_apply]
  change D.sym (locRes _ _ (Edesc (θ24 R))) = _
  rw [locRes_E R D h10]

end

end X2Y5Z7.ResidueSymbols
