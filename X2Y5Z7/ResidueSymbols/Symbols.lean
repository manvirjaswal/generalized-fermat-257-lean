module

public import X2Y5Z7.ResidueSymbols.Models
public import X2Y5Z7.Residue.Local

@[expose] public section

/-! # Fifth-power symbols of `𝔔`-units at the model primes

For a model prime `D : FiniteFields.L24Prime`, `vU D` is the group of `𝔔`-units of `L₂₄` (`Residue/Local.lean`) and
`symU D : vU D →* Multiplicative (ℤ/5)` is the fifth-power residue symbol of the residue. On the units of
`𝓞 L₂₄` this gives `symO D`.

`symU_of_prod`: if `E = ∏ B_j^{c_j} · y⁵` is a `𝔔`-unit, its symbol is `Σ c_j · sym(B_j(α, β))`. -/

namespace X2Y5Z7.ResidueSymbols

open NumberField X2Y5Z7.FiniteFields

noncomputable section

variable (D : L24Prime)

theorem res_ker_ne_bot : RingHom.ker D.res ≠ ⊥ := by
  intro h
  have hq : ((D.q : ℕ) : 𝓞 L24) ∈ RingHom.ker D.res := by
    rw [RingHom.mem_ker, map_natCast, D.char]
  rw [h, Ideal.mem_bot] at hq
  exact (Nat.cast_ne_zero.mpr D.prime.ne_zero) hq

/-- The `𝔔`-units of `L₂₄` at the model prime `D`. -/
abbrev vU : Subgroup L24ˣ := vUnits D.res (res_ker_ne_bot D)

/-- The fifth-power symbol of a `𝔔`-unit. -/
def symU : vU D →* Multiplicative (ZMod 5) where
  toFun x := Multiplicative.ofAdd (D.sym (resHom D.res (res_ker_ne_bot D) x : D.K))
  map_one' := by
    rw [map_one, Units.val_one, D.sym_one, ofAdd_zero]
  map_mul' x y := by
    rw [map_mul, Units.val_mul, D.sym_mul (Units.ne_zero _) (Units.ne_zero _), ofAdd_add]

theorem symU_apply (x : vU D) :
    Multiplicative.toAdd (symU D x) = D.sym (locRes D.res (res_ker_ne_bot D) ((x : L24ˣ) : L24)) := rfl

/-- An element of `𝓞 L₂₄` with nonzero residue is a `𝔔`-unit, with residue `D.res z`. -/
theorem mem_vU_of_res_ne (z : 𝓞 L24) (hz : D.res z ≠ 0) (u : L24ˣ) (hu : (u : L24) = algebraMap (𝓞 L24) L24 z) :
    u ∈ vU D ∧ locRes D.res (res_ker_ne_bot D) (u : L24) = D.res z := by
  rw [hu]
  exact ⟨(mem_vUnits _ _ u).mpr (by rw [hu]; exact (vRes_algebraMap_eq_one_iff _ _ z).mpr hz),
    locRes_algebraMap _ _ z⟩

/-- The symbol on the units of `𝓞 L₂₄`. -/
def symO : (𝓞 L24)ˣ →* Multiplicative (ZMod 5) :=
  (symU D).comp
    { toFun := fun u => ⟨Units.map (algebraMap (𝓞 L24) L24 : 𝓞 L24 →* L24) u,
        (mem_vU_of_res_ne D u (by
          intro h0
          have := congrArg D.res u.mul_inv
          rw [map_mul, h0, zero_mul, map_one] at this
          exact zero_ne_one this) _ rfl).1⟩
      map_one' := by ext; simp
      map_mul' := fun u v => by ext; simp }

theorem symO_apply (u : (𝓞 L24)ˣ) : Multiplicative.toAdd (symO D u) = D.sym (D.res u) := by
  have hne : D.res u ≠ 0 := by
    intro h0
    have := congrArg D.res u.mul_inv
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  change D.sym (locRes D.res (res_ker_ne_bot D) (algebraMap (𝓞 L24) L24 u)) = _
  rw [locRes_algebraMap]

/-- **Symbols of products.** If `B_j` are integral with `B_j = Bu_j` in `L₂₄ˣ` and
`E = ∏ Bu_j^{c_j} · y⁵` is a `𝔔`-unit, then `sym(E) = Σ c_j sym(B_j(α, β))`. -/
theorem symU_of_prod (Bx : Fin 24 → 𝓞 L24) (hBx : ∀ j, ((Bx j : 𝓞 L24) : L24) = B j)
    (Bu : Fin 24 → L24ˣ) (hBu : ∀ j, (Bu j : L24) = algebraMap (𝓞 L24) L24 (Bx j))
    (c : Fin 24 → ℕ) (y E : L24ˣ) (hE : E = (∏ j, Bu j ^ c j) * y ^ 5) (hEU : E ∈ vU D) :
    Multiplicative.toAdd (symU D ⟨E, hEU⟩) = ∑ j, (c j : ZMod 5) * D.sym (D.imgB j) := by
  have hres : ∀ j, D.res (Bx j) = D.imgB j := fun j => res_B D j (Bx j) (hBx j)
  have hmem : ∀ j, Bu j ∈ vU D ∧ locRes D.res (res_ker_ne_bot D) (Bu j : L24) = D.imgB j := by
    intro j
    obtain ⟨h1, h2⟩ := mem_vU_of_res_ne D (Bx j) (by rw [hres]; exact D.imgB_ne j) (Bu j) (hBu j)
    exact ⟨h1, h2.trans (hres j)⟩
  have hPU : (∏ j, Bu j ^ c j) ∈ vU D :=
    Subgroup.prod_mem _ (fun j _ => Subgroup.pow_mem _ (hmem j).1 _)
  have hy5 : y ^ 5 ∈ vU D := by
    have : y ^ 5 = (∏ j, Bu j ^ c j)⁻¹ * E := by rw [hE]; group
    rw [this]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hPU) hEU
  have hy : y ∈ vU D := mem_vUnits_of_pow _ _ y 5 (by norm_num) hy5
  have hEq : (⟨E, hEU⟩ : vU D) = (∏ j, (⟨Bu j, (hmem j).1⟩ : vU D) ^ c j) * (⟨y, hy⟩ : vU D) ^ 5 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_pow]
    exact hE
  rw [hEq, map_mul, map_pow, map_prod, toAdd_mul, toAdd_prod, toAdd_pow]
  have h5 : (5 : ℕ) • Multiplicative.toAdd (symU D ⟨y, hy⟩) = 0 := by
    rw [nsmul_eq_mul]; exact mul_eq_zero_of_left (by decide) _
  rw [h5, add_zero]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_pow, toAdd_pow, nsmul_eq_mul, symU_apply]
  simp only [(hmem j).2]

end

end X2Y5Z7.ResidueSymbols
