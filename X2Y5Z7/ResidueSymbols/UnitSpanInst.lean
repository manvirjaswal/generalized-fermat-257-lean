import X2Y5Z7.ResidueSymbols.Symbols
import X2Y5Z7.Reduction.UnitSpan
import X2Y5Z7.FiniteFields.Q181
import X2Y5Z7.FiniteFields.Q311

/-! # The units `B₁₃, …, B₂₄` span the units of `𝓞 L₂₄` modulo fifth powers

We apply `UnitSpan.units_span` with the 22 symbols at the primes of `L₂₄` above `181` and `311`: the matrix
`N` of the symbols of `B₁₃, …, B₂₄` there (columns 13–24 of `M₁₈₁` and `M₃₁₁`) has the explicit left inverse
`Linv` (`Linv_mul_N`, checked by `decide`). -/

namespace X2Y5Z7.ResidueSymbols

open NumberField X2Y5Z7.FiniteFields

noncomputable section

/-- Column `12 + j` of the symbol matrices. -/
def col (j : Fin 12) : Fin 24 := ⟨12 + j.val, by omega⟩

/-- The 22 symbol maps at the primes above 181 and 311. -/
def χ22 (k : Fin 22) : (𝓞 L24)ˣ →* Multiplicative (ZMod 5) :=
  Fin.addCases (fun i : Fin 11 => symO (Q181.L24P i)) (fun i : Fin 11 => symO (Q311.L24P i)) k

/-- The symbols of `B₁₃, …, B₂₄` at these primes. -/
def N22 : Matrix (Fin 22) (Fin 12) (ZMod 5) :=
  Matrix.of fun k j => Fin.addCases (fun i : Fin 11 => Q181.M i (col j)) (fun i : Fin 11 => Q311.M i (col j)) k

/-- A left inverse of `N22` over `F₅` (computed in Python, checked below). -/
def Linv : Matrix (Fin 12) (Fin 22) (ZMod 5) :=
  !![0, 3, 3, 0, 1, 3, 1, 2, 4, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 1, 1, 2, 0, 2, 2, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0;
    3, 1, 4, 3, 2, 2, 0, 2, 2, 1, 0, 3, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 3, 2, 3, 3, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 3, 1, 3, 4, 0, 2, 3, 0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0;
    4, 0, 4, 3, 3, 1, 4, 4, 0, 1, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0;
    2, 3, 4, 4, 0, 0, 2, 1, 2, 3, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    2, 2, 2, 0, 0, 4, 1, 3, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    2, 3, 1, 2, 1, 4, 0, 4, 0, 4, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    2, 2, 1, 4, 2, 0, 0, 0, 4, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0;
    3, 4, 4, 1, 1, 2, 4, 4, 4, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0;
    3, 4, 1, 0, 4, 2, 2, 3, 4, 4, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0]

theorem Linv_mul_N : Linv * N22 = 1 := by
  decide +kernel

/-- **Unit spanning for `L₂₄`.** Given integral `B_j` (`Bx j = B j`) with `B₁₃, …, B₂₄` units, every unit of
`𝓞 L₂₄` is `∏_{j} B_{13+j}^{c_j} · w⁵`. -/
theorem units_span_B (Bx : Fin 24 → 𝓞 L24) (hBx : ∀ j, ((Bx j : 𝓞 L24) : L24) = B j)
    (hU : ∀ j : Fin 12, IsUnit (Bx (col j))) (u : (𝓞 L24)ˣ) :
    ∃ c : Fin 12 → ZMod 5, ∃ w : (𝓞 L24)ˣ, u = (∏ j, (hU j).unit ^ (c j).val) * w ^ 5 := by
  refine UnitSpan.units_span (fun j => (hU j).unit) χ22 N22 ?_ Linv Linv_mul_N u
  intro k j
  have hres : ∀ D : L24Prime, Multiplicative.toAdd (symO D (hU j).unit) = D.sym (D.imgB (col j)) := by
    intro D
    rw [symO_apply, IsUnit.unit_spec, res_B D (col j) (Bx (col j)) (hBx _)]
  refine Fin.addCases (m := 11) (n := 11)
    (motive := fun k : Fin (11 + 11) => Multiplicative.toAdd (χ22 k (hU j).unit) = N22 k j)
    (fun i => ?_) (fun i => ?_) k
  · simp only [χ22, N22, Fin.addCases_left, Matrix.of_apply]
    rw [hres, Q181.sym_M]
  · simp only [χ22, N22, Fin.addCases_right, Matrix.of_apply]
    rw [hres, Q311.sym_M]

end

end X2Y5Z7.ResidueSymbols
