import X2Y5Z7.ResidueSymbols.Symbols

/-! # The conditions at one auxiliary prime

`AuxAt P I E`: the element `E` is a unit at the primes `P k` of `L₂₄` above an auxiliary prime `q`, and its vector
of fifth-power residue symbols lies in `I`. If the symbols of `E` are `Σ c_j χ(B_j)`, this says `M c ∈ I` for the
symbol matrix `M` of the `B_j` (`mulVec_mem`). -/

namespace X2Y5Z7.Main

open NumberField X2Y5Z7.FiniteFields X2Y5Z7.ResidueSymbols Matrix

noncomputable section

/-- The conclusion of Corollary 5.5 (`q ∤ XYZ`) and Proposition 5.3 at one auxiliary prime: `E` is a unit at every prime above `q` and
its vector of symbols lies in `I`. -/
def AuxAt {m : ℕ} (P : Fin m → L24Prime) (I : Finset (Fin m → ZMod 5)) (E : L24ˣ) : Prop :=
  ∃ hE : ∀ k, E ∈ vU (P k), (fun k => Multiplicative.toAdd (symU (P k) ⟨E, hE k⟩)) ∈ I

/-- Matching the symbol vector with `M c`. -/
theorem mulVec_mem {m : ℕ} (P : Fin m → L24Prime) (M : Matrix (Fin m) (Fin 24) (ZMod 5))
    (hM : ∀ k j, (P k).sym ((P k).imgB j) = M k j) (I : Finset (Fin m → ZMod 5)) (E : L24ˣ)
    (c : Fin 24 → ZMod 5)
    (hc : ∀ (D : L24Prime) (h : E ∈ vU D),
      Multiplicative.toAdd (symU D ⟨E, h⟩) = ∑ j, c j * D.sym (D.imgB j))
    (hA : AuxAt P I E) : M *ᵥ c ∈ I := by
  obtain ⟨hE, hI⟩ := hA
  convert hI using 1
  funext k
  rw [hc (P k) (hE k)]
  simp only [Matrix.mulVec, dotProduct, hM, mul_comm]

end

end X2Y5Z7.Main
