module

public import X2Y5Z7.FiniteFields.Residue

@[expose] public section

/-! # Proposition 5.3: compatibility of the embeddings with the residue maps

`iota_res`: a ring homomorphism `φ : k_i → K` between the models of a prime of `L8` and a prime of `L24` with
`φ x = α` commutes with the residue maps: `φ (res₈ y) = res₂₄ (y)` for `y ∈ 𝓞 L8` (both are ring homomorphisms
`𝓞 L8 → K` sending `a ↦ α`, and `h'(α) ≠ 0`, so `ringHom_L8_ext` applies). -/

namespace X2Y5Z7.SymbolSets

open X2Y5Z7.FiniteFields NumberField

theorem iota_res (D8 : L8Prime) (D24 : L24Prime) (φ : D8.K →+* D24.K) (hφ : φ D8.x = D24.α) (y : 𝓞 L8) :
    φ (D8.res y) = D24.res (algebraMap (𝓞 L8) (𝓞 L24) y) := by
  have h := ringHom_L8_ext (φ.comp D8.res) (D24.res.comp (algebraMap (𝓞 L8) (𝓞 L24)))
    (by rw [RingHom.comp_apply, RingHom.comp_apply, L8Prime.res_a8, hφ, L24Prime.res_a8])
    (by rw [RingHom.comp_apply, L8Prime.res_a8, hφ]; exact D24.hZd_α)
  exact RingHom.congr_fun h y

end X2Y5Z7.SymbolSets
