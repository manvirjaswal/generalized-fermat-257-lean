module

public import X2Y5Z7.Auxiliary.ResidueGeneration

@[expose] public section

/-! # Distinct primes give distinct minimal polynomials

If two residue maps `r₁, r₂` of `𝓞 K` onto finite fields of characteristic `q` both satisfy the derivative condition for
the generator `θ`, and `r₁ θ`, `r₂ θ` have the same minimal polynomial over `ZMod q`, then there is an isomorphism
`σ : k₁ ≃ₐ k₂` with `σ (r₁ θ) = r₂ θ`, and `σ ∘ r₁ = r₂` (they agree on `ℤ[θ]`, and `D · 𝓞 K ⊆ ℤ[θ]` with `r₂ D ≠ 0`).
Hence `ker r₁ = ker r₂`. -/

namespace X2Y5Z7.Aux

open Polynomial
open scoped NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Two ring homomorphisms from `𝓞 K` to a field that agree on `θ` agree everywhere, provided the derivative element
has nonzero image. -/
theorem ringHom_eq_of_eq_gen {L : Type*} [Field L] (θ : 𝓞 K)
    (hθ : Algebra.adjoin ℚ ({(θ : K)} : Set K) = ⊤) (f g : 𝓞 K →+* L) (hfg : f θ = g θ)
    (hd : g (derivativeInteger θ) ≠ 0) : f = g := by
  have hle : Algebra.adjoin ℤ ({θ} : Set (𝓞 K)) ≤ AlgHom.equalizer f.toIntAlgHom g.toIntAlgHom := by
    apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact hfg
  have hon (x : 𝓞 K) (hx : x ∈ Algebra.adjoin ℤ ({θ} : Set (𝓞 K))) : f x = g x := hle hx
  have hD : f (derivativeInteger θ) = g (derivativeInteger θ) := hon _ (by
    simpa only [mul_one] using derivative_clears θ 1 hθ)
  ext a
  have ha := hon _ (derivative_clears θ a hθ)
  rw [map_mul, map_mul, hD] at ha
  exact mul_left_cancel₀ hd ha

variable {q : ℕ} [Fact q.Prime]

/-- Equal minimal polynomials of the residues of `θ` force equal kernels. -/
theorem ker_eq_of_minpoly_eq (θ : 𝓞 K) (hθ : Algebra.adjoin ℚ ({(θ : K)} : Set K) = ⊤)
    {k₁ k₂ : Type*} [Field k₁] [Finite k₁] [Algebra (ZMod q) k₁]
    [Field k₂] [Finite k₂] [Algebra (ZMod q) k₂]
    (r₁ : 𝓞 K →+* k₁) (hr₁ : Function.Surjective r₁) (hd₁ : r₁ (derivativeInteger θ) ≠ 0)
    (r₂ : 𝓞 K →+* k₂) (hr₂ : Function.Surjective r₂) (hd₂ : r₂ (derivativeInteger θ) ≠ 0)
    (hm : minpoly (ZMod q) (r₁ θ) = minpoly (ZMod q) (r₂ θ)) :
    RingHom.ker r₁ = RingHom.ker r₂ := by
  let pb₁ := residueBasis (q := q) θ r₁ hr₁ hθ hd₁
  let pb₂ := residueBasis (q := q) θ r₂ hr₂ hθ hd₂
  let σ : k₁ ≃ₐ[ZMod q] k₂ := pb₁.equivOfMinpoly pb₂ hm
  have hσ : σ (r₁ θ) = r₂ θ := pb₁.equivOfMinpoly_gen pb₂ hm
  have heq : (σ : k₁ →+* k₂).comp r₁ = r₂ := ringHom_eq_of_eq_gen θ hθ _ _ hσ hd₂
  rw [← heq]
  ext a
  simp only [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply]
  exact (map_eq_zero_iff (σ : k₁ →+* k₂) σ.injective).symm

/-- **Distinctness.** Distinct primes satisfying the derivative condition give distinct minimal polynomials. -/
theorem minpoly_ne_of_ker_ne (θ : 𝓞 K) (hθ : Algebra.adjoin ℚ ({(θ : K)} : Set K) = ⊤)
    {k₁ k₂ : Type*} [Field k₁] [Finite k₁] [Algebra (ZMod q) k₁]
    [Field k₂] [Finite k₂] [Algebra (ZMod q) k₂]
    (r₁ : 𝓞 K →+* k₁) (hr₁ : Function.Surjective r₁) (hd₁ : r₁ (derivativeInteger θ) ≠ 0)
    (r₂ : 𝓞 K →+* k₂) (hr₂ : Function.Surjective r₂) (hd₂ : r₂ (derivativeInteger θ) ≠ 0)
    (hker : RingHom.ker r₁ ≠ RingHom.ker r₂) :
    minpoly (ZMod q) (r₁ θ) ≠ minpoly (ZMod q) (r₂ θ) :=
  fun hm => hker (ker_eq_of_minpoly_eq θ hθ r₁ hr₁ hd₁ r₂ hr₂ hd₂ hm)

end

end X2Y5Z7.Aux
