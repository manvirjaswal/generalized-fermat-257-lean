import X2Y5Z7.Units.RealRoots
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-! # The signature and the unit rank of `L₂₄`

* A ring homomorphism `L₂₄ → ℝ` is determined by the images of `a` and `b`, which are real roots of `h` and
  of `ψ`. The polynomial `h` has at most two real roots and `ψ` at most one (`RealRoots.lean`), so `L₂₄` has
  at most two real places. It has one, from a real root of `h` and one of `ψ` (`AdjoinRoot.lift`, twice).
  As `r₁ + 2r₂ = 24`, `r₁` is even; so `r₁ = 2` and `r₂ = 11`.
* By Dirichlet's unit theorem the unit rank of `L₂₄` is `r₁ + r₂ - 1 = 12`.
* A real embedding sends a fifth root of unity of `L₂₄` to a real fifth root of unity, which is `1`; so
  `L₂₄` contains no fifth root of unity other than `1`. -/

namespace X2Y5Z7

open Polynomial NumberField NumberField.InfinitePlace

noncomputable section

/-! ## Ring homomorphisms out of `L₂₄` -/

/-- `a` is a root of `h`. -/
theorem a_root : aeval a h = 0 := by
  rw [aeval_def, RingHom.ext_rat (algebraMap ℚ L8) (AdjoinRoot.of h)]
  exact AdjoinRoot.eval₂_root h

/-- The image of `a` under a ring homomorphism is a root of `h`. -/
theorem aeval_ringHom_a {S : Type*} [CommRing S] [Algebra ℚ S] (f : L8 →+* S) :
    aeval (f a) h = 0 := by
  have := congrArg f a_root
  rw [aeval_h] at this ⊢
  simpa [map_ofNat] using this

/-- The image of `b` under a ring homomorphism is a root of `ψ`. -/
theorem aeval_ringHom_b {S : Type*} [CommRing S] [Algebra ℚ S] (f : L24 →+* S) :
    aeval (f b) ψ = 0 := by
  have := congrArg f b_root
  rw [aeval_ψ] at this ⊢
  simpa [map_ofNat] using this

/-- A ring homomorphism out of `L₂₄` is determined by the images of `a` and `b`. -/
theorem L24_ringHom_ext {S : Type*} [CommRing S] {σ τ : L24 →+* S}
    (ha : σ (algebraMap L8 L24 a) = τ (algebraMap L8 L24 a)) (hb : σ b = τ b) : σ = τ :=
  AdjoinRoot.ringHom_ext (AdjoinRoot.ringHom_ext (RingHom.ext_rat _ _) ha) hb

/-- `L₂₄` has a real embedding: send `a` to a real root of `h`, then `b` to a real root of `ψ`. -/
theorem exists_L24_real_embedding : Nonempty (L24 →+* ℝ) := by
  obtain ⟨r, -, -, hr⟩ := exists_h_real_root
  obtain ⟨s, -, -, hs⟩ := exists_ψ_real_root
  let σ₈ : L8 →+* ℝ := AdjoinRoot.lift (algebraMap ℚ ℝ) r (by rwa [← aeval_def])
  refine ⟨AdjoinRoot.lift σ₈ s ?_⟩
  rw [ψL8, eval₂_map, RingHom.ext_rat (σ₈.comp (algebraMap ℚ L8)) (algebraMap ℚ ℝ), ← aeval_def]
  exact hs

/-! ## The signature -/

/-- `L₂₄` has at most two real places: the real embedding at a real place is determined by the images of
`a` (a real root of `h`, on one side of `0` or the other) and `b` (the real root of `ψ`). -/
theorem L24_nrRealPlaces_le : nrRealPlaces L24 ≤ 2 := by
  classical
  let F : {w : InfinitePlace L24 // w.IsReal} → Bool :=
    fun w => decide (embedding_of_isReal w.2 (algebraMap L8 L24 a) < 0)
  have hF : Function.Injective F := by
    rintro ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ hw
    have ha := h_real_root_eq (aeval_ringHom_a ((embedding_of_isReal hw₁).comp (algebraMap L8 L24)))
      (aeval_ringHom_a ((embedding_of_isReal hw₂).comp (algebraMap L8 L24))) (decide_eq_decide.mp (by simpa [F] using hw))
    have hb := ψ_real_root_eq (aeval_ringHom_b (embedding_of_isReal hw₁))
      (aeval_ringHom_b (embedding_of_isReal hw₂))
    have hσ : embedding_of_isReal hw₁ = embedding_of_isReal hw₂ := L24_ringHom_ext ha hb
    refine Subtype.ext (embedding_injective L24 (RingHom.ext fun x => ?_))
    rw [← embedding_of_isReal_apply hw₁, ← embedding_of_isReal_apply hw₂, hσ]
  exact (Fintype.card_le_of_injective F hF).trans (by simp)

/-- `L₂₄` has a real place. -/
theorem L24_nrRealPlaces_pos : 0 < nrRealPlaces L24 := by
  classical
  obtain ⟨σ⟩ := exists_L24_real_embedding
  have hφ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    exact RingHom.ext fun x => by simp
  exact Fintype.card_pos_iff.2 ⟨⟨mk _, isReal_mk_iff.2 hφ⟩⟩

/-- `L₂₄` has exactly two real places. -/
theorem L24_nrRealPlaces : nrRealPlaces L24 = 2 := by
  have h₁ := L24_nrRealPlaces_le
  have h₂ := L24_nrRealPlaces_pos
  have h₃ := card_add_two_mul_card_eq_rank L24
  rw [L24_finrank] at h₃
  omega

/-- `L₂₄` has exactly eleven complex places. -/
theorem L24_nrComplexPlaces : nrComplexPlaces L24 = 11 := by
  have h₃ := card_add_two_mul_card_eq_rank L24
  rw [L24_finrank, L24_nrRealPlaces] at h₃
  omega

/-! ## Units -/

/-- Dirichlet's unit theorem for `L₂₄`: the unit rank is `2 + 11 - 1 = 12`. -/
theorem L24_unit_rank : NumberField.Units.rank L24 = 12 := by
  rw [NumberField.Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces, L24_nrRealPlaces,
    L24_nrComplexPlaces]

/-- `1` is the only fifth root of unity in `L₂₄`: a real embedding sends it to a real fifth root of
unity. -/
theorem L24_fifth_root_eq_one (x : L24) (hx : x ^ 5 = 1) : x = 1 := by
  obtain ⟨σ⟩ := exists_L24_real_embedding
  apply σ.injective
  have : σ x ^ 5 = σ 1 ^ 5 := by rw [← map_pow, hx, map_one, one_pow]
  exact Odd.pow_injective (by decide) this

/-- `1` is the only unit of `𝓞 L₂₄` whose fifth power is `1`. -/
theorem L24_unit_fifth_root_eq_one (u : (𝓞 L24)ˣ) (hu : u ^ 5 = 1) : u = 1 := by
  apply Units.ext
  apply RingOfIntegers.ext
  apply L24_fifth_root_eq_one
  have h := congrArg (fun v : (𝓞 L24)ˣ => ((v : 𝓞 L24) : L24)) hu
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, map_pow, map_one] using h

end

end X2Y5Z7
