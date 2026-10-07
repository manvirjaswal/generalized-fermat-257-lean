import X2Y5Z7.Residue.Clearing
import X2Y5Z7.Fields.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-! # Residue maps of the ring of integers of `L8`

`a8 = a ∈ 𝓞 L8` has minimal polynomial `hZ` over `ℤ`. Since `a` generates `L8`, the element `D8 = h'(a)` lies in the
conductor of `ℤ[a]` (Mathlib's `conductor_mul_differentIdeal`), so `D8 · 𝓞 L8 ⊆ ℤ[a]`. Hence for a field `k` and a root
`α ∈ k` of `h` with `h'(α) ≠ 0`, the homomorphism `ℤ[a] → k`, `a ↦ α`, extends uniquely to `res8 : 𝓞 L8 →+* k`. -/

namespace X2Y5Z7

open Polynomial NumberField

noncomputable section

theorem hZ_map : hZ.map (algebraMap ℤ ℚ) = h := by rw [h, algebraMap_int_eq]

theorem a_root : aeval a h = 0 := by
  have : aeval (AdjoinRoot.root h) h = 0 := AdjoinRoot.aeval_eq h ▸ AdjoinRoot.mk_self
  exact this

theorem a_isIntegral : IsIntegral ℤ a := by
  refine ⟨hZ, hZ_monic, ?_⟩
  have h0 : eval₂ (algebraMap ℚ L8) a (hZ.map (Int.castRingHom ℚ)) = 0 := by
    have := a_root
    rw [aeval_def] at this
    exact this
  rw [eval₂_map] at h0
  have e : (algebraMap ℚ L8).comp (Int.castRingHom ℚ) = algebraMap ℤ L8 := RingHom.ext_int _ _
  rwa [e] at h0

/-- `a` as an element of the ring of integers of `L8`. -/
def a8 : 𝓞 L8 := ⟨a, a_isIntegral⟩

@[simp] theorem coe_a8 : ((a8 : 𝓞 L8) : L8) = a := rfl

theorem a8_isIntegral : IsIntegral ℤ a8 := Algebra.IsIntegral.isIntegral a8

theorem minpoly_a : minpoly ℚ a = h := by
  have hmonic : h.Monic := by rw [← hZ_map]; exact hZ_monic.map _
  exact (minpoly.eq_of_irreducible_of_monic h_irreducible a_root hmonic).symm

theorem minpoly_a8 : minpoly ℤ a8 = hZ := by
  have e1 : minpoly ℤ a8 = minpoly ℤ (a8 : L8) :=
    (minpoly.algHom_eq (IsScalarTower.toAlgHom ℤ (𝓞 L8) L8) (IsFractionRing.injective (𝓞 L8) L8) a8).symm
  rw [e1, coe_a8]
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (IsFractionRing.injective ℤ ℚ)
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ a_isIntegral, minpoly_a, hZ_map]

theorem adjoin_a8_eq_top : Algebra.adjoin ℚ {algebraMap (𝓞 L8) L8 a8} = ⊤ := by
  change Algebra.adjoin ℚ {AdjoinRoot.root h} = ⊤
  exact AdjoinRoot.adjoinRoot_eq_top

/-- The clearing element `h'(a)`. -/
def D8 : 𝓞 L8 := aeval a8 (derivative hZ)

theorem D8_mem_conductor : D8 ∈ conductor ℤ a8 := by
  have he := conductor_mul_differentIdeal ℤ ℚ L8 a8 adjoin_a8_eq_top
  have hle : conductor ℤ a8 * differentIdeal ℤ (𝓞 L8) ≤ conductor ℤ a8 := Ideal.mul_le_left
  rw [he, minpoly_a8] at hle
  exact hle (Ideal.subset_span (Set.mem_singleton _))

theorem D8_clears (z : 𝓞 L8) : D8 * z ∈ Algebra.adjoin ℤ {a8} :=
  (mem_conductor_iff.mp D8_mem_conductor) z

theorem D8_mem : D8 ∈ Algebra.adjoin ℤ {a8} := by simpa using D8_clears 1

variable {k : Type*} [Field k]

/-- The homomorphism `ℤ[a] → k`, `a ↦ α`, for a root `α` of `h`. -/
def ordRes8 (α : k) (hα : eval₂ (Int.castRingHom k) α hZ = 0) : Algebra.adjoin ℤ {a8} →+* k :=
  (AdjoinRoot.lift (Int.castRingHom k) α (by rw [minpoly_a8]; exact hα)).comp
    (minpoly.equivAdjoin a8_isIntegral).symm.toRingEquiv.toRingHom

theorem equivAdjoin_a8_root :
    minpoly.equivAdjoin a8_isIntegral (AdjoinRoot.root (minpoly ℤ a8)) =
      ⟨a8, Algebra.self_mem_adjoin_singleton ℤ a8⟩ := by
  rw [minpoly.coe_equivAdjoin, ← AdjoinRoot.mk_X]
  exact Subtype.ext (AdjoinRoot.Minpoly.coe_toAdjoin_mk_X (R := ℤ) (x := a8))

theorem ordRes8_gen (α : k) (hα : eval₂ (Int.castRingHom k) α hZ = 0) :
    ordRes8 α hα ⟨a8, Algebra.self_mem_adjoin_singleton ℤ a8⟩ = α := by
  have : (minpoly.equivAdjoin a8_isIntegral).symm ⟨a8, Algebra.self_mem_adjoin_singleton ℤ a8⟩ =
      AdjoinRoot.root (minpoly ℤ a8) := by
    rw [AlgEquiv.symm_apply_eq, equivAdjoin_a8_root]
  simp only [ordRes8, RingHom.coe_comp, Function.comp_apply]
  erw [this]
  exact AdjoinRoot.lift_root _

theorem ordRes8_aeval (α : k) (hα : eval₂ (Int.castRingHom k) α hZ = 0) (p : ℤ[X]) :
    ordRes8 α hα ⟨aeval a8 p, aeval_mem_adjoin_singleton ℤ a8⟩ = eval₂ (Int.castRingHom k) α p := by
  have e : (⟨aeval a8 p, aeval_mem_adjoin_singleton ℤ a8⟩ : Algebra.adjoin ℤ {a8}) =
      aeval (⟨a8, Algebra.self_mem_adjoin_singleton ℤ a8⟩ : Algebra.adjoin ℤ {a8}) p := by
    apply Subtype.ext
    simp [aeval_subalgebra_coe]
  rw [e, aeval_def, hom_eval₂, ordRes8_gen]
  congr 1
  exact RingHom.ext_int _ _

theorem ordRes8_D8_ne (α : k) (hα : eval₂ (Int.castRingHom k) α hZ = 0)
    (hD : eval₂ (Int.castRingHom k) α (derivative hZ) ≠ 0) : ordRes8 α hα ⟨D8, D8_mem⟩ ≠ 0 := by
  have e : (⟨D8, D8_mem⟩ : Algebra.adjoin ℤ {a8}) =
      ⟨aeval a8 (derivative hZ), aeval_mem_adjoin_singleton ℤ a8⟩ := rfl
  rw [e, ordRes8_aeval]
  exact hD

/-- The residue map of `𝓞 L8` attached to a simple root `α` of `h` in a field. -/
def res8 (α : k) (hα : eval₂ (Int.castRingHom k) α hZ = 0)
    (hD : eval₂ (Int.castRingHom k) α (derivative hZ) ≠ 0) : 𝓞 L8 →+* k :=
  extendByClearing (Algebra.adjoin ℤ {a8}) (ordRes8 α hα) ⟨D8, D8_mem⟩ (ordRes8_D8_ne α hα hD) D8_clears

theorem res8_a8 (α : k) (hα : eval₂ (Int.castRingHom k) α hZ = 0)
    (hD : eval₂ (Int.castRingHom k) α (derivative hZ) ≠ 0) : res8 α hα hD a8 = α := by
  have := extendByClearing_coe (Algebra.adjoin ℤ {a8}) (ordRes8 α hα) ⟨D8, D8_mem⟩ (ordRes8_D8_ne α hα hD)
    D8_clears ⟨a8, Algebra.self_mem_adjoin_singleton ℤ a8⟩
  rw [ordRes8_gen] at this
  exact this

/-- A ring homomorphism out of `𝓞 L8` evaluated on `p(a)`. -/
theorem ringHom_aeval_a8 (f : 𝓞 L8 →+* k) (p : ℤ[X]) :
    f (aeval a8 p) = eval₂ (Int.castRingHom k) (f a8) p := by
  rw [aeval_def, hom_eval₂]
  congr 1
  exact RingHom.ext_int _ _

/-- Uniqueness: a ring homomorphism `𝓞 L8 → k` is determined by the image of `a`, if `h'` does not vanish there. -/
theorem ringHom_L8_ext (f g : 𝓞 L8 →+* k) (hfg : f a8 = g a8)
    (hD : eval₂ (Int.castRingHom k) (f a8) (derivative hZ) ≠ 0) : f = g := by
  apply ringHom_eq_of_clearing (Algebra.adjoin ℤ {a8}) f g D8 D8_clears (by rw [D8, ringHom_aeval_a8]; exact hD)
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.mp hx]; exact hfg
  | algebraMap r => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]

theorem res8_unique (α : k) (hα : eval₂ (Int.castRingHom k) α hZ = 0)
    (hD : eval₂ (Int.castRingHom k) α (derivative hZ) ≠ 0) (f : 𝓞 L8 →+* k) (hf : f a8 = α) :
    f = res8 α hα hD :=
  ringHom_L8_ext f _ (by rw [hf, res8_a8]) (by rw [hf]; exact hD)

end

end X2Y5Z7
