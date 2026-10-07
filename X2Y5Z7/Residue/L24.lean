import X2Y5Z7.Residue.L8

/-! # Residue maps of the ring of integers of `L24`

`b5 = 5b ∈ 𝓞 L24` is a root of the monic `m₅ = X³ + 4X² + 14X + 70 = 5ψ(X/5)`, which is its minimal polynomial over
`L8` and over `𝓞 L8`. Since `5b` generates `L24` over `L8`, `D24 = m₅'(5b)` lies in the conductor of `𝓞 L8[5b]` in
`𝓞 L24`. Hence a residue map `r8 : 𝓞 L8 →+* k` and a root `β5 ∈ k` of `m₅` with `m₅'(β5) ≠ 0` give a unique
`res24 : 𝓞 L24 →+* k` extending `r8` with `5b ↦ β5`. -/

namespace X2Y5Z7

open Polynomial NumberField

noncomputable section

/-- `m₅ = X³ + 4X² + 14X + 70`, the minimal polynomial of `5b`. -/
def m5Z : ℤ[X] := X ^ 3 + 4 * X ^ 2 + 14 * X + 70

theorem m5Z_monic : m5Z.Monic := by unfold m5Z; monicity!

theorem m5Z_natDegree : m5Z.natDegree = 3 := by unfold m5Z; compute_degree!

theorem aeval_m5Z {R : Type*} [CommRing R] (y : R) : aeval y m5Z = y ^ 3 + 4 * y ^ 2 + 14 * y + 70 := by
  simp [m5Z, map_ofNat]

theorem eval₂_m5Z {R : Type*} [CommRing R] (f : ℤ →+* R) (y : R) :
    eval₂ f y m5Z = y ^ 3 + 4 * y ^ 2 + 14 * y + 70 := by
  simp [m5Z, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_ofNat]

theorem m5_root : aeval (5 * b) m5Z = 0 := by
  simp only [m5Z, map_add, map_mul, map_pow, aeval_X, map_ofNat]
  have hb : 25 * b ^ 3 + 20 * b ^ 2 + 14 * b + 14 = 0 := by
    have := b_root
    simp [ψ, ψZ, aeval_def] at this
    linear_combination this
  linear_combination 5 * hb

theorem b5_isIntegral : IsIntegral ℤ (5 * b) := ⟨m5Z, m5Z_monic, by rw [← aeval_def]; exact m5_root⟩

/-- `5b` as an element of the ring of integers of `L24`. -/
def b5 : 𝓞 L24 := ⟨5 * b, b5_isIntegral⟩

@[simp] theorem coe_b5 : ((b5 : 𝓞 L24) : L24) = 5 * b := rfl

/-- `m₅` over `L8`. -/
def m5L8 : L8[X] := m5Z.map (algebraMap ℤ L8)

theorem m5L8_monic : m5L8.Monic := m5Z_monic.map _

theorem m5L8_natDegree : m5L8.natDegree = 3 := by
  rw [m5L8, m5Z_monic.natDegree_map, m5Z_natDegree]

theorem m5L8_no_root (β : L8) : ¬ IsRoot m5L8 β := by
  intro hβ
  apply ψL8_no_root (β / 5)
  have h1 : β ^ 3 + 4 * β ^ 2 + 14 * β + 70 = 0 := by
    have := hβ
    simp only [IsRoot, m5L8, eval_map, eval₂_m5Z] at this
    exact this
  simp only [IsRoot, ψL8, ψ, ψZ, eval_map, Polynomial.map_map]
  simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_ofNat]
  linear_combination h1 / 5

theorem m5L8_irreducible : Irreducible m5L8 :=
  irreducible_of_degree_le_three_of_not_isRoot (by rw [m5L8_natDegree]; decide) m5L8_no_root

theorem m5L8_root : aeval (5 * b) m5L8 = 0 := by
  rw [m5L8, aeval_map_algebraMap]
  exact m5_root

theorem minpoly_b5_field : minpoly L8 (5 * b) = m5L8 :=
  (minpoly.eq_of_irreducible_of_monic m5L8_irreducible m5L8_root m5L8_monic).symm

theorem b5_isIntegral' : IsIntegral (𝓞 L8) b5 := Algebra.IsIntegral.isIntegral b5

theorem minpoly_b5 : minpoly (𝓞 L8) b5 = m5Z.map (algebraMap ℤ (𝓞 L8)) := by
  have e1 : minpoly (𝓞 L8) b5 = minpoly (𝓞 L8) (b5 : L24) :=
    (minpoly.algHom_eq (IsScalarTower.toAlgHom (𝓞 L8) (𝓞 L24) L24)
      (IsFractionRing.injective (𝓞 L24) L24) b5).symm
  rw [e1]
  apply Polynomial.map_injective (algebraMap (𝓞 L8) L8) (IsFractionRing.injective (𝓞 L8) L8)
  have hint : IsIntegral (𝓞 L8) (b5 : L24) := by
    refine ⟨m5Z.map (algebraMap ℤ (𝓞 L8)), m5Z_monic.map _, ?_⟩
    rw [eval₂_map]
    have e : (algebraMap (𝓞 L8) L24).comp (algebraMap ℤ (𝓞 L8)) = algebraMap ℤ L24 := RingHom.ext_int _ _
    rw [e, ← aeval_def, coe_b5]
    exact m5_root
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' L8 hint, coe_b5, minpoly_b5_field, m5L8,
    Polynomial.map_map]
  congr 1

theorem adjoin_b5_eq_top : Algebra.adjoin L8 {algebraMap (𝓞 L24) L24 b5} = ⊤ := by
  have hb : b ∈ Algebra.adjoin L8 {algebraMap (𝓞 L24) L24 b5} := by
    have h5 : (5 * b : L24) ∈ Algebra.adjoin L8 {algebraMap (𝓞 L24) L24 b5} := Algebra.subset_adjoin rfl
    have : b = algebraMap L8 L24 (1 / 5) * (5 * b) := by
      rw [map_div₀, map_one, map_ofNat]; field_simp
    rw [this]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) h5
  apply top_unique
  rw [← AdjoinRoot.adjoinRoot_eq_top (f := ψL8)]
  exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hb)

/-- The clearing element `m₅'(5b)`. -/
def D24 : 𝓞 L24 := aeval b5 (derivative (minpoly (𝓞 L8) b5))

theorem D24_mem_conductor : D24 ∈ conductor (𝓞 L8) b5 := by
  have he := conductor_mul_differentIdeal (𝓞 L8) L8 L24 b5 adjoin_b5_eq_top
  have hle : conductor (𝓞 L8) b5 * differentIdeal (𝓞 L8) (𝓞 L24) ≤ conductor (𝓞 L8) b5 := Ideal.mul_le_left
  rw [he] at hle
  exact hle (Ideal.subset_span (Set.mem_singleton _))

theorem D24_clears (z : 𝓞 L24) : D24 * z ∈ Algebra.adjoin (𝓞 L8) {b5} :=
  (mem_conductor_iff.mp D24_mem_conductor) z

theorem D24_mem : D24 ∈ Algebra.adjoin (𝓞 L8) {b5} := by simpa using D24_clears 1

variable {k : Type*} [Field k]

theorem eval₂_minpoly_b5 (r8 : 𝓞 L8 →+* k) (β5 : k) :
    eval₂ r8 β5 (minpoly (𝓞 L8) b5) = eval₂ (Int.castRingHom k) β5 m5Z := by
  rw [minpoly_b5, eval₂_map]
  congr 1
  exact RingHom.ext_int _ _

theorem eval₂_derivative_minpoly_b5 (r8 : 𝓞 L8 →+* k) (β5 : k) :
    eval₂ r8 β5 (derivative (minpoly (𝓞 L8) b5)) = eval₂ (Int.castRingHom k) β5 (derivative m5Z) := by
  rw [minpoly_b5, derivative_map, eval₂_map]
  congr 1
  exact RingHom.ext_int _ _

/-- The homomorphism `𝓞 L8[5b] → k` extending `r8`, with `5b ↦ β5`. -/
def ordRes24 (r8 : 𝓞 L8 →+* k) (β5 : k) (hβ : eval₂ (Int.castRingHom k) β5 m5Z = 0) :
    Algebra.adjoin (𝓞 L8) {b5} →+* k :=
  (AdjoinRoot.lift r8 β5 (by rw [eval₂_minpoly_b5]; exact hβ)).comp
    (minpoly.equivAdjoin b5_isIntegral').symm.toRingEquiv.toRingHom

theorem equivAdjoin_b5_root :
    minpoly.equivAdjoin b5_isIntegral' (AdjoinRoot.root (minpoly (𝓞 L8) b5)) =
      ⟨b5, Algebra.self_mem_adjoin_singleton (𝓞 L8) b5⟩ := by
  rw [minpoly.coe_equivAdjoin, ← AdjoinRoot.mk_X]
  exact Subtype.ext (AdjoinRoot.Minpoly.coe_toAdjoin_mk_X (R := 𝓞 L8) (x := b5))

theorem ordRes24_gen (r8 : 𝓞 L8 →+* k) (β5 : k) (hβ : eval₂ (Int.castRingHom k) β5 m5Z = 0) :
    ordRes24 r8 β5 hβ ⟨b5, Algebra.self_mem_adjoin_singleton (𝓞 L8) b5⟩ = β5 := by
  have : (minpoly.equivAdjoin b5_isIntegral').symm ⟨b5, Algebra.self_mem_adjoin_singleton (𝓞 L8) b5⟩ =
      AdjoinRoot.root (minpoly (𝓞 L8) b5) := by
    rw [AlgEquiv.symm_apply_eq, equivAdjoin_b5_root]
  simp only [ordRes24, RingHom.coe_comp, Function.comp_apply]
  erw [this]
  exact AdjoinRoot.lift_root _

theorem ordRes24_algebraMap (r8 : 𝓞 L8 →+* k) (β5 : k) (hβ : eval₂ (Int.castRingHom k) β5 m5Z = 0)
    (y : 𝓞 L8) : ordRes24 r8 β5 hβ (algebraMap (𝓞 L8) (Algebra.adjoin (𝓞 L8) {b5}) y) = r8 y := by
  simp only [ordRes24, RingHom.coe_comp, Function.comp_apply]
  erw [AlgEquiv.commutes]
  exact AdjoinRoot.lift_of _

theorem ordRes24_aeval (r8 : 𝓞 L8 →+* k) (β5 : k) (hβ : eval₂ (Int.castRingHom k) β5 m5Z = 0)
    (p : (𝓞 L8)[X]) :
    ordRes24 r8 β5 hβ ⟨aeval b5 p, aeval_mem_adjoin_singleton (𝓞 L8) b5⟩ = eval₂ r8 β5 p := by
  have e : (⟨aeval b5 p, aeval_mem_adjoin_singleton (𝓞 L8) b5⟩ : Algebra.adjoin (𝓞 L8) {b5}) =
      aeval (⟨b5, Algebra.self_mem_adjoin_singleton (𝓞 L8) b5⟩ : Algebra.adjoin (𝓞 L8) {b5}) p := by
    apply Subtype.ext
    simp [aeval_subalgebra_coe]
  rw [e, aeval_def, hom_eval₂, ordRes24_gen]
  congr 1
  ext y
  exact ordRes24_algebraMap r8 β5 hβ y

theorem ordRes24_D24_ne (r8 : 𝓞 L8 →+* k) (β5 : k) (hβ : eval₂ (Int.castRingHom k) β5 m5Z = 0)
    (hD : eval₂ (Int.castRingHom k) β5 (derivative m5Z) ≠ 0) : ordRes24 r8 β5 hβ ⟨D24, D24_mem⟩ ≠ 0 := by
  have e : (⟨D24, D24_mem⟩ : Algebra.adjoin (𝓞 L8) {b5}) =
      ⟨aeval b5 (derivative (minpoly (𝓞 L8) b5)), aeval_mem_adjoin_singleton (𝓞 L8) b5⟩ := rfl
  rw [e, ordRes24_aeval, eval₂_derivative_minpoly_b5]
  exact hD

/-- The residue map of `𝓞 L24` extending `r8 : 𝓞 L8 →+* k`, with `5b ↦ β5`, for a simple root `β5` of `m₅`. -/
def res24 (r8 : 𝓞 L8 →+* k) (β5 : k) (hβ : eval₂ (Int.castRingHom k) β5 m5Z = 0)
    (hD : eval₂ (Int.castRingHom k) β5 (derivative m5Z) ≠ 0) : 𝓞 L24 →+* k :=
  extendByClearing (Algebra.adjoin (𝓞 L8) {b5}) (ordRes24 r8 β5 hβ) ⟨D24, D24_mem⟩
    (ordRes24_D24_ne r8 β5 hβ hD) D24_clears

theorem res24_b5 (r8 : 𝓞 L8 →+* k) (β5 : k) (hβ : eval₂ (Int.castRingHom k) β5 m5Z = 0)
    (hD : eval₂ (Int.castRingHom k) β5 (derivative m5Z) ≠ 0) : res24 r8 β5 hβ hD b5 = β5 := by
  have := extendByClearing_coe (Algebra.adjoin (𝓞 L8) {b5}) (ordRes24 r8 β5 hβ) ⟨D24, D24_mem⟩
    (ordRes24_D24_ne r8 β5 hβ hD) D24_clears ⟨b5, Algebra.self_mem_adjoin_singleton (𝓞 L8) b5⟩
  rw [ordRes24_gen] at this
  exact this

theorem res24_algebraMap (r8 : 𝓞 L8 →+* k) (β5 : k) (hβ : eval₂ (Int.castRingHom k) β5 m5Z = 0)
    (hD : eval₂ (Int.castRingHom k) β5 (derivative m5Z) ≠ 0) (y : 𝓞 L8) :
    res24 r8 β5 hβ hD (algebraMap (𝓞 L8) (𝓞 L24) y) = r8 y := by
  have := extendByClearing_coe (Algebra.adjoin (𝓞 L8) {b5}) (ordRes24 r8 β5 hβ) ⟨D24, D24_mem⟩
    (ordRes24_D24_ne r8 β5 hβ hD) D24_clears (algebraMap (𝓞 L8) (Algebra.adjoin (𝓞 L8) {b5}) y)
  rw [ordRes24_algebraMap] at this
  exact this

/-- A ring homomorphism out of `𝓞 L24` evaluated on `p(5b)`, `p` with coefficients in `𝓞 L8`. -/
theorem ringHom_aeval_b5 (f : 𝓞 L24 →+* k) (p : (𝓞 L8)[X]) :
    f (aeval b5 p) = eval₂ (f.comp (algebraMap (𝓞 L8) (𝓞 L24))) (f b5) p := by
  rw [aeval_def, hom_eval₂]

/-- Uniqueness: a ring homomorphism `𝓞 L24 → k` is determined by its restriction to `𝓞 L8` and the image of `5b`,
if `m₅'` does not vanish there. -/
theorem ringHom_L24_ext (f g : 𝓞 L24 →+* k)
    (h8 : f.comp (algebraMap (𝓞 L8) (𝓞 L24)) = g.comp (algebraMap (𝓞 L8) (𝓞 L24))) (hb : f b5 = g b5)
    (hD : eval₂ (Int.castRingHom k) (f b5) (derivative m5Z) ≠ 0) : f = g := by
  apply ringHom_eq_of_clearing (Algebra.adjoin (𝓞 L8) {b5}) f g D24 D24_clears (by
    rw [D24, ringHom_aeval_b5, eval₂_derivative_minpoly_b5]; exact hD)
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.mp hx]; exact hb
  | algebraMap r => exact congrArg (fun φ => φ r) h8
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]

theorem res24_unique (r8 : 𝓞 L8 →+* k) (β5 : k) (hβ : eval₂ (Int.castRingHom k) β5 m5Z = 0)
    (hD : eval₂ (Int.castRingHom k) β5 (derivative m5Z) ≠ 0) (f : 𝓞 L24 →+* k)
    (h8 : f.comp (algebraMap (𝓞 L8) (𝓞 L24)) = r8) (hb : f b5 = β5) : f = res24 r8 β5 hβ hD := by
  apply ringHom_L24_ext f _ ?_ (by rw [hb, res24_b5]) (by rw [hb]; exact hD)
  rw [h8]
  ext y
  exact (res24_algebraMap r8 β5 hβ hD y).symm

end

end X2Y5Z7
