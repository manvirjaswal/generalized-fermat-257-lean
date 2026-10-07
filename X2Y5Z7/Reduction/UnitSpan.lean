import X2Y5Z7.Units.Signature

/-! # Units of `𝓞 L₂₄` modulo fifth powers

By Dirichlet's unit theorem every unit is `ζ · ∏ εᵢ^{nᵢ}` with `ζ` a root of unity and `ε₁, …, ε₁₂` a
fundamental system (`L24_unit_rank`). Raising to the fifth power is injective on the finite group of roots of
unity (`L24_unit_fifth_root_eq_one`), hence bijective, so `ζ` is a fifth power. Therefore
`(𝓞 L₂₄)ˣ / fifth powers` has at most `5¹²` elements.

`units_span`: if twelve units `B₁, …, B₁₂` have independent images under some homomorphisms
`χ_k : (𝓞 L₂₄)ˣ → ℤ/5` (a matrix `N = (χ_k(B_j))` with a left inverse), then the classes of
`∏ B_j^{c_j}`, `c ∈ (ℤ/5)¹²`, are `5¹²` distinct classes, so they are all the classes: every unit is
`∏ B_j^{c_j} · w⁵`. -/

namespace X2Y5Z7.UnitSpan

open NumberField NumberField.Units

noncomputable section

/-- The unit group of `𝓞 L₂₄`. -/
abbrev U := (𝓞 L24)ˣ

/-- Units modulo fifth powers. -/
abbrev Q := U ⧸ (powMonoidHom 5 : U →* U).range

/-- Every root of unity of `L₂₄` is a fifth power of a root of unity. -/
theorem torsion_fifth_power (ζ : torsion L24) : ∃ w : U, (ζ : U) = w ^ 5 := by
  have hinj : Function.Injective (powMonoidHom 5 : torsion L24 →* torsion L24) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply Subtype.ext
    apply L24_unit_fifth_root_eq_one
    simpa using congrArg Subtype.val hx
  obtain ⟨w, hw⟩ := Finite.injective_iff_surjective.mp hinj ζ
  exact ⟨w, by rw [← hw]; simp⟩

/-- `f^m = f^(m mod 5) · (f^(m div 5))⁵`. -/
theorem zpow_eq_pow_val_mul (f : U) (m : ℤ) :
    f ^ m = f ^ ((m : ZMod 5).val) * (f ^ (m / 5)) ^ 5 := by
  rw [← zpow_natCast, ← zpow_natCast (f ^ (m / 5)), ← zpow_mul, ← zpow_add, ZMod.val_intCast]
  congr 1
  push_cast
  lia

/-- Every unit is a product of powers `< 5` of the fundamental units times a fifth power. -/
theorem exists_fund_rep (u : U) :
    ∃ c : Fin (rank L24) → ZMod 5, ∃ w : U,
      u = (∏ i, fundSystem L24 i ^ (c i).val) * w ^ 5 := by
  obtain ⟨⟨ζ, n⟩, hu, -⟩ := exist_unique_eq_mul_prod L24 u
  obtain ⟨w₀, hw₀⟩ := torsion_fifth_power ζ
  refine ⟨fun i => (n i : ZMod 5), w₀ * ∏ i, fundSystem L24 i ^ (n i / 5), ?_⟩
  rw [hu, hw₀, Finset.prod_congr rfl (fun i _ => zpow_eq_pow_val_mul (fundSystem L24 i) (n i)),
    Finset.prod_mul_distrib, Finset.prod_pow, mul_pow]
  simp only [mul_comm (w₀ ^ 5), mul_assoc]

/-- There are at most `5¹²` units modulo fifth powers. -/
theorem card_Q_le : Nat.card Q ≤ 5 ^ 12 ∧ Finite Q := by
  let g : (Fin (rank L24) → ZMod 5) → Q := fun c =>
    QuotientGroup.mk (∏ i, fundSystem L24 i ^ (c i).val)
  have hg : Function.Surjective g := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H u =>
      obtain ⟨c, w, hu⟩ := exists_fund_rep u
      refine ⟨c, QuotientGroup.eq.mpr ⟨w, ?_⟩⟩
      simp [hu]
  have hfin : Finite Q := Finite.of_surjective g hg
  refine ⟨?_, hfin⟩
  calc Nat.card Q ≤ Nat.card (Fin (rank L24) → ZMod 5) := Nat.card_le_card_of_surjective g hg
    _ = 5 ^ 12 := by simp [L24_unit_rank]

/-- The image of a product of powers under a homomorphism to `ℤ/5`. -/
theorem toAdd_prod_pow {n : ℕ} (χ : U →* Multiplicative (ZMod 5)) (B : Fin n → U)
    (c : Fin n → ZMod 5) :
    Multiplicative.toAdd (χ (∏ j, B j ^ (c j).val)) =
      ∑ j, c j * Multiplicative.toAdd (χ (B j)) := by
  simp [map_prod, toAdd_prod, toAdd_pow, nsmul_eq_mul]

/-- **Spanning criterion.** Twelve units with independent symbol vectors span the units modulo fifth
powers. -/
theorem units_span {m : ℕ} (B : Fin 12 → U) (χ : Fin m → U →* Multiplicative (ZMod 5))
    (N : Matrix (Fin m) (Fin 12) (ZMod 5))
    (hN : ∀ k j, Multiplicative.toAdd (χ k (B j)) = N k j)
    (L : Matrix (Fin 12) (Fin m) (ZMod 5)) (hL : L * N = 1) (u : U) :
    ∃ c : Fin 12 → ZMod 5, ∃ w : U, u = (∏ j, B j ^ (c j).val) * w ^ 5 := by
  let φ : (Fin 12 → ZMod 5) → Q := fun c => QuotientGroup.mk (∏ j, B j ^ (c j).val)
  have hφ : Function.Injective φ := by
    intro c c' hcc
    obtain ⟨w, hw⟩ := QuotientGroup.eq.mp hcc
    have hNc : N.mulVec c = N.mulVec c' := by
      funext k
      have h := congrArg (fun x => Multiplicative.toAdd (χ k x)) hw
      simp only [powMonoidHom_apply, map_pow, toAdd_pow, map_mul, map_inv, toAdd_mul,
        toAdd_inv, toAdd_prod_pow, hN] at h
      have h5 : (5 : ℕ) • Multiplicative.toAdd (χ k w) = 0 := by
        rw [nsmul_eq_mul]
        exact mul_eq_zero_of_left (by decide) _
      rw [h5] at h
      simp only [Matrix.mulVec, dotProduct]
      simp only [mul_comm (N k _)]
      linear_combination h
    calc c = (L * N).mulVec c := by rw [hL, Matrix.one_mulVec]
      _ = (L * N).mulVec c' := by rw [← Matrix.mulVec_mulVec, hNc, Matrix.mulVec_mulVec]
      _ = c' := by rw [hL, Matrix.one_mulVec]
  obtain ⟨hcard, hfin⟩ := card_Q_le
  have hbij := hφ.bijective_of_nat_card_le (by simpa [Nat.card_pi] using hcard)
  obtain ⟨c, hc⟩ := hbij.2 (QuotientGroup.mk u)
  obtain ⟨w, hw⟩ := QuotientGroup.eq.mp hc
  refine ⟨c, w, ?_⟩
  simp only [powMonoidHom_apply] at hw
  rw [hw]
  group

end

end X2Y5Z7.UnitSpan
