import X2Y5Z7.Main.AuxAt
import X2Y5Z7.Reduction.SelmerForm
import X2Y5Z7.ResidueSymbols.UnitSpanInst
import X2Y5Z7.FiniteFields.Q181
import X2Y5Z7.FiniteFields.Q311
import X2Y5Z7.FiniteFields.Q131
import X2Y5Z7.FiniteFields.Q251
import X2Y5Z7.FiniteFields.Q101
import X2Y5Z7.SymbolSets.Sets
import X2Y5Z7.Sieve.Theorem

/-! # The class of `E` in terms of the basis `B₁, …, B₂₄`

Under the class-group hypothesis, an element `E` of the Selmer group `L₂₄(S, 5)` is `∏ B_j^{e_j} · z⁵` for some
integers `e_j` and some `z ∈ L₂₄ˣ` (Proposition 6.2(ii)). The residue symbols of `E` at an auxiliary prime are then
`Σ e_j χ(B_j)`. The conditions (N), (V) and (Q) of Theorem 7.1 are statements about the vector `e mod 5`. -/

namespace X2Y5Z7.Main

open NumberField X2Y5Z7.FiniteFields X2Y5Z7.ResidueSymbols Polynomial Matrix

noncomputable section

variable {Bx : Fin 24 → 𝓞 L24} (hBx : ∀ j, ((Bx j : 𝓞 L24) : L24) = B j)
  (hB : SelmerForm.SUnitFacts Bx)

/-- The exponents of the unit part, placed in positions 13–24. -/
def lift12 (c : Fin 12 → ZMod 5) (j : Fin 24) : ℤ :=
  if h : 12 ≤ j.val then ((c ⟨j.val - 12, by omega⟩).val : ℤ) else 0

theorem prod_lift12 (c : Fin 12 → ZMod 5) (g : Fin 24 → L24) :
    ∏ j, g j ^ lift12 c j = ∏ j : Fin 12, g (ResidueSymbols.col j) ^ (c j).val := by
  change ∏ j : Fin (12 + 12), g j ^ lift12 c j = _
  rw [Fin.prod_univ_add]
  have h1 : ∀ i : Fin 12, lift12 c (Fin.castAdd 12 i) = 0 := by
    intro i; rw [lift12, dite_eq_right_iff]; intro h; simp only [Fin.val_castAdd] at h; omega
  have h2 : ∀ i : Fin 12, lift12 c (Fin.natAdd 12 i) = ((c i).val : ℤ) := by
    intro i
    simp only [lift12, Fin.val_natAdd, show 12 ≤ 12 + i.val from by omega, dite_true]
    congr 3; ext; simp
  simp only [h1, h2, zpow_zero, Finset.prod_const_one, one_mul, zpow_natCast]
  rfl

include hBx hB in
theorem B_ne_zero (j : Fin 24) : B j ≠ 0 := by
  rw [← hBx]; exact SelmerForm.algebraMap_ne_zero hB j

include hBx hB in
/-- **Proposition 6.2(ii), in the form used by the sieve.** A Selmer element is `∏ B_j^{e_j} · z⁵`. -/
theorem exists_form (hclass : ∀ c : ClassGroup (𝓞 L24), c ^ 5 = 1 → c = 1) (E : L24ˣ)
    (hE : ∀ v, v ∉ Selmer.L24SIntegers.Sprimes → (5 : ℤ) ∣ SelmerForm.cnt v E) :
    ∃ e : Fin 24 → ℤ, ∃ z : L24ˣ, (E : L24) = (∏ j, B j ^ e j) * (z : L24) ^ 5 := by
  obtain ⟨e, u, y, hEq⟩ := SelmerForm.selmer_form hB hclass E hE
  have hU : ∀ j : Fin 12, IsUnit (Bx (ResidueSymbols.col j)) :=
    fun j => hB.isUnit (ResidueSymbols.col j) (by simp [ResidueSymbols.col])
  obtain ⟨c12, w, hu⟩ := units_span_B Bx hBx hU u
  refine ⟨e + lift12 c12, y * Units.map (algebraMap (𝓞 L24) L24 : 𝓞 L24 →* L24) w, ?_⟩
  have hu' : ((Units.map (algebraMap (𝓞 L24) L24 : 𝓞 L24 →* L24) u : L24ˣ) : L24) =
      (∏ j : Fin 12, B (ResidueSymbols.col j) ^ (c12 j).val) *
        ((Units.map (algebraMap (𝓞 L24) L24 : 𝓞 L24 →* L24) w : L24ˣ) : L24) ^ 5 := by
    rw [hu]
    simp [Units.coe_map, map_prod, hBx]
  have hBu : ∀ j, ((SelmerForm.Bu hB j : L24ˣ) : L24) = B j := fun j => hBx j
  rw [hEq]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_prod, Units.val_zpow_eq_zpow_val, hBu]
  rw [hu', ← prod_lift12 c12 B]
  have hprod : (∏ j, B j ^ (e + lift12 c12) j) = (∏ j, B j ^ e j) * ∏ j, B j ^ lift12 c12 j := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [Pi.add_apply, zpow_add₀ (B_ne_zero hBx hB j)]
  rw [hprod]
  ring

include hBx hB in
/-- The residue symbols of `∏ B_j^{e_j} · z⁵` at a model prime where it is a unit. -/
theorem sym_of_form (D : L24Prime) (E : L24ˣ) (hEU : E ∈ vU D) (e : Fin 24 → ℤ) (z : L24ˣ)
    (hform : (E : L24) = (∏ j, B j ^ e j) * (z : L24) ^ 5) :
    Multiplicative.toAdd (symU D ⟨E, hEU⟩) = ∑ j, (e j : ZMod 5) * D.sym (D.imgB j) := by
  have hmem : ∀ j, SelmerForm.Bu hB j ∈ vU D ∧
      locRes D.res (res_ker_ne_bot D) (SelmerForm.Bu hB j : L24) = D.imgB j := by
    intro j
    obtain ⟨h1, h2⟩ := mem_vU_of_res_ne D (Bx j)
      (by rw [res_B D j _ (hBx j)]; exact D.imgB_ne j) (SelmerForm.Bu hB j) rfl
    exact ⟨h1, h2.trans (res_B D j _ (hBx j))⟩
  let bu : Fin 24 → vU D := fun j => ⟨SelmerForm.Bu hB j, (hmem j).1⟩
  have hsymB : ∀ j, Multiplicative.toAdd (symU D (bu j)) = D.sym (D.imgB j) := by
    intro j; rw [symU_apply]; exact congrArg D.sym (hmem j).2
  have hEq : E = (∏ j, SelmerForm.Bu hB j ^ e j) * z ^ 5 := by
    apply Units.ext
    have hBu : ∀ j, ((SelmerForm.Bu hB j : L24ˣ) : L24) = B j := fun j => hBx j
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_prod, Units.val_zpow_eq_zpow_val, hBu]
    exact hform
  have hP : (∏ j, SelmerForm.Bu hB j ^ e j) ∈ vU D :=
    Subgroup.prod_mem _ (fun j _ => Subgroup.zpow_mem _ (hmem j).1 _)
  have hz5 : z ^ 5 ∈ vU D := by
    have : z ^ 5 = (∏ j, SelmerForm.Bu hB j ^ e j)⁻¹ * E := by rw [hEq, inv_mul_cancel_left]
    rw [this]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hP) hEU
  have hz : z ∈ vU D := mem_vUnits_of_pow _ _ z 5 (by norm_num) hz5
  have hsplit : (⟨E, hEU⟩ : vU D) = (∏ j, bu j ^ e j) * (⟨z, hz⟩ : vU D) ^ 5 := by
    apply (vU D).subtype_injective
    simp only [map_mul, map_pow, map_prod, map_zpow, Subgroup.coe_subtype, bu]
    exact hEq
  rw [hsplit, map_mul, toAdd_mul, map_pow, toAdd_pow]
  have h5 : (5 : ℕ) • Multiplicative.toAdd (symU D ⟨z, hz⟩) = 0 := by
    rw [nsmul_eq_mul]; exact mul_eq_zero_of_left (by decide) _
  rw [h5, add_zero, map_prod, toAdd_prod]
  simp only [map_zpow, toAdd_zpow, zsmul_eq_mul, hsymB]

/-! ## The paper's sieve: (N), (V) and (Q) at the five primes of Theorem 7.1 -/

/-- The printed matrix `M_q` lists the primes above `q` in another order than the models: row `k` of the printed
matrix is row `σ k` of ours, and the printed set `I(q)` is our set with coordinates reordered by `σ`. -/
theorem mem_perm {m : ℕ} (σ : Fin m → Fin m) (M Mp : Matrix (Fin m) (Fin 24) (ZMod 5))
    (hM : (List.finRange m).all (fun k => (List.finRange 24).all fun j => decide (Mp k j = M (σ k) j)) = true)
    (L1 L2 : List (Fin m → ZMod 5)) (hL : L1.all (fun v => L2.contains (fun k => v (σ k))) = true)
    (c : Fin 24 → ZMod 5) (h : M *ᵥ c ∈ L1.toFinset) : Mp *ᵥ c ∈ L2 := by
  simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq, true_implies] at hM
  have hMc : Mp *ᵥ c = fun k => (M *ᵥ c) (σ k) := by
    funext k; simp only [Matrix.mulVec, dotProduct, hM]
  rw [List.mem_toFinset] at h
  have := List.all_eq_true.1 hL _ h
  rw [hMc]; simpa using this

/-- The row orders (printed row `k` = model row `σ k`). -/
def σ181 : Fin 11 → Fin 11 := ![4, 2, 0, 5, 7, 6, 3, 1, 8, 9, 10]
def σ311 : Fin 11 → Fin 11 := ![6, 2, 4, 0, 5, 3, 1, 7, 9, 10, 8]
def σ131 : Fin 9 → Fin 9 := ![2, 4, 1, 5, 0, 3, 6, 8, 7]
def σ251 : Fin 9 → Fin 9 := ![1, 0, 5, 2, 4, 3, 8, 6, 7]
def σ101 : Fin 7 → Fin 7 := ![1, 0, 2, 5, 3, 4, 6]

theorem M181_perm : (List.finRange 11).all (fun k => (List.finRange 24).all fun j =>
    decide (Sieve.M181 k j = Q181.M (σ181 k) j)) = true := by decide +kernel
theorem M311_perm : (List.finRange 11).all (fun k => (List.finRange 24).all fun j =>
    decide (Sieve.M311 k j = Q311.M (σ311 k) j)) = true := by decide +kernel
theorem M131_perm : (List.finRange 9).all (fun k => (List.finRange 24).all fun j =>
    decide (Sieve.M131 k j = Q131.M (σ131 k) j)) = true := by decide +kernel
theorem M251_perm : (List.finRange 9).all (fun k => (List.finRange 24).all fun j =>
    decide (Sieve.M251 k j = Q251.M (σ251 k) j)) = true := by decide +kernel
theorem M101_perm : (List.finRange 7).all (fun k => (List.finRange 24).all fun j =>
    decide (Sieve.M101 k j = Q101.M (σ101 k) j)) = true := by decide +kernel

theorem I181_perm : SymbolSets.I181L.all (fun v => Sieve.I181.contains (fun k => v (σ181 k))) = true := by
  decide +kernel
theorem I311_perm : SymbolSets.I311L.all (fun v => Sieve.I311.contains (fun k => v (σ311 k))) = true := by
  decide +kernel
theorem I131_perm : SymbolSets.I131L.all (fun v => Sieve.I131.contains (fun k => v (σ131 k))) = true := by
  decide +kernel
theorem I251_perm : SymbolSets.I251L.all (fun v => Sieve.I251.contains (fun k => v (σ251 k))) = true := by
  decide +kernel
theorem I101_perm : SymbolSets.I101L.all (fun v => Sieve.I101.contains (fun k => v (σ101 k))) = true := by
  decide +kernel

include hBx hB in
/-- **From Theorem 7.1 to Theorem 1.1.** If every factorization `E = ∏ B_j^{e_j} z⁵` satisfies (N) and (V),
and the symbol vectors of `E` at `181, 311, 131, 251, 101` lie in the sets `I(q)`, Theorem 7.1 gives a
contradiction. -/
theorem compose_paper (hclass : ∀ c : ClassGroup (𝓞 L24), c ^ 5 = 1 → c = 1) (E : L24ˣ)
    (hE : ∀ v, v ∉ Selmer.L24SIntegers.Sprimes → (5 : ℤ) ∣ SelmerForm.cnt v E)
    (hNV : ∀ (e : Fin 24 → ℤ) (z : L24ˣ), (E : L24) = (∏ j, B j ^ e j) * (z : L24) ^ 5 →
      Sieve.CondN (fun j => (e j : ZMod 5)) ∧ Sieve.CondV (fun j => (e j : ZMod 5)))
    (h181 : AuxAt Q181.L24P SymbolSets.I181 E) (h311 : AuxAt Q311.L24P SymbolSets.I311 E)
    (h131 : AuxAt Q131.L24P SymbolSets.I131 E) (h251 : AuxAt Q251.L24P SymbolSets.I251 E)
    (h101 : AuxAt Q101.L24P SymbolSets.I101 E) : False := by
  obtain ⟨e, z, hform⟩ := exists_form hBx hB hclass E hE
  have hc := fun D h => sym_of_form hBx hB D E h e z hform
  obtain ⟨hN, hV⟩ := hNV e z hform
  exact Sieve.sieve _ hN hV
    ⟨mem_perm σ181 _ _ M181_perm _ _ I181_perm _ (mulVec_mem _ _ Q181.sym_M _ E _ hc h181),
     mem_perm σ311 _ _ M311_perm _ _ I311_perm _ (mulVec_mem _ _ Q311.sym_M _ E _ hc h311),
     mem_perm σ131 _ _ M131_perm _ _ I131_perm _ (mulVec_mem _ _ Q131.sym_M _ E _ hc h131),
     mem_perm σ251 _ _ M251_perm _ _ I251_perm _ (mulVec_mem _ _ Q251.sym_M _ E _ hc h251),
     mem_perm σ101 _ _ M101_perm _ _ I101_perm _ (mulVec_mem _ _ Q101.sym_M _ E _ hc h101)⟩
end

end X2Y5Z7.Main
