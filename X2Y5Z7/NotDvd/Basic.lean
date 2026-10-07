module

public import X2Y5Z7.Primes.Basic
public import X2Y5Z7.Auxiliary.GeneratorsY
public import X2Y5Z7.Auxiliary.Degree
public import Mathlib.NumberTheory.LegendreSymbol.Basic

@[expose] public section

/-! # Corollary 5.5 (`q ∤ XYZ`): the auxiliary prime `q` divides none of `X`, `Y`, `Z` (generic part)

Let `s` be a solution, `Rt : Aux.Root s` a generating root, and `R : Fin r → Aux.ResidueMap L8 q` residue maps at
primes of `L8` above `q` with pairwise distinct kernels, of residue degrees `d_i`.

* `q ∣ X` (`exists_split_X`): with `T = {i : r_i(w) = 0}`, the primes outside `T` have `r_i(w)` a root of
  `C̄(w) = w³ + 8Z̄w² + 56Z̄²w + 560Z̄³` (degree sum `≤ 3`); those in `T` have `r_i(u)⁵ = -56Z̄⁷` (degree sum `≤ 5`, each
  degree divides `5`).
* `q ∣ Z` (`exists_split_Z`): primes in `T` have degree sum `≤ 1` (root of `w`); the others have
  `r_i(w)⁷ = 400000X̄⁵` (degree sum `≤ 7`, each degree divides `D` when `7(q-1) ∣ q^D - 1`).
* `q ∣ Y` (`sq_sum_eq_Y`): for `d` with `Z̄d̄² = c₀` and a factorization `P_{c₀} = ∏ φ_j` into monic irreducibles
  over `F_q`, the multiset of residue degrees is that of the `deg φ_j` (when `Σ d_i = 8`); we record the consequence
  `Σ d_i² = Σ (deg φ_j)²`. `exists_d` gives `d` with `Z̄d̄² ∈ {1, ν}` for a non-square `ν`.

The final `not_dvd_X`, `not_dvd_Z`, `not_dvd_Y` take a decidable combinatorial hypothesis on the degree vector. -/

namespace X2Y5Z7.NotDvd

open Polynomial NumberField X2Y5Z7.Aux

noncomputable section

variable {q : ℕ} [hqp : Fact q.Prime]

/-! ## Helpers -/

theorem algebraMap_ne {k : Type*} [Field k] [Algebra (ZMod q) k] {c : ZMod q} (hc : c ≠ 0) :
    algebraMap (ZMod q) k c ≠ 0 := (_root_.map_ne_zero _).mpr hc

theorem intCast_eq {k : Type*} [Field k] [Algebra (ZMod q) k] (n : ℤ) :
    ((n : ZMod q) : ZMod q) = 0 → (n : k) = 0 := by
  intro h
  rw [← map_intCast (algebraMap (ZMod q) k), h, map_zero]

theorem intCast_ne {k : Type*} [Field k] [Algebra (ZMod q) k] (n : ℤ) :
    (n : ZMod q) ≠ 0 → (n : k) ≠ 0 := by
  intro h
  rw [← map_intCast (algebraMap (ZMod q) k)]
  exact algebraMap_ne h

theorem seventy_ne {k : Type*} [Field k] [Algebra (ZMod q) k] (h70 : (70 : ZMod q) ≠ 0) : (70 : k) ≠ 0 := by
  have := algebraMap_ne (k := k) h70
  rwa [map_ofNat] at this

theorem zmod_eq_zero_iff (n : ℤ) : (n : ZMod q) = 0 ↔ (q : ℤ) ∣ n := ZMod.intCast_zmod_eq_zero_iff_dvd n q

/-- A prime cannot divide both of two coprime integers. -/
theorem not_dvd_of_coprime {a b : ℤ} (h : IsCoprime a b) (ha : (q : ℤ) ∣ a) (hb : (q : ℤ) ∣ b) : False := by
  have hu := h.isUnit_of_dvd' ha hb
  rw [Int.isUnit_iff] at hu
  have h2 := hqp.out.two_le
  omega

variable {r : ℕ}

omit hqp in
theorem pairwise_subtype (R : Fin r → ResidueMap L8 q)
    (hker : Pairwise fun i j => RingHom.ker (R i).r ≠ RingHom.ker (R j).r) (p : Fin r → Prop) :
    Pairwise fun i j : Subtype p => RingHom.ker (R i.1).r ≠ RingHom.ker (R j.1).r :=
  fun _ _ hij => hker fun h => hij (Subtype.ext h)

theorem sum_subtype_eq (f : Fin r → ℕ) (p : Fin r → Prop) [DecidablePred p] :
    ∑ i : Subtype p, f i.1 = ∑ i ∈ Finset.univ.filter p, f i :=
  (Finset.sum_subtype _ (by simp) f).symm

/-! ## `q ∣ X` -/

theorem Cpoly_monic (s : Solution) : (Cpoly s).Monic := by unfold Cpoly; monicity!

theorem Cpoly_natDegree (s : Solution) : (Cpoly s).natDegree = 3 := by unfold Cpoly; compute_degree!

theorem derivativeInteger_wI {s : Solution} (Rt : Root s) :
    derivativeInteger Rt.wI = aeval Rt.wI (derivative (Gw s)) := by
  rw [derivativeInteger, Rt.minpoly_wI]

theorem derivativeInteger_uI {s : Solution} (Rt : Root s) :
    derivativeInteger Rt.uI = aeval Rt.uI (derivative (Gu s)) := by
  rw [derivativeInteger, Rt.minpoly_uI]

theorem derivativeInteger_τI {s : Solution} (Rt : Root s) (d : ℤ) (hd : d ≠ 0) :
    derivativeInteger (Rt.τI d) = aeval (Rt.τI d) (derivative (Gd s d)) := by
  rw [derivativeInteger, Rt.minpoly_τI d hd]

/-- The split of the primes above `q ∣ X`. -/
theorem exists_split_X (s : Solution) (Rt : Root s) (R : Fin r → ResidueMap L8 q)
    (hker : Pairwise fun i j => RingHom.ker (R i).r ≠ RingHom.ker (R j).r) (h70 : (70 : ZMod q) ≠ 0)
    (hdiv : 5 * (q - 1) ∣ q ^ 5 - 1) (hX : (q : ℤ) ∣ s.X) :
    ∃ T : Finset (Fin r), (∀ i ∈ T, (R i).deg ∣ 5) ∧ ∑ i ∈ T, (R i).deg ≤ 5 ∧ ∑ i ∈ Tᶜ, (R i).deg ≤ 3 := by
  classical
  have hZq : (s.Z : ZMod q) ≠ 0 := fun h =>
    not_dvd_of_coprime s.coprime hX ((zmod_eq_zero_iff _).mp h)
  have hXq : (s.X : ZMod q) = 0 := (zmod_eq_zero_iff _).mpr hX
  have hXk : ∀ i, (s.X : (R i).k) = 0 := fun i => intCast_eq _ hXq
  have h70k : ∀ i, (70 : (R i).k) * s.Z ≠ 0 := fun i => mul_ne_zero (seventy_ne h70) (intCast_ne _ hZq)
  obtain ⟨h2, -, h7⟩ := ne_zero_of_70 h70
  let p : Fin r → Prop := fun i => (R i).r Rt.wI = 0
  refine ⟨Finset.univ.filter p, ?_, ?_, ?_⟩
  · -- degrees divide 5
    intro i hi
    have hw : (R i).r Rt.wI = 0 := (Finset.mem_filter.mp hi).2
    obtain ⟨-, hu5, hdu⟩ := Rt.qX_uI (R i).r (hXk i) (h70k i) hw
    rw [ResidueMap.deg, ← minpoly_degree Rt.uI (R i).r (R i).surj Rt.adjoin_uI
      (by rw [derivativeInteger_uI]; exact hdu)]
    refine minpoly_natDegree_dvd_of_pow_eq _ 5 5 (-56 * (s.Z : ZMod q) ^ 7) ?_ ?_ hdiv
    · intro h
      apply mul_ne_zero (mul_ne_zero (pow_ne_zero 3 h2) h7) (pow_ne_zero 7 hZq)
      linear_combination -h
    · rw [hu5]; simp [map_mul, map_pow, map_neg, map_intCast, map_ofNat]
  · -- primes with `r(w) = 0`: `r(u)⁵ = -56Z̄⁷`
    let R' : Subtype p → ResidueMap L8 q := fun i => R i.1
    have hle := sum_deg_le Rt.uI Rt.adjoin_uI R' (pairwise_subtype R hker p)
      (fun i => by
        rw [derivativeInteger_uI]
        exact (Rt.qX_uI (R i.1).r (hXk i.1) (h70k i.1) i.2).2.2)
      (X ^ 5 + C (56 * (s.Z : ZMod q) ^ 7)) (X_pow_add_C_ne_zero (by norm_num) _)
      (fun i => by
        have := (Rt.qX_uI (R i.1).r (hXk i.1) (h70k i.1) i.2).2.1
        simp only [map_add, map_pow, aeval_X, map_mul, map_intCast, map_ofNat]
        change (R i.1).r Rt.uI ^ 5 + _ = 0
        rw [this]; ring)
    rw [natDegree_X_pow_add_C] at hle
    rw [← sum_subtype_eq (fun i => (R i).deg) p]
    exact hle
  · -- primes with `r(w) ≠ 0`: roots of `C̄`
    rw [Finset.compl_filter]
    let R' : Subtype (fun i => ¬ p i) → ResidueMap L8 q := fun i => R i.1
    have hC := (Cpoly_monic s).map (Int.castRingHom (ZMod q))
    have hle := sum_deg_le Rt.wI Rt.adjoin_wI R' (pairwise_subtype R hker _)
      (fun i => by
        rw [derivativeInteger_wI]
        exact (Rt.qX_wI (R i.1).r (hXk i.1) (h70k i.1) i.2).1)
      ((Cpoly s).map (Int.castRingHom (ZMod q))) hC.ne_zero
      (fun i => by
        rw [← algebraMap_int_eq, aeval_map_algebraMap]
        exact (Rt.qX_wI (R i.1).r (hXk i.1) (h70k i.1) i.2).2)
    rw [(Cpoly_monic s).natDegree_map, Cpoly_natDegree] at hle
    rw [← sum_subtype_eq (fun i => (R i).deg) (fun i => ¬ p i)]
    exact hle

/-! ## `q ∣ Z` -/

/-- The split of the primes above `q ∣ Z`. -/
theorem exists_split_Z (s : Solution) (Rt : Root s) (R : Fin r → ResidueMap L8 q)
    (hker : Pairwise fun i j => RingHom.ker (R i).r ≠ RingHom.ker (R j).r) (h70 : (70 : ZMod q) ≠ 0)
    (D : ℕ) (hdiv : 7 * (q - 1) ∣ q ^ D - 1) (hZ : (q : ℤ) ∣ s.Z) :
    ∃ T : Finset (Fin r), ∑ i ∈ T, (R i).deg ≤ 1 ∧ (∀ i ∈ Tᶜ, (R i).deg ∣ D) ∧ ∑ i ∈ Tᶜ, (R i).deg ≤ 7 := by
  classical
  have hXq : (s.X : ZMod q) ≠ 0 := fun h =>
    not_dvd_of_coprime s.coprime ((zmod_eq_zero_iff _).mp h) hZ
  have hZq : (s.Z : ZMod q) = 0 := (zmod_eq_zero_iff _).mpr hZ
  have hZk : ∀ i, (s.Z : (R i).k) = 0 := fun i => intCast_eq _ hZq
  have h70k : ∀ i, (70 : (R i).k) * s.X ≠ 0 := fun i => mul_ne_zero (seventy_ne h70) (intCast_ne _ hXq)
  obtain ⟨h2, h5, -⟩ := ne_zero_of_70 h70
  have hd : ∀ i, (R i).r (derivativeInteger Rt.wI) ≠ 0 := fun i => by
    rw [derivativeInteger_wI]; exact (Rt.qZ (R i).r (hZk i) (h70k i)).1
  let p : Fin r → Prop := fun i => (R i).r Rt.wI = 0
  have hpow : ∀ i, ¬ p i → (R i).r Rt.wI ^ 7 = 400000 * (s.X : (R i).k) ^ 5 := fun i hi =>
    (Rt.qZ (R i).r (hZk i) (h70k i)).2.resolve_left hi
  refine ⟨Finset.univ.filter p, ?_, ?_, ?_⟩
  · let R' : Subtype p → ResidueMap L8 q := fun i => R i.1
    have hle := sum_deg_le Rt.wI Rt.adjoin_wI R' (pairwise_subtype R hker p) (fun i => hd i.1)
      X X_ne_zero (fun i => by rw [aeval_X]; exact i.2)
    rw [natDegree_X] at hle
    rw [← sum_subtype_eq (fun i => (R i).deg) p]
    exact hle
  · intro i hi
    rw [Finset.compl_filter, Finset.mem_filter] at hi
    rw [ResidueMap.deg, ← minpoly_degree Rt.wI (R i).r (R i).surj Rt.adjoin_wI (hd i)]
    refine minpoly_natDegree_dvd_of_pow_eq _ 7 D (400000 * (s.X : ZMod q) ^ 5) ?_ ?_ hdiv
    · intro h
      apply mul_ne_zero (mul_ne_zero (pow_ne_zero 7 h2) (pow_ne_zero 5 h5)) (pow_ne_zero 5 hXq)
      linear_combination h
    · rw [hpow i hi.2]; simp [map_mul, map_pow, map_intCast, map_ofNat]
  · rw [Finset.compl_filter]
    let R' : Subtype (fun i => ¬ p i) → ResidueMap L8 q := fun i => R i.1
    have hle := sum_deg_le Rt.wI Rt.adjoin_wI R' (pairwise_subtype R hker _) (fun i => hd i.1)
      (X ^ 7 - C (400000 * (s.X : ZMod q) ^ 5)) (X_pow_sub_C_ne_zero (by norm_num) _)
      (fun i => by
        have := hpow i.1 i.2
        simp only [map_sub, map_pow, aeval_X, map_mul, map_intCast, map_ofNat]
        change (R i.1).r Rt.wI ^ 7 - _ = 0
        rw [this]; ring)
    rw [natDegree_X_pow_sub_C] at hle
    rw [← sum_subtype_eq (fun i => (R i).deg) (fun i => ¬ p i)]
    exact hle

/-! ## `q ∣ Y` -/

theorem aeval_Pc {k : Type*} [Field k] [Algebra (ZMod q) k] (c : ZMod q) (y : k) :
    aeval y (Pc c) = eval y (Pc (algebraMap (ZMod q) k c)) := by
  rw [eval_Pc]
  simp only [Pc, map_sub, map_add, map_pow, aeval_X, aeval_C, map_mul, map_ofNat]

/-- For `Z̄d̄² = c₀` and `P_{c₀} = ∏ φ_j` (monic irreducible), `Σ d_i² = Σ (deg φ_j)²`. -/
theorem sq_sum_eq_Y (s : Solution) (Rt : Root s) (R : Fin r → ResidueMap L8 q)
    (hker : Pairwise fun i j => RingHom.ker (R i).r ≠ RingHom.ker (R j).r) (h70 : (70 : ZMod q) ≠ 0)
    (hY : (q : ℤ) ∣ s.Y) (d : ℤ) (hd : (d : ZMod q) ≠ 0) (c₀ : ZMod q) (hc : (s.Z : ZMod q) * (d : ZMod q) ^ 2 = c₀)
    {m : ℕ} (φ : Fin m → (ZMod q)[X]) (hφm : ∀ j, (φ j).Monic) (hφi : ∀ j, Irreducible (φ j))
    (hprod : ∏ j, φ j = Pc c₀) (hsum : ∑ i, (R i).deg = ∑ j, (φ j).natDegree) :
    ∑ i, (R i).deg ^ 2 = ∑ j, (φ j).natDegree ^ 2 := by
  have hZq : (s.Z : ZMod q) ≠ 0 := fun h =>
    not_dvd_of_coprime s.coprime_YZ hY ((zmod_eq_zero_iff _).mp h)
  have hYq : (s.Y : ZMod q) = 0 := (zmod_eq_zero_iff _).mpr hY
  have hd0 : d ≠ 0 := by rintro rfl; exact hd (by simp)
  have hYk : ∀ i, (s.Y : (R i).k) = 0 := fun i => intCast_eq _ hYq
  have hder : ∀ i, (R i).r (derivativeInteger (Rt.τI d)) ≠ 0 := fun i => by
    rw [derivativeInteger_τI Rt d hd0]
    exact Rt.τI_derivative_ne_zero (R i).r d (hYk i)
      (mul_ne_zero (mul_ne_zero (seventy_ne h70) (intCast_ne _ hZq)) (intCast_ne _ hd))
  have hroot : ∀ i, aeval ((R i).r (Rt.τI d)) (∏ j, φ j) = 0 := fun i => by
    rw [hprod, aeval_Pc, ← hc]
    simp only [map_mul, map_pow, map_intCast]
    exact Rt.eval_Pc_res_τI (R i).r d (hYk i)
  have hM := multiset_deg_eq (Rt.τI d) (Rt.adjoin_τI d hd0) R hker hder φ hφm hφi hroot
    (by rw [natDegree_prod_factors φ hφi]; exact hsum)
  have := congrArg (fun M : Multiset ℕ => (M.map (fun n => n ^ 2)).sum) hM
  simp only [Multiset.map_map, Function.comp_def] at this
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  exact this

/-- For `Z̄ ≠ 0` and a non-square `ν`, some `d` with `d̄ ≠ 0` has `Z̄d̄² ∈ {1, ν}`. -/
theorem exists_d (z ν : ZMod q) (hz : z ≠ 0) (hν0 : ν ≠ 0) (hν : ν ^ (q / 2) = -1) :
    ∃ d : ℤ, (d : ZMod q) ≠ 0 ∧ (z * (d : ZMod q) ^ 2 = 1 ∨ z * (d : ZMod q) ^ 2 = ν) := by
  have hcast : ∀ e : ZMod q, (((e.val : ℕ) : ℤ) : ZMod q) = e := fun e => by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  rcases ZMod.pow_div_two_eq_neg_one_or_one q hz with h1 | h1
  · obtain ⟨e, he⟩ := (ZMod.euler_criterion q hz).mpr h1
    have he0 : e ≠ 0 := by rintro rfl; exact hz (by simpa using he)
    refine ⟨((e⁻¹).val : ℤ), ?_, Or.inl ?_⟩ <;> rw [hcast]
    · exact inv_ne_zero he0
    · rw [he]; field_simp
  · have ha : ν * z⁻¹ ≠ 0 := mul_ne_zero hν0 (inv_ne_zero hz)
    have hsq : (ν * z⁻¹) ^ (q / 2) = 1 := by
      rw [mul_pow, inv_pow, hν, h1]; norm_num
    obtain ⟨e, he⟩ := (ZMod.euler_criterion q ha).mpr hsq
    refine ⟨(e.val : ℤ), ?_, Or.inr ?_⟩ <;> rw [hcast]
    · rintro rfl; exact ha (by simpa using he)
    · rw [sq, ← he]; field_simp

/-! ## The three cases, against a degree vector -/

/-- `q ∤ X`, given that no split of the degree vector is compatible with `q ∣ X`. -/
theorem not_dvd_X (s : Solution) (Rt : Root s) (R : Fin r → ResidueMap L8 q)
    (hker : Pairwise fun i j => RingHom.ker (R i).r ≠ RingHom.ker (R j).r) (h70 : (70 : ZMod q) ≠ 0)
    (hdiv : 5 * (q - 1) ∣ q ^ 5 - 1) (dv : Fin r → ℕ) (hdeg : ∀ i, (R i).deg = dv i)
    (hcomb : ∀ T : Finset (Fin r), (∀ i ∈ T, dv i ∣ 5) → ∑ i ∈ T, dv i ≤ 5 → ∑ i ∈ Tᶜ, dv i ≤ 3 → False) :
    ¬ (q : ℤ) ∣ s.X := fun hX => by
  obtain ⟨T, h1, h2, h3⟩ := exists_split_X s Rt R hker h70 hdiv hX
  simp only [hdeg] at h1 h2 h3
  exact hcomb T h1 h2 h3

/-- `q ∤ Z`, given that no split of the degree vector is compatible with `q ∣ Z`. -/
theorem not_dvd_Z (s : Solution) (Rt : Root s) (R : Fin r → ResidueMap L8 q)
    (hker : Pairwise fun i j => RingHom.ker (R i).r ≠ RingHom.ker (R j).r) (h70 : (70 : ZMod q) ≠ 0)
    (D : ℕ) (hdiv : 7 * (q - 1) ∣ q ^ D - 1) (dv : Fin r → ℕ) (hdeg : ∀ i, (R i).deg = dv i)
    (hcomb : ∀ T : Finset (Fin r), ∑ i ∈ T, dv i ≤ 1 → (∀ i ∈ Tᶜ, dv i ∣ D) → ∑ i ∈ Tᶜ, dv i ≤ 7 → False) :
    ¬ (q : ℤ) ∣ s.Z := fun hZ => by
  obtain ⟨T, h1, h2, h3⟩ := exists_split_Z s Rt R hker h70 D hdiv hZ
  simp only [hdeg] at h1 h2 h3
  exact hcomb T h1 h2 h3

/-- `q ∤ Y`, given factorizations of `P_1` and `P_ν` (`ν` a non-square) whose degree multisets differ from the
degree vector (detected by the sum of squares). -/
theorem not_dvd_Y (s : Solution) (Rt : Root s) (R : Fin r → ResidueMap L8 q)
    (hker : Pairwise fun i j => RingHom.ker (R i).r ≠ RingHom.ker (R j).r) (h70 : (70 : ZMod q) ≠ 0)
    (dv : Fin r → ℕ) (hdeg : ∀ i, (R i).deg = dv i) (hsum : ∑ i, dv i = 8)
    (ν : ZMod q) (hν0 : ν ≠ 0) (hν : ν ^ (q / 2) = -1)
    {m₁ : ℕ} (φ₁ : Fin m₁ → (ZMod q)[X]) (hm₁ : ∀ j, (φ₁ j).Monic) (hi₁ : ∀ j, Irreducible (φ₁ j))
    (hp₁ : ∏ j, φ₁ j = Pc 1) (hs₁ : ∑ j, (φ₁ j).natDegree = 8)
    (hne₁ : ∑ i, dv i ^ 2 ≠ ∑ j, (φ₁ j).natDegree ^ 2)
    {m₂ : ℕ} (φ₂ : Fin m₂ → (ZMod q)[X]) (hm₂ : ∀ j, (φ₂ j).Monic) (hi₂ : ∀ j, Irreducible (φ₂ j))
    (hp₂ : ∏ j, φ₂ j = Pc ν) (hs₂ : ∑ j, (φ₂ j).natDegree = 8)
    (hne₂ : ∑ i, dv i ^ 2 ≠ ∑ j, (φ₂ j).natDegree ^ 2) :
    ¬ (q : ℤ) ∣ s.Y := fun hY => by
  have hZq : (s.Z : ZMod q) ≠ 0 := fun h =>
    not_dvd_of_coprime s.coprime_YZ hY ((zmod_eq_zero_iff _).mp h)
  obtain ⟨d, hd, hc | hc⟩ := exists_d _ ν hZq hν0 hν
  · have := sq_sum_eq_Y s Rt R hker h70 hY d hd 1 hc φ₁ hm₁ hi₁ hp₁ (by simp only [hdeg, hsum, hs₁])
    simp only [hdeg] at this
    exact hne₁ this
  · have := sq_sum_eq_Y s Rt R hker h70 hY d hd ν hc φ₂ hm₂ hi₂ hp₂ (by simp only [hdeg, hsum, hs₂])
    simp only [hdeg] at this
    exact hne₂ this

end

end X2Y5Z7.NotDvd
