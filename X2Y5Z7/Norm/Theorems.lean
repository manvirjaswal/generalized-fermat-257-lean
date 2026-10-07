module

public import X2Y5Z7.Norm.Identities
public import X2Y5Z7.Norm.Basic
public import X2Y5Z7.Sieve.Theorem

@[expose] public section

/-! # Lemma 6.3 and the condition (N) for the descent element

* `u_independent` (**Lemma 6.3(i)**): the classes of `u₁, …, u₁₀` in `L₈ˣ/L₈ˣ⁵` are independent over `𝔽₅`. If
  `∏ u_i^{e_i}` is a fifth power up to sign, then the fifth-power residue symbols at the ten primes `Pr k`
  (`Symbols.lean`) give `Su · e ≡ 0 (mod 5)`, and `Su` is invertible.
* `normB`, `two_eq` (**Lemma 6.3(ii)**, `Identities.lean`): `N_{L₂₄/L₈}(B_j) = ±∏ u_i^{N_{ij}}` and `2 = ±∏ u_i^{T_i}`,
  with `N`, `T` the data `Sieve.NM`, `Sieve.TT` of (A.1).
* `condN_of_form` (Section 7, step (2) of the proof of Theorem 1.1): if `E = ∏ B_j^{e_j} · z⁵`, then taking norms to
  `L₈` and using Proposition 3.2 gives `∏ u_i^{(Ne - T)_i} ∈ ±L₈ˣ⁵`, so `Ne ≡ T (mod 5)` by Lemma 6.3(i). -/

namespace X2Y5Z7.Norm

open Polynomial FiniteFields Matrix

noncomputable section

/-- `u_i` as a unit of `L₈`. -/
abbrev U (i : Fin 10) : L8ˣ := uU un_ne i

theorem prod_zpow_eq_zpow_sum {G ι : Type*} [CommGroup G] (g : G) (s : Finset ι) (f : ι → ℤ) :
    ∏ j ∈ s, g ^ f j = g ^ ∑ j ∈ s, f j := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons j s hj ih => rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add]

/-! ## Lemma 6.3(i) -/

/-- The symbols at `Pr k` of a fifth power `∏ u_i^{f_i}`. -/
theorem sum_sym_eq_zero (f : Fin 10 → ℤ) (Y : L8ˣ) (h : ∏ i, U i ^ f i = Y ^ 5) (k : Fin 10) :
    ∑ i, Su k i * (f i : ZMod 5) = 0 := by
  have hs := fun i => symL8_u un_ne (Pr k) i _ (sym_u k i)
  choose hmem hval using hs
  have hprod : ∏ i, U i ^ f i ∈ unitsL8 (Pr k) :=
    Subgroup.prod_mem _ fun i _ => Subgroup.zpow_mem _ (hmem i) _
  rw [h] at hprod
  have hY : Y ∈ unitsL8 (Pr k) := mem_unitsK_of_pow _ _ Y 5 (by norm_num) hprod
  have hH : (∏ i, (⟨U i, hmem i⟩ : unitsL8 (Pr k)) ^ f i) = (⟨Y, hY⟩ : unitsL8 (Pr k)) ^ 5 := by
    apply Subtype.ext
    simpa using h
  have := congrArg (fun x => Multiplicative.toAdd (symL8 (Pr k) x)) hH
  simp only [map_prod, map_zpow, map_pow, toAdd_prod, toAdd_zpow, toAdd_pow, hval] at this
  have h5 : (5 : ℕ) • Multiplicative.toAdd (symL8 (Pr k) ⟨Y, hY⟩) = 0 := by
    rw [nsmul_eq_mul]
    have : ((5 : ℕ) : ZMod 5) = 0 := by decide
    rw [this, zero_mul]
  rw [h5] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [zsmul_eq_mul, mul_comm]
  rfl

/-- Lemma 6.3(i) for units: if `∏ u_i^{f_i}` is a fifth power in `L₈ˣ`, then `5 ∣ f_i` for all `i`. -/
theorem dvd_of_prod_U_eq_pow (f : Fin 10 → ℤ) (Y : L8ˣ) (h : ∏ i, U i ^ f i = Y ^ 5) (i : Fin 10) :
    (5 : ℤ) ∣ f i := by
  have hv : Su *ᵥ (fun i => (f i : ZMod 5)) = 0 := by
    funext k
    exact sum_sym_eq_zero f Y h k
  have h0 : (fun i => (f i : ZMod 5)) = 0 := by
    rw [← Matrix.one_mulVec (fun i => (f i : ZMod 5)), ← SuInv_mul, ← Matrix.mulVec_mulVec, hv,
      Matrix.mulVec_zero]
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (f i) 5).mp (congrFun h0 i)

/-- **Lemma 6.3(i).** If `∏ u_i^{e_i}` is a fifth power in `L₈` up to sign, then `5 ∣ e_i` for all `i`: the classes of
`u₁, …, u₁₀` in `L₈ˣ/L₈ˣ⁵` are linearly independent over `𝔽₅`. -/
theorem u_independent (e : Fin 10 → ℤ) (x : L8)
    (h : ∏ i, u i ^ e i = x ^ 5 ∨ ∏ i, u i ^ e i = -x ^ 5) : ∀ i, (5 : ℤ) ∣ e i := by
  obtain ⟨y, hy⟩ : ∃ y : L8, ∏ i, u i ^ e i = y ^ 5 := by
    rcases h with h | h
    · exact ⟨x, h⟩
    · exact ⟨-x, by rw [h, Odd.neg_pow (by decide)]⟩
  have hne : ∏ i, u i ^ e i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (u_ne_zero un_ne i)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [hy] at hne
    exact hne (by norm_num)
  intro i
  refine dvd_of_prod_U_eq_pow e (Units.mk0 y hy0) ?_ i
  apply Units.ext
  simp [hy]

/-! ## The condition (N) -/

/-- The norm `N_{L₂₄/L₈}` as a homomorphism of monoids with zero. -/
def normZ : L24 →*₀ L8 where
  toFun := Algebra.norm L8
  map_zero' := Algebra.norm_zero
  map_one' := map_one _
  map_mul' := map_mul _

theorem normZ_apply (x : L24) : normZ x = Algebra.norm L8 x := rfl

/-- A sign as a unit. -/
def sgnU (s : ℤ) : L8ˣ := if s = 1 then 1 else -1

theorem coe_sgnU (s : ℤ) (hs : s = 1 ∨ s = -1) : ((sgnU s : L8ˣ) : L8) = s := by
  rcases hs with rfl | rfl <;> simp [sgnU]

theorem sgnU_sq (s : ℤ) : sgnU s ^ 2 = 1 := by
  unfold sgnU; split_ifs <;> simp

/-- `N_{L₂₄/L₈}(B_j)` as a unit. -/
def NBU (j : Fin 24) : L8ˣ := sgnU (sgnB j) * ∏ i, U i ^ Sieve.NM i j

theorem coe_NBU (j : Fin 24) : ((NBU j : L8ˣ) : L8) = Algebra.norm L8 (B j) := by
  rw [normB, NBU, Units.val_mul, coe_sgnU _ (sgnB_eq j), Units.coe_prod]
  simp

theorem two_eq_U : ((∏ i, U i ^ Sieve.TT i : L8ˣ) : L8) = 2 := by
  rw [two_eq, sgnT, Units.coe_prod]
  simp

/-- The exponents `N e - T`. -/
def expo (e : Fin 24 → ℤ) (i : Fin 10) : ℤ := ∑ j, Sieve.NM i j * e j - Sieve.TT i

theorem prod_NBU_zpow (e : Fin 24 → ℤ) :
    ∏ j, NBU j ^ e j = (∏ j, sgnU (sgnB j) ^ e j) * ∏ i, U i ^ ∑ j, Sieve.NM i j * e j := by
  simp only [NBU, mul_zpow, Finset.prod_mul_distrib, ← Finset.prod_zpow, ← zpow_mul]
  congr 1
  rw [Finset.prod_comm]
  exact Finset.prod_congr rfl fun i _ => prod_zpow_eq_zpow_sum _ _ _

theorem solve_aux {G : Type*} [CommGroup G] (T C σ P W : G) (hU : T * C ^ 5 = σ * P * W ^ 5)
    (hσ : σ ^ 5 = σ⁻¹) : P / T = (σ * C * W⁻¹) ^ 5 := by
  have hP : P = σ⁻¹ * (T * C ^ 5) * (W ^ 5)⁻¹ := by rw [hU]; group
  rw [hP, mul_pow, mul_pow, hσ, inv_pow, div_eq_mul_inv]
  simp only [mul_comm, mul_left_comm, mul_assoc]
  exact mul_inv_cancel_left T _

/-- **The condition (N).** If `E = ∏ B_j^{e_j} · z⁵` for the descent element `E` of `θ ∈ L₈`, then the class
`c = e mod 5` satisfies `N c ≡ T (mod 5)`. -/
theorem condN_of_form (θ : L8) (hθ : aeval θ ψ ≠ 0) (e : Fin 24 → ℤ) (z : L24ˣ)
    (hE : Edesc (algebraMap L8 L24 θ) = (∏ j, B j ^ e j) * (z : L24) ^ 5) :
    Sieve.CondN (fun j => (e j : ZMod 5)) := by
  -- the norm of `E` in two ways
  have hc : (2 ^ 4 * 5 ^ 2 * (aeval θ ψ) ^ 2 : L8) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hθ)
  set C : L8ˣ := Units.mk0 _ hc
  set W : L8ˣ := Units.map (Algebra.norm L8 : L24 →* L8) z
  set σ : L8ˣ := ∏ j, sgnU (sgnB j) ^ e j
  have hN := congrArg normZ hE
  rw [normZ_apply, norm_Edesc_eq_two_mul_pow θ hθ, map_mul, map_prod, map_pow] at hN
  simp only [map_zpow₀, normZ_apply] at hN
  have hU : (∏ i, U i ^ Sieve.TT i) * C ^ 5 = σ * (∏ i, U i ^ ∑ j, Sieve.NM i j * e j) * W ^ 5 := by
    apply Units.ext
    rw [← prod_NBU_zpow, Units.val_mul, Units.val_mul, two_eq_U]
    simp only [Units.val_pow_eq_pow_val, Units.coe_prod, Units.val_zpow_eq_zpow_val, coe_NBU, C, W,
      Units.val_mk0, Units.coe_map]
    exact hN
  -- hence `∏ u_i^{(Ne - T)_i}` is a fifth power
  have hσ : σ ^ 2 = 1 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, sgnU_sq, one_zpow]
  have hσ5 : σ ^ 5 = σ⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, show 5 + 1 = 2 * 3 by rfl, pow_mul, hσ, one_pow]
  have hF : ∏ i, U i ^ expo e i = (σ * C * W⁻¹) ^ 5 := by
    simp only [expo, zpow_sub, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    rw [← div_eq_mul_inv]
    exact solve_aux _ _ _ _ _ hU hσ5
  -- by Lemma 6.3(i)
  funext i
  have hd := dvd_of_prod_U_eq_pow (expo e) _ hF i
  replace hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (expo e i) 5).mpr (by exact_mod_cast hd)
  rw [expo] at hd
  push_cast at hd
  rw [sub_eq_zero] at hd
  rw [← hd]
  simp [Matrix.mulVec, dotProduct, Matrix.map_apply]
