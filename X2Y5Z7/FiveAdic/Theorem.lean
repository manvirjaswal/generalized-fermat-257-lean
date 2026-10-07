module

public import X2Y5Z7.FiveAdic.Norms

@[expose] public section

/-! # Proposition 4.2: `5 ∤ YZ` and the valuations of `E` at the primes above 5

Let `(X, Y, Z)` be a solution with a root `θ ∈ L₈` of `f_η` generating `L₈` (`Aux.Root`), and
`E = 80000 (θ - b) ψ(θ)³ ∈ L₂₄`. The paper's 5-adic proof (Steps 1–7) is carried out at the primes `Q k` of `L₂₄`
above 5 (`Q k = (B_{k+2})`, the paper's `P₂, …, P₈`), with `n = v₅(η) = 5 v₅(X)`:

* `five_not_dvd_Z`, `five_not_dvd_Y`;
* `ν_E_P3 : ν_{P₃}(E) = 4n + 12`, `ν_E_P5 : ν_{P₅}(E) = 6n + 18`, `ν_E_P6 : ν_{P₆}(E) = 30`,
  `ν_E_P7 : ν_{P₇}(E) = 20`, and `ν_E_pC : ν_P(E) ∈ {6n + 30, 6n + 35, 8n + 35}` for `P = P₂, P₄, P₈`;
* `count_Edesc_mod_five`: the exponents of `P₃, P₅` in `(E)` are `≡ 2, 3 (mod 5)`, and those of
  `P₂, P₄, P₆, P₇, P₈` are `≡ 0 (mod 5)` (condition (V) of Section 7). -/

namespace X2Y5Z7.FiveAdic

open Polynomial IsDedekindDomain NumberField Integral SUnits Prop31
open scoped nonZeroDivisors

noncomputable section

/-! ## The primes of `L₂₄` over `p_A, p_B, p_C` -/

theorem liesOver_pA (k : Fin 7) (hk : k = 4 ∨ k = 5) : (Q k).asIdeal.LiesOver pA.asIdeal := by
  refine liesOver_of_pos pA _ rfl k ?_
  have h := ν_nA k
  change 0 < ν (Q k) (algebraMap L8 L24 (evF v_5 / 820))
  rw [h]
  rcases hk with rfl | rfl <;> decide

theorem liesOver_pB (k : Fin 7) (hk : k = 1 ∨ k = 3) : (Q k).asIdeal.LiesOver pB.asIdeal := by
  refine liesOver_of_pos pB _ rfl k ?_
  have h := ν_nB k
  change 0 < ν (Q k) (algebraMap L8 L24 (evF v_2 / 820))
  rw [h]
  rcases hk with rfl | rfl <;> decide

theorem liesOver_pC (k : Fin 7) (hk : k = 0 ∨ k = 2 ∨ k = 6) : (Q k).asIdeal.LiesOver pC.asIdeal := by
  refine liesOver_of_pos pC _ rfl k ?_
  have h := ν_nC k
  change 0 < ν (Q k) (algebraMap L8 L24 (evF v_1 / 820))
  rw [h]
  rcases hk with rfl | rfl | rfl <;> decide

/-- Over `p_A`: `ν_{P₆}(x) = 2 ν_{P₇}(x)` for `x ∈ L₈`. -/
theorem gA (x : L8) : ν (Q 4) (algebraMap L8 L24 x) = 2 * ν (Q 5) (algebraMap L8 L24 x) := by
  have := group_rel pA 4 5 (liesOver_pA 4 (Or.inl rfl)) (liesOver_pA 5 (Or.inr rfl)) x
  rw [show eQ 4 = 10 from rfl, show eQ 5 = 5 from rfl] at this
  omega

/-- Over `p_B`: `ν_{P₅}(x) = 2 ν_{P₃}(x)` for `x ∈ L₈`. -/
theorem gB (x : L8) : ν (Q 3) (algebraMap L8 L24 x) = 2 * ν (Q 1) (algebraMap L8 L24 x) := by
  have := group_rel pB 3 1 (liesOver_pB 3 (Or.inr rfl)) (liesOver_pB 1 (Or.inl rfl)) x
  rw [show eQ 3 = 2 from rfl, show eQ 1 = 1 from rfl] at this
  omega

/-- Over `p_C`: `ν_{P₂}(x) = ν_{P₄}(x) = ν_{P₈}(x)` for `x ∈ L₈`. -/
theorem gC (x : L8) : ν (Q 0) (algebraMap L8 L24 x) = ν (Q 2) (algebraMap L8 L24 x) ∧
    ν (Q 6) (algebraMap L8 L24 x) = ν (Q 2) (algebraMap L8 L24 x) := by
  have h1 := group_rel pC 0 2 (liesOver_pC 0 (Or.inl rfl)) (liesOver_pC 2 (Or.inr (Or.inl rfl))) x
  have h2 := group_rel pC 6 2 (liesOver_pC 6 (Or.inr (Or.inr rfl))) (liesOver_pC 2 (Or.inr (Or.inl rfl))) x
  rw [show eQ 0 = 2 from rfl, show eQ 2 = 2 from rfl] at h1
  rw [show eQ 6 = 2 from rfl, show eQ 2 = 2 from rfl] at h2
  omega

/-! ## The solution -/

variable {s : Solution} (R : Aux.Root s)

/-- `θ` in `L₂₄`. -/
def θL : L24 := algebraMap L8 L24 R.θ

theorem θL_root : aeval (θL R) (fpoly s.η) = 0 := by
  rw [θL, aeval_algebraMap_apply, R.root, map_zero]

theorem ν_η (k : Fin 7) : ν (Q k) (algebraMap ℚ L24 s.η) = eQ k * padicValRat 5 s.η :=
  ν_ratCast k _ (η_ne_zero s)

theorem padicValRat_η : padicValRat 5 s.η = 5 * (padicValInt 5 s.X : ℤ) - 7 * (padicValInt 5 s.Z : ℤ) := by
  have hX : (s.X : ℚ) ≠ 0 := Int.cast_ne_zero.mpr s.X_ne
  have hZ : (s.Z : ℚ) ≠ 0 := Int.cast_ne_zero.mpr s.Z_ne
  rw [Solution.η, padicValRat.div (pow_ne_zero _ hX) (pow_ne_zero _ hZ), padicValRat.pow, padicValRat.pow,
    padicValRat.of_int, padicValRat.of_int]
  push_cast
  ring

theorem η_sub_one : s.η - 1 = -((s.Y : ℚ) ^ 2 / (s.Z : ℚ) ^ 7) := by
  have hZ : (s.Z : ℚ) ≠ 0 := Int.cast_ne_zero.mpr s.Z_ne
  have h : (s.X : ℚ) ^ 5 + (s.Y : ℚ) ^ 2 = (s.Z : ℚ) ^ 7 := by exact_mod_cast s.eq
  rw [Solution.η]
  field_simp
  linear_combination h

theorem η_sub_one_ne : s.η - 1 ≠ 0 := by
  rw [η_sub_one]
  exact neg_ne_zero.mpr (div_ne_zero (pow_ne_zero _ (Int.cast_ne_zero.mpr s.Y_ne))
    (pow_ne_zero _ (Int.cast_ne_zero.mpr s.Z_ne)))

theorem padicValRat_η_sub_one :
    padicValRat 5 (s.η - 1) = 2 * (padicValInt 5 s.Y : ℤ) - 7 * (padicValInt 5 s.Z : ℤ) := by
  have hY : (s.Y : ℚ) ≠ 0 := Int.cast_ne_zero.mpr s.Y_ne
  have hZ : (s.Z : ℚ) ≠ 0 := Int.cast_ne_zero.mpr s.Z_ne
  rw [η_sub_one, padicValRat.neg, padicValRat.div (pow_ne_zero _ hY) (pow_ne_zero _ hZ), padicValRat.pow,
    padicValRat.pow, padicValRat.of_int, padicValRat.of_int]
  push_cast
  ring

theorem ν_η_sub_one (k : Fin 7) :
    ν (Q k) (algebraMap ℚ L24 s.η - 1) = eQ k * padicValRat 5 (s.η - 1) := by
  rw [← ν_ratCast k _ η_sub_one_ne, map_sub, map_one]

theorem η_sub_one_ne' : algebraMap ℚ L24 s.η - 1 ≠ 0 := by
  rw [← map_one (algebraMap ℚ L24), ← map_sub]
  exact (map_ne_zero_iff _ (algebraMap ℚ L24).injective).mpr η_sub_one_ne

/-- `θ - c ≠ 0` when `f_η(c) ≠ 0`. -/
theorem θL_sub_ne (c : ℚ) (hc : (fpoly s.η).eval c ≠ 0) : θL R - algebraMap ℚ L24 c ≠ 0 := by
  intro h0
  rw [sub_eq_zero] at h0
  apply hc
  have := θL_root R
  rw [h0, aeval_algebraMap_apply, map_eq_zero_iff _ (algebraMap ℚ L24).injective] at this
  simpa [Polynomial.coe_aeval_eq_eval] using this

theorem sum_θ (c : ℚ) (hc : (fpoly s.η).eval c ≠ 0) :
    ∑ k : Fin 7, ν (Q k) (θL R - algebraMap ℚ L24 c) = 3 * (padicValRat 5 ((fpoly s.η).eval c) - 2) :=
  sum_ν_sub_rat R.root R.gen c hc

theorem θL_sub (c : ℚ) : θL R - algebraMap ℚ L24 c = algebraMap L8 L24 (R.θ - algebraMap ℚ L8 c) := by
  rw [θL, map_sub, ← IsScalarTower.algebraMap_apply]

theorem fpoly_quarter_val (η : ℚ) : (fpoly η).eval (1 / 4) = 1225 / 16384 := by
  rw [fpoly_eval]; ring

theorem padicValRat_quarter : padicValRat 5 (1225 / 16384 : ℚ) = 2 := by
  have := padicValRat_const 2 49 16384 (by decide) (by decide)
  norm_num at this ⊢
  exact this

/-! ## Step 1: `5 ∤ Z` -/

/-- **Proposition 4.2** (Step 1): `5 ∤ Z`. -/
theorem five_not_dvd_Z (s : Solution) (R : Aux.Root s) : ¬ (5 : ℤ) ∣ s.Z := by
  intro h5
  have hX : ¬ (5 : ℤ) ∣ s.X := by
    intro hX5
    obtain ⟨u, w, huw⟩ := s.coprime
    have : (5 : ℤ) ∣ u * s.X + w * s.Z := dvd_add (dvd_mul_of_dvd_right hX5 u) (dvd_mul_of_dvd_right h5 w)
    rw [huw] at this
    norm_num at this
  have hm : 1 ≤ padicValInt 5 s.Z := by
    unfold padicValInt
    exact one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr s.Z_ne) (Int.ofNat_dvd_left.mp h5)
  set m : ℤ := (padicValInt 5 s.Z : ℤ) with hmdef
  have hv : padicValRat 5 s.η = -7 * m := by
    rw [padicValRat_η, padicValInt.eq_zero_of_not_dvd hX]
    push_cast
    ring
  -- at each prime: `ν(4θ - 1) = (2 + 7m) e`
  have hk : ∀ k : Fin 7, ν (Q k) (θL R - algebraMap ℚ L24 (1 / 4)) = (2 + 7 * m) * eQ k := by
    intro k
    have he := ν_five k
    have he0 := eQ_pos k
    have hN : ν (Q k) (algebraMap ℚ L24 s.η) = -7 * m * eQ k := by rw [ν_η, hv]; ring
    have h7 : ¬ (7 : ℤ) ∣ ν (Q k) (algebraMap ℚ L24 s.η) - 2 * eQ k := by
      rw [hN]
      fin_cases k <;> simp [eQ] <;> omega
    have h1 := step1_local he he0 (hZ_Q k) (η_ne_zero s) (θL_root R) (by rw [hN]; nlinarith) h7
    have h4 : θL R - algebraMap ℚ L24 (1 / 4) = (4 * θL R - 1) / 4 := by
      rw [map_div₀, map_one, map_ofNat]; ring
    rw [h4, ν_div (four_θ_sub_one_ne (η_ne_zero s) (θL_root R)) (by norm_num), h1,
      ν_unit_const (x := (4 : L24)) he (hZ_Q k) 4 1 (by decide) (by decide) (by norm_num), hN]
    ring
  have hsum := sum_θ R (1 / 4) (by rw [fpoly_quarter_val]; norm_num)
  rw [fpoly_quarter_val, padicValRat_quarter] at hsum
  simp only [hk, Fin.sum_univ_seven] at hsum
  simp only [eQ] at hsum
  norm_num at hsum
  omega

/-! ## Steps 2 and 3: the valuations of `θ` -/

/-- `n = v₅(η) = 5 v₅(X) ≥ 0` once `5 ∤ Z`. -/
theorem padicValRat_η_of (hZ5 : ¬ (5 : ℤ) ∣ s.Z) : padicValRat 5 s.η = 5 * (padicValInt 5 s.X : ℤ) := by
  rw [padicValRat_η, padicValInt.eq_zero_of_not_dvd hZ5]
  push_cast
  ring

theorem fpoly_zero_val (η : ℚ) : (fpoly η).eval 0 = η := by rw [fpoly_eval]; ring

theorem fpoly_one_val (η : ℚ) : (fpoly η).eval 1 = 292 - 3 * η := by rw [fpoly_eval]; ring

/-- `v₅(292 - 3η) = 0` when `v₅(η) > 0`. -/
theorem padicValRat_292 {η : ℚ} (hη : η ≠ 0) (hv : 0 < padicValRat 5 η) : padicValRat 5 (292 - 3 * η) = 0 := by
  have h292 : padicValRat 5 (292 : ℚ) = 0 := by
    have := padicValRat_const 0 292 1 (by decide) (by decide)
    norm_num at this ⊢
    exact this
  have h3 : padicValRat 5 (-3 * η) = padicValRat 5 η := by
    rw [padicValRat.mul (by norm_num) hη]
    have : padicValRat 5 (-3 : ℚ) = 0 := by
      have := padicValRat_const 0 (-3) 1 (by decide) (by decide)
      norm_num at this ⊢
      exact this
    rw [this, zero_add]
  have hne : (292 : ℚ) + -3 * η ≠ 0 := by
    intro h0
    have : η = 292 / 3 := by linarith
    rw [this] at hv
    have : padicValRat 5 (292 / 3 : ℚ) = 0 := by
      have := padicValRat_const 0 292 3 (by decide) (by decide)
      norm_num at this ⊢
      exact this
    omega
  rw [sub_eq_add_neg, show -(3 * η) = -3 * η by ring,
    padicValRat.add_eq_of_lt hne (by norm_num) (mul_ne_zero (by norm_num) hη) (by rw [h292, h3]; exact hv), h292]


/-- The counting of Steps 2–3 (`n > 0`), as integer arithmetic. -/
theorem θ_arith_pos (n : ℤ) (hn : 0 < n) (h5n : (5 : ℤ) ∣ n) (t0 t1 t2 t3 t4 t5 t6 u0 u1 u2 u3 u4 u5 u6 : ℤ)
    (h1 : t1 = -1 ∨ t1 = 0 ∨ (0 < t1 ∧ 5 * t1 = 1 * n))
    (h2 : t2 = -2 ∨ t2 = 0 ∨ (0 < t2 ∧ 5 * t2 = 2 * n))
    (h5 : t5 = -5 ∨ t5 = 0 ∨ (0 < t5 ∧ 5 * t5 = 5 * n))
    (gA : t4 = 2 * t5) (gB : t3 = 2 * t1) (gC0 : t0 = t2) (gC6 : t6 = t2)
    (hs : t0 + t1 + t2 + t3 + t4 + t5 + t6 = 3 * (n - 2))
    (hu : u0 + u1 + u2 + u3 + u4 + u5 + u6 = 3 * (0 - 2))
    (uA : u4 = 2 * u5) (uB : u3 = 2 * u1) (uC0 : u0 = u2) (uC6 : u6 = u2)
    (v1 : (t1 < 0 → u1 = t1) ∧ (0 < t1 → u1 = 0) ∧ (t1 = 0 → 0 ≤ u1))
    (v2 : (t2 < 0 → u2 = t2) ∧ (0 < t2 → u2 = 0) ∧ (t2 = 0 → 0 ≤ u2))
    (v5 : (t5 < 0 → u5 = t5) ∧ (0 < t5 → u5 = 0) ∧ (t5 = 0 → 0 ≤ u5)) :
    t0 = -2 ∧ t2 = -2 ∧ t6 = -2 ∧ t1 = 0 ∧ t3 = 0 ∧ t5 = n ∧ t4 = 2 * n := by
  obtain ⟨a, rfl⟩ := h5n
  subst gA gB gC0 gC6 uA uB uC0 uC6
  obtain ⟨v1a, v1b, v1c⟩ := v1
  obtain ⟨v2a, v2b, v2c⟩ := v2
  obtain ⟨v5a, v5b, v5c⟩ := v5
  rcases h1 with h1 | h1 | ⟨h1a, h1b⟩ <;> rcases h2 with h2 | h2 | ⟨h2a, h2b⟩ <;>
    rcases h5 with h5 | h5 | ⟨h5a, h5b⟩ <;> omega

/-- The per-prime alternatives for `θ` (Steps 2–3, local part). -/
theorem θ_alt (hZ5 : ¬ (5 : ℤ) ∣ s.Z) (k : Fin 7) :
    ν (Q k) (θL R) = -eQ k ∨ ν (Q k) (θL R) = 0 ∨
      (0 < ν (Q k) (θL R) ∧ 5 * ν (Q k) (θL R) = eQ k * padicValRat 5 s.η) := by
  have hn := padicValRat_η_of hZ5
  have := ν_θ_cases_nonneg (ν_five k) (eQ_pos k) (hZ_Q k) (η_ne_zero s) (θL_root R)
    (by rw [ν_η, hn]; have := eQ_pos k; positivity)
  rwa [ν_η] at this

/-- **Steps 2–3**: `ν(θ) = -2` at `P₂, P₄, P₈` (`p_C`), `0` at `P₃, P₅` (`p_B`), `n` at `P₇` and `2n` at `P₆`
(`p_A`), where `n = v₅(η)`. -/
theorem θ_vals (hZ5 : ¬ (5 : ℤ) ∣ s.Z) :
    ν (Q 0) (θL R) = -2 ∧ ν (Q 2) (θL R) = -2 ∧ ν (Q 6) (θL R) = -2 ∧ ν (Q 1) (θL R) = 0 ∧
      ν (Q 3) (θL R) = 0 ∧ ν (Q 5) (θL R) = padicValRat 5 s.η ∧ ν (Q 4) (θL R) = 2 * padicValRat 5 s.η := by
  have hn := padicValRat_η_of hZ5
  set n := padicValRat 5 s.η with hndef
  have hn0 : 0 ≤ n := by rw [hn]; positivity
  have h5n : (5 : ℤ) ∣ n := by rw [hn]; exact dvd_mul_right _ _
  have gθA := gA R.θ
  have gθB := gB R.θ
  have gθC := gC R.θ
  change ν (Q 4) (θL R) = 2 * ν (Q 5) (θL R) at gθA
  change ν (Q 3) (θL R) = 2 * ν (Q 1) (θL R) at gθB
  change ν (Q 0) (θL R) = ν (Q 2) (θL R) ∧ ν (Q 6) (θL R) = ν (Q 2) (θL R) at gθC
  have h1 := θ_alt R hZ5 1
  have h2 := θ_alt R hZ5 2
  have h5 := θ_alt R hZ5 5
  rw [show eQ 1 = 1 from rfl] at h1
  rw [show eQ 2 = 2 from rfl] at h2
  rw [show eQ 5 = 5 from rfl] at h5
  have hsum0 := sum_θ R 0 (by rw [fpoly_zero_val]; exact η_ne_zero s)
  rw [fpoly_zero_val, map_zero, Fin.sum_univ_seven] at hsum0
  simp only [sub_zero] at hsum0
  rcases eq_or_lt_of_le hn0 with hn0' | hnpos
  · -- `n = 0`
    omega
  · -- `n > 0`: also use `θ - 1`
    have hc1 : (fpoly s.η).eval 1 ≠ 0 := by
      rw [fpoly_one_val]; intro h0
      have h3 : s.η = 292 / 3 := by linarith
      have := hnpos
      rw [hndef, h3] at this
      have h' : padicValRat 5 (292 / 3 : ℚ) = 0 := by
        have := padicValRat_const 0 292 3 (by decide) (by decide)
        norm_num at this ⊢
        exact this
      omega
    have hsum1 := sum_θ R 1 hc1
    rw [fpoly_one_val, padicValRat_292 (η_ne_zero s) (by omega), map_one, Fin.sum_univ_seven] at hsum1
    have gA1 := gA (R.θ - algebraMap ℚ L8 1)
    have gB1 := gB (R.θ - algebraMap ℚ L8 1)
    have gC1 := gC (R.θ - algebraMap ℚ L8 1)
    rw [← θL_sub, map_one] at gA1 gB1 gC1
    have hθ0 := θ_ne_zero (η_ne_zero s) (θL_root R)
    have hne1 : θL R - 1 ≠ 0 := by
      have := θL_sub_ne R 1 hc1; rwa [map_one] at this
    have u1 := ν_sub_unit (v := Q 1) hθ0 one_ne_zero ν_one hne1
    have u2 := ν_sub_unit (v := Q 2) hθ0 one_ne_zero ν_one hne1
    have u5 := ν_sub_unit (v := Q 5) hθ0 one_ne_zero ν_one hne1
    exact θ_arith_pos n hnpos h5n _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h5 gθA gθB gθC.1 gθC.2
      (by rw [← hndef] at hsum0; exact hsum0) (by simpa using hsum1) gA1 gB1 gC1.1 gC1.2 u1 u2 u5

/-! ## Steps 4 and 5: the unit roots near `1/4` -/

theorem quarter_eq : algebraMap ℚ L24 (1 / 4) = (1 / 4 : L24) := by
  rw [map_div₀, map_one, map_ofNat]

theorem fpoly_quarter_ne : (fpoly s.η).eval (1 / 4) ≠ 0 := by rw [fpoly_quarter_val]; norm_num

/-- When `n = 0`: `ν_{P₃}(θ - 1/4) + ν_{P₇}(θ - 1/4) = 2`, both `≥ 0` (from `Σ_k ν_k(θ - 1/4) = 0`). -/
theorem quarter_sum (hZ5 : ¬ (5 : ℤ) ∣ s.Z) (hn : padicValRat 5 s.η = 0) :
    ν (Q 1) (θL R - 1 / 4) + ν (Q 5) (θL R - 1 / 4) = 2 ∧ 0 ≤ ν (Q 1) (θL R - 1 / 4) ∧
      0 ≤ ν (Q 5) (θL R - 1 / 4) := by
  obtain ⟨t0, t2, t6, t1, t3, t5, t4⟩ := θ_vals R hZ5
  rw [hn] at t5 t4
  have hsum := sum_θ R (1 / 4) fpoly_quarter_ne
  rw [fpoly_quarter_val, padicValRat_quarter, quarter_eq, Fin.sum_univ_seven] at hsum
  have gA' := gA (R.θ - algebraMap ℚ L8 (1 / 4))
  have gB' := gB (R.θ - algebraMap ℚ L8 (1 / 4))
  have gC' := gC (R.θ - algebraMap ℚ L8 (1 / 4))
  rw [← θL_sub, quarter_eq] at gA' gB' gC'
  have hθ0 := θ_ne_zero (η_ne_zero s) (θL_root R)
  have hne : θL R - 1 / 4 ≠ 0 := by
    have := θL_sub_ne R (1 / 4) fpoly_quarter_ne; rwa [quarter_eq] at this
  have hq : ∀ k : Fin 7, ν (Q k) (1 / 4 : L24) = 0 := fun k =>
    ν_unit_const (ν_five k) (hZ_Q k) 1 4 (by decide) (by decide) (by norm_num)
  have u2 := ν_sub_unit (v := Q 2) hθ0 (by norm_num) (hq 2) hne
  have u1 := ν_sub_unit (v := Q 1) hθ0 (by norm_num) (hq 1) hne
  have u5 := ν_sub_unit (v := Q 5) hθ0 (by norm_num) (hq 5) hne
  have w2 := u2.1 (by omega)
  have w1 := u1.2.2 t1
  have w5 := u5.2.2 t5
  omega

/-- **Step 4**: `5 ∤ Y`. -/
theorem five_not_dvd_Y (s : Solution) (R : Aux.Root s) : ¬ (5 : ℤ) ∣ s.Y := by
  intro hY5
  have hZ5 := five_not_dvd_Z s R
  have hX5 : ¬ (5 : ℤ) ∣ s.X := by
    intro hX5
    obtain ⟨u, w, huw⟩ := s.coprime_XY
    have : (5 : ℤ) ∣ u * s.X + w * s.Y := dvd_add (dvd_mul_of_dvd_right hX5 u) (dvd_mul_of_dvd_right hY5 w)
    rw [huw] at this
    norm_num at this
  have hn : padicValRat 5 s.η = 0 := by
    rw [padicValRat_η_of hZ5, padicValInt.eq_zero_of_not_dvd hX5]; rfl
  have hY1 : 1 ≤ padicValInt 5 s.Y := by
    unfold padicValInt
    exact one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr s.Y_ne) (Int.ofNat_dvd_left.mp hY5)
  have hη1 : ∀ k : Fin 7, Ge (Q k) (2 * eQ k) (algebraMap ℚ L24 s.η - 1) := by
    intro k
    refine Ge.of_ν ?_
    rw [ν_η_sub_one, padicValRat_η_sub_one, padicValInt.eq_zero_of_not_dvd hZ5]
    have := eQ_pos k
    push_cast
    nlinarith
  obtain ⟨t0, t2, t6, t1, t3, t5, t4⟩ := θ_vals R hZ5
  rw [hn] at t5
  obtain ⟨hs, hw1, hw5⟩ := quarter_sum R hZ5 hn
  have p1 := step4_pos (ν_five 1) (eQ_pos 1) (hZ_Q 1) (le_of_eq t1.symm) (θL_root R) (hη1 1)
  have p5 := step4_pos (ν_five 5) (eQ_pos 5) (hZ_Q 5) (le_of_eq t5.symm) (θL_root R) (hη1 5)
  have hne : θL R - 1 / 4 ≠ 0 := by
    have := θL_sub_ne R (1 / 4) fpoly_quarter_ne; rwa [quarter_eq] at this
  have p1' : 1 ≤ ν (Q 1) (θL R - 1 / 4) := by rcases p1 with h | h; exact absurd h hne; exact h
  have p5' : 1 ≤ ν (Q 5) (θL R - 1 / 4) := by rcases p5 with h | h; exact absurd h hne; exact h
  exact step4_ne (ν_five 1) (eQ_pos 1) (hZ_Q 1) (le_of_eq t1.symm) (θL_root R) (hη1 1) (by
    rw [show eQ 1 = 1 from rfl]; omega)

/-- **Step 5**: when `n = 0`, `ν_{P₃}(θ - 1/4) = 2` and `ν_{P₇}(θ - 1/4) = 0`. -/
theorem step5_vals (hn : padicValRat 5 s.η = 0) :
    ν (Q 1) (θL R - 1 / 4) = 2 ∧ ν (Q 5) (θL R - 1 / 4) = 0 := by
  have hZ5 := five_not_dvd_Z s R
  have hY5 := five_not_dvd_Y s R
  obtain ⟨t0, t2, t6, t1, t3, t5, t4⟩ := θ_vals R hZ5
  rw [hn] at t5
  obtain ⟨hs, hw1, hw5⟩ := quarter_sum R hZ5 hn
  have hη1 : ∀ k : Fin 7, ν (Q k) (algebraMap ℚ L24 s.η - 1) = 0 := by
    intro k
    rw [ν_η_sub_one, padicValRat_η_sub_one, padicValInt.eq_zero_of_not_dvd hZ5,
      padicValInt.eq_zero_of_not_dvd hY5]
    simp
  have hne : θL R - 1 / 4 ≠ 0 := by
    have := θL_sub_ne R (1 / 4) fpoly_quarter_ne; rwa [quarter_eq] at this
  have q1 : ν (Q 1) (θL R - 1 / 4) = 0 ∨ ν (Q 1) (θL R - 1 / 4) = 2 := by
    rcases eq_or_lt_of_le hw1 with h | h
    · exact Or.inl h.symm
    · right
      have := step5 (ν_five 1) (eQ_pos 1) (hZ_Q 1) (le_of_eq t1.symm) (θL_root R) η_sub_one_ne' (hη1 1) hne h
      rw [this]; rfl
  have q5 : ν (Q 5) (θL R - 1 / 4) = 0 ∨ ν (Q 5) (θL R - 1 / 4) = 10 := by
    rcases eq_or_lt_of_le hw5 with h | h
    · exact Or.inl h.symm
    · right
      have := step5 (ν_five 5) (eQ_pos 5) (hZ_Q 5) (le_of_eq t5.symm) (θL_root R) η_sub_one_ne' (hη1 5) hne h
      rw [this]; rfl
  omega

/-! ## Steps 6 and 7: the valuations of `E` -/

/-- The descent element `E = 80000 (θ - b) ψ(θ)³` of the solution. -/
abbrev Esol : L24 := Edesc (θL R)

theorem ψθL : aeval (θL R) ψ = algebraMap L8 L24 (aeval R.θ ψ) := by
  rw [θL, aeval_algebraMap_apply]

/-- `ν_{P₃}(ψ(θ)) = ν_{P₃}(θ - b) = n + 2` (Step 6(b)). -/
theorem ν_P3_ψ : ν (Q 1) (aeval (θL R) ψ) = padicValRat 5 s.η + 2 ∧
    ν (Q 1) (θL R - b) = padicValRat 5 s.η + 2 := by
  have hZ5 := five_not_dvd_Z s R
  obtain ⟨t0, t2, t6, t1, t3, t5, t4⟩ := θ_vals R hZ5
  have hb := b_types.1
  have hN : ν (Q 1) (algebraMap ℚ L24 s.η) = padicValRat 5 s.η := by
    rw [ν_η, show eQ 1 = 1 from rfl, one_mul]
  have hsb := ν_sub_b_of_b1 (ν_five 1) (eQ_pos 1) (hZ_Q 1) (η_ne_zero s) (θL_root R) hb t1
  have hn0 : 0 ≤ padicValRat 5 s.η := by rw [padicValRat_η_of hZ5]; positivity
  have hψ : ν (Q 1) (aeval (θL R) ψ) = padicValRat 5 s.η + 2 := by
    rcases eq_or_lt_of_le hn0 with h0 | hpos
    · have h5 := (step5_vals R h0.symm).1
      have h4 : ν (Q 1) (4 * θL R - 1) = 2 := by
        rw [show 4 * θL R - 1 = 4 * (θL R - 1 / 4) by ring, ν_mul (by norm_num) (by
          have := θL_sub_ne R (1 / 4) fpoly_quarter_ne; rwa [quarter_eq] at this), h5,
          ν_unit_const (ν_five 1) (hZ_Q 1) 4 1 (by decide) (by decide) (by norm_num)]
        rfl
      rw [ν_ψ_of_zero (ν_five 1) (hZ_Q 1) (η_ne_zero s) (θL_root R) t1, h4, hN]
    · have := pB_pos (ν_five 1) (eQ_pos 1) (hZ_Q 1) (η_ne_zero s) (θL_root R) hb t1 (by rw [hN]; exact hpos)
      rw [this, hN, show eQ 1 = 1 from rfl]
      ring
  exact ⟨hψ, hsb.trans hψ⟩

/-- **Proposition 4.2**, `P₃` (label `(1,1,1)`): `ν(E) = 4n + 12`. -/
theorem ν_E_P3 : ν (Q 1) (Esol R) = 4 * padicValRat 5 s.η + 12 := by
  obtain ⟨hψ, hsb⟩ := ν_P3_ψ R
  rw [Esol, ν_Edesc (ν_five 1) (hZ_Q 1) (η_ne_zero s) (θL_root R), hψ, hsb, show eQ 1 = 1 from rfl]
  ring

/-- **Proposition 4.2**, `P₅` (label `(2,1,1)`): `ν(E) = 6n + 18`. -/
theorem ν_E_P5 : ν (Q 3) (Esol R) = 6 * padicValRat 5 s.η + 18 := by
  have hZ5 := five_not_dvd_Z s R
  obtain ⟨t0, t2, t6, t1, t3, t5, t4⟩ := θ_vals R hZ5
  obtain ⟨hψ, -⟩ := ν_P3_ψ R
  have hψ3 : ν (Q 3) (aeval (θL R) ψ) = 2 * (padicValRat 5 s.η + 2) := by
    rw [ψθL, gB, ← ψθL, hψ]
  have hsb := sub_b2 (e := 2) (by norm_num) b_types.2.2.1 (le_of_eq t3.symm)
  rw [Esol, ν_Edesc (ν_five 3) (hZ_Q 3) (η_ne_zero s) (θL_root R), hψ3, hsb, show eQ 3 = 2 from rfl]
  ring

/-- `ν_{P₇}(ψ(θ)) = 0` and `ν_{P₇}(θ - b) = 0` (Step 6(a)). -/
theorem ν_P7 : ν (Q 5) (aeval (θL R) ψ) = 0 ∧ ν (Q 5) (θL R - b) = 0 := by
  have hZ5 := five_not_dvd_Z s R
  obtain ⟨t0, t2, t6, t1, t3, t5, t4⟩ := θ_vals R hZ5
  have hb := b_types.2.1
  have hn0 : 0 ≤ padicValRat 5 s.η := by rw [padicValRat_η_of hZ5]; positivity
  have hθ0 := θ_ne_zero (η_ne_zero s) (θL_root R)
  rcases eq_or_lt_of_le hn0 with h0 | hpos
  · rw [← h0] at t5
    have h5 := (step5_vals R h0.symm).2
    have hne : θL R - 1 / 4 ≠ 0 := by
      have := θL_sub_ne R (1 / 4) fpoly_quarter_ne; rwa [quarter_eq] at this
    refine ⟨?_, pA_zero (ν_five 5) (eQ_pos 5) (hZ_Q 5) hb hne h5⟩
    have h4 : ν (Q 5) (4 * θL R - 1) = 0 := by
      rw [show 4 * θL R - 1 = 4 * (θL R - 1 / 4) by ring, ν_mul (by norm_num) hne, h5,
        ν_unit_const (ν_five 5) (hZ_Q 5) 4 1 (by decide) (by decide) (by norm_num)]
      rfl
    rw [ν_ψ_of_zero (ν_five 5) (hZ_Q 5) (η_ne_zero s) (θL_root R) t5, h4, ν_η, ← h0]
    ring
  · have ht : 0 < ν (Q 5) (θL R) := by rw [t5]; exact hpos
    exact ⟨ν_ψ_of_pos (ν_five 5) (hZ_Q 5) hθ0 (eQ_pos 5) ht, pA_pos hb ht⟩

/-- **Proposition 4.2**, `P₇` (label `(5,1,5)`): `ν(E) = 20`. -/
theorem ν_E_P7 : ν (Q 5) (Esol R) = 20 := by
  obtain ⟨hψ, hsb⟩ := ν_P7 R
  rw [Esol, ν_Edesc (ν_five 5) (hZ_Q 5) (η_ne_zero s) (θL_root R), hψ, hsb, show eQ 5 = 5 from rfl]
  ring

/-- **Proposition 4.2**, `P₆` (label `(10,1,5)`): `ν(E) = 30`. -/
theorem ν_E_P6 : ν (Q 4) (Esol R) = 30 := by
  have hZ5 := five_not_dvd_Z s R
  obtain ⟨t0, t2, t6, t1, t3, t5, t4⟩ := θ_vals R hZ5
  obtain ⟨hψ, -⟩ := ν_P7 R
  have hψ4 : ν (Q 4) (aeval (θL R) ψ) = 0 := by
    rw [ψθL, gA, ← ψθL, hψ]; ring
  have hn0 : 0 ≤ padicValRat 5 s.η := by rw [padicValRat_η_of hZ5]; positivity
  have hsb := sub_b2 (e := 10) (by norm_num) b_types.2.2.2 (by rw [t4]; omega)
  rw [Esol, ν_Edesc (ν_five 4) (hZ_Q 4) (η_ne_zero s) (θL_root R), hψ4, hsb, show eQ 4 = 10 from rfl]
  ring

theorem ν_E_pC_of (k : Fin 7) (he : eQ k = 2) (ht2 : ν (Q k) (θL R) = -2) :
    ν (Q k) (Esol R) = 6 * padicValRat 5 s.η + 30 ∨ ν (Q k) (Esol R) = 6 * padicValRat 5 s.η + 35 ∨
      ν (Q k) (Esol R) = 8 * padicValRat 5 s.η + 35 := by
  have hZ5 := five_not_dvd_Z s R
  have ht : ν (Q k) (θL R) = -eQ k := by rw [he, ht2]
  have hn0 : 0 ≤ padicValRat 5 s.η := by rw [padicValRat_η_of hZ5]; positivity
  have hψ := ν_ψ_of_neg_e (ν_five k) (eQ_pos k) (hZ_Q k) (η_ne_zero s) (θL_root R) ht
  rw [ν_η, he] at hψ
  have hE := ν_Edesc (ν_five k) (hZ_Q k) (η_ne_zero s) (θL_root R)
  rw [hψ, he] at hE
  rw [Esol, hE]
  rcases ν_b_Q k with hb | hb
  · have := pC_b1 (eQ_pos k) (η_ne_zero s) (θL_root R) hb ht
    rw [this, he]
    left; ring
  · have hd := ν_dψ k
    rw [hb, he] at hd
    have := pC_b2 (ν_five k) (eQ_pos k) (hZ_Q k) (η_ne_zero s) (θL_root R) hb ht dψ_ne_zero
      (by rw [he]; omega) (by rw [ν_η]; positivity)
    rw [ν_η, he] at this
    omega

/-- **Proposition 4.2**, `P₂, P₄, P₈` (label `(2,1,2)`): `ν(E) ∈ {6n + 30, 6n + 35, 8n + 35}`. -/
theorem ν_E_pC (k : Fin 7) (hk : k = 0 ∨ k = 2 ∨ k = 6) :
    ν (Q k) (Esol R) = 6 * padicValRat 5 s.η + 30 ∨ ν (Q k) (Esol R) = 6 * padicValRat 5 s.η + 35 ∨
      ν (Q k) (Esol R) = 8 * padicValRat 5 s.η + 35 := by
  obtain ⟨t0, t2, t6, -⟩ := θ_vals R (five_not_dvd_Z s R)
  rcases hk with rfl | rfl | rfl
  · exact ν_E_pC_of R 0 rfl t0
  · exact ν_E_pC_of R 2 rfl t2
  · exact ν_E_pC_of R 6 rfl t6

/-! ## Proposition 4.2 in terms of the primes `(B_i)` -/

theorem Esol_ne_zero : Esol R ≠ 0 := Edesc_ne_zero s.η (η_ne_zero s) _ (θL_root R)

/-- `n = v₅(η) = 5 v₅(X)`. -/
theorem padicValRat_η_eq (s : Solution) (R : Aux.Root s) :
    padicValRat 5 s.η = 5 * (padicValInt 5 s.X : ℤ) :=
  padicValRat_η_of (five_not_dvd_Z s R)

theorem count_eq (k : Fin 7) (v : HeightOneSpectrum (𝓞 L24)) (hv : v.asIdeal = Ideal.span {Bint (idx k)}) :
    FractionalIdeal.count L24 v (FractionalIdeal.spanSingleton (𝓞 L24)⁰ (Edesc (algebraMap L8 L24 R.θ))) =
      ν (Q k) (Esol R) := by
  have : v = Q k := HeightOneSpectrum.ext hv
  subst this
  exact count_eq_ν _ (Esol_ne_zero R)

/-- **Proposition 4.2** (exact values). With `n = v₅(η) = 5 v₅(X)`, the exponent of `P_{i+1} = (B_{i+1})` in `(E)`
is `4n + 12` at `P₃`, `6n + 18` at `P₅`, `30` at `P₆`, `20` at `P₇`, and one of `6n + 30, 6n + 35, 8n + 35` at
`P₂, P₄, P₈`. -/
theorem count_Edesc_values (s : Solution) (R : Aux.Root s) (v : HeightOneSpectrum (𝓞 L24)) :
    let c := FractionalIdeal.count L24 v
      (FractionalIdeal.spanSingleton (𝓞 L24)⁰ (Edesc (algebraMap L8 L24 R.θ)))
    let n := 5 * (padicValInt 5 s.X : ℤ)
    (v.asIdeal = Ideal.span {Bint 2} → c = 4 * n + 12) ∧
    (v.asIdeal = Ideal.span {Bint 4} → c = 6 * n + 18) ∧
    (v.asIdeal = Ideal.span {Bint 5} → c = 30) ∧
    (v.asIdeal = Ideal.span {Bint 6} → c = 20) ∧
    (v.asIdeal = Ideal.span {Bint 1} ∨ v.asIdeal = Ideal.span {Bint 3} ∨ v.asIdeal = Ideal.span {Bint 7} →
      c = 6 * n + 30 ∨ c = 6 * n + 35 ∨ c = 8 * n + 35) := by
  intro c n
  have hn : padicValRat 5 s.η = n := padicValRat_η_eq s R
  refine ⟨fun hv => ?_, fun hv => ?_, fun hv => ?_, fun hv => ?_, fun hv => ?_⟩
  · rw [show c = _ from count_eq R 1 v hv, ν_E_P3, hn]
  · rw [show c = _ from count_eq R 3 v hv, ν_E_P5, hn]
  · rw [show c = _ from count_eq R 4 v hv, ν_E_P6]
  · rw [show c = _ from count_eq R 5 v hv, ν_E_P7]
  · rcases hv with hv | hv | hv
    · rw [show c = _ from count_eq R 0 v hv, ← hn]; exact ν_E_pC R 0 (Or.inl rfl)
    · rw [show c = _ from count_eq R 2 v hv, ← hn]; exact ν_E_pC R 2 (Or.inr (Or.inl rfl))
    · rw [show c = _ from count_eq R 6 v hv, ← hn]; exact ν_E_pC R 6 (Or.inr (Or.inr rfl))

/-- **Proposition 4.2** at `P₃ = (B₃)` (label `(1,1,1)`): the exponent of `P₃` in `(E)` is `≡ 2 (mod 5)`. -/
theorem count_Edesc_P3 (s : Solution) (R : Aux.Root s) (v : HeightOneSpectrum (𝓞 L24))
    (hv : v.asIdeal = Ideal.span {Bint 2}) :
    FractionalIdeal.count L24 v (FractionalIdeal.spanSingleton (𝓞 L24)⁰ (Edesc (algebraMap L8 L24 R.θ))) ≡ 2
      [ZMOD 5] := by
  rw [(count_Edesc_values s R v).1 hv, Int.modEq_iff_dvd]
  exact ⟨-4 * (padicValInt 5 s.X : ℤ) - 2, by ring⟩

/-- **Proposition 4.2** at `P₅ = (B₅)` (label `(2,1,1)`): the exponent of `P₅` in `(E)` is `≡ 3 (mod 5)`. -/
theorem count_Edesc_P5 (s : Solution) (R : Aux.Root s) (v : HeightOneSpectrum (𝓞 L24))
    (hv : v.asIdeal = Ideal.span {Bint 4}) :
    FractionalIdeal.count L24 v (FractionalIdeal.spanSingleton (𝓞 L24)⁰ (Edesc (algebraMap L8 L24 R.θ))) ≡ 3
      [ZMOD 5] := by
  rw [(count_Edesc_values s R v).2.1 hv, Int.modEq_iff_dvd]
  exact ⟨-6 * (padicValInt 5 s.X : ℤ) - 3, by ring⟩

/-- **Proposition 4.2** at `P₂, P₄, P₆, P₇, P₈` (`Bint` indices `1, 3, 5, 6, 7`): the exponent in `(E)` is
`≡ 0 (mod 5)`. -/
theorem count_Edesc_zero (s : Solution) (R : Aux.Root s) (v : HeightOneSpectrum (𝓞 L24)) (i : Fin 24)
    (hi : i = 1 ∨ i = 3 ∨ i = 5 ∨ i = 6 ∨ i = 7) (hv : v.asIdeal = Ideal.span {Bint i}) :
    FractionalIdeal.count L24 v (FractionalIdeal.spanSingleton (𝓞 L24)⁰ (Edesc (algebraMap L8 L24 R.θ))) ≡ 0
      [ZMOD 5] := by
  obtain ⟨-, -, h6, h7, hC⟩ := count_Edesc_values s R v
  rw [Int.ModEq, Int.zero_emod]
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · rcases hC (Or.inl hv) with h' | h' | h' <;> rw [h'] <;> omega
  · rcases hC (Or.inr (Or.inl hv)) with h' | h' | h' <;> rw [h'] <;> omega
  · rw [h6 hv]; rfl
  · rw [h7 hv]; rfl
  · rcases hC (Or.inr (Or.inr hv)) with h' | h' | h' <;> rw [h'] <;> omega

/-- The residues of Proposition 4.2 (condition (V) of Section 7), indexed by `Bint` index: `2` at `P₃ = (B₃)`,
`3` at `P₅ = (B₅)`, `0` at the other primes above 5. -/
def valE : Fin 24 → ℤ := ![0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- **Proposition 4.2** (condition (V)): for each prime `P = (B_i)` above 5 (`1 ≤ i ≤ 7`), the exponent of `P` in
`(E)` is `≡ valE i (mod 5)`. -/
theorem count_Edesc_mod_five (s : Solution) (R : Aux.Root s) (v : HeightOneSpectrum (𝓞 L24)) (i : Fin 24)
    (hi1 : 1 ≤ i.val) (hi7 : i.val ≤ 7) (hv : v.asIdeal = Ideal.span {Bint i}) :
    FractionalIdeal.count L24 v (FractionalIdeal.spanSingleton (𝓞 L24)⁰ (Edesc (algebraMap L8 L24 R.θ))) ≡ valE i
      [ZMOD 5] := by
  have : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    fin_cases i <;> simp_all
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact count_Edesc_zero s R v 1 (Or.inl rfl) hv
  · exact count_Edesc_P3 s R v hv
  · exact count_Edesc_zero s R v 3 (Or.inr (Or.inl rfl)) hv
  · exact count_Edesc_P5 s R v hv
  · exact count_Edesc_zero s R v 5 (Or.inr (Or.inr (Or.inl rfl))) hv
  · exact count_Edesc_zero s R v 6 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hv
  · exact count_Edesc_zero s R v 7 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hv

end

end X2Y5Z7.FiveAdic
