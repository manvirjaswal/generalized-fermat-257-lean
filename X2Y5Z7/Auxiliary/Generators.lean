module

public import X2Y5Z7.Descent.Basic
public import X2Y5Z7.Residue.L8

@[expose] public section

/-! # Integral generators of `L8` attached to a solution

Let `s` be a solution and `θ ∈ L8` a root of `f_η` generating `L8` (Putz's theorem gives one). This file builds
algebraic integers from `θ`, their monic integer equations, and what these equations become under a ring
homomorphism `r : 𝓞 L8 →+* k` to a field, in the cases `q ∤ XY`, `q ∣ X`, `q ∣ Z`.

* `w = 10 Z θ` is a root of
  `Gw = w⁸ + 8Zw⁷ + 56Z²w⁶ + 560Z³w⁵ - 400000X⁵w + 1000000X⁵Z`.
* `u = X/θ` is a root of `Gu = u⁸ - 4Xu⁷ + 56Z⁷u³ + 56XZ⁷u² + 80X²Z⁷u + 100X³Z⁷`.

Key identities (each is proved by `linear_combination` below):
* `A·Gw + B·Gw' = 140000000000·X⁵(X⁵ - Z⁷) = -140000000000·X⁵Y²`;
* modulo `X`: `Gw = w⁵ C(w)` with `C = w³ + 8Zw² + 56Z²w + 560Z³`,
  `(653Z - 39w) C + (13w² - 183Zw - 280Z²) C' = 350000 Z⁴`, and `Z⁵ C(w) = u⁵ (4w - 10Z)`. -/

namespace X2Y5Z7.Aux

open Polynomial NumberField

noncomputable section

/-! ## Generic helpers -/

section Helpers

variable {k : Type*} [Field k]

theorem ringHom_aeval (r : 𝓞 L8 →+* k) (x : 𝓞 L8) (p : ℤ[X]) : r (aeval x p) = aeval (r x) p := by
  rw [aeval_def, aeval_def, hom_eval₂]
  congr 1
  exact RingHom.ext_int _ _

theorem coe_aeval (x : 𝓞 L8) (p : ℤ[X]) : ((aeval x p : 𝓞 L8) : L8) = aeval (x : L8) p :=
  (aeval_algebraMap_apply L8 x p).symm

/-- An element of `L8` that is a root of a monic integer polynomial, as an element of `𝓞 L8`. -/
def mkInt (x : L8) (p : ℤ[X]) (hp : p.Monic) (hx : aeval x p = 0) : 𝓞 L8 :=
  ⟨x, ⟨p, hp, by rwa [aeval_def] at hx⟩⟩

@[simp] theorem coe_mkInt (x : L8) (p : ℤ[X]) (hp : p.Monic) (hx : aeval x p = 0) :
    ((mkInt x p hp hx : 𝓞 L8) : L8) = x := rfl

theorem aeval_mkInt (x : L8) (p : ℤ[X]) (hp : p.Monic) (hx : aeval x p = 0) :
    aeval (mkInt x p hp hx) p = 0 := by
  apply RingOfIntegers.ext
  rw [coe_aeval, coe_mkInt, hx]
  rfl

theorem adjoin_eq_top_of_mem {x θ : L8} (hgen : Algebra.adjoin ℚ {θ} = ⊤)
    (hmem : θ ∈ Algebra.adjoin ℚ {x}) : Algebra.adjoin ℚ {x} = ⊤ := by
  rw [eq_top_iff, ← hgen]
  exact Algebra.adjoin_le (Set.singleton_subset_iff.2 hmem)

/-- A generator of `L8` in `𝓞 L8` that is a root of a monic integer polynomial of degree 8 has that polynomial as
its minimal polynomial over `ℤ`. -/
theorem minpoly_eq_of_gen (x : 𝓞 L8) (p : ℤ[X]) (hp : p.Monic) (hdeg : p.natDegree = 8)
    (hx : aeval x p = 0) (hgen : Algebra.adjoin ℚ {(x : L8)} = ⊤) : minpoly ℤ x = p := by
  have hint : IsIntegral ℤ (x : L8) := RingOfIntegers.isIntegral_coe x
  have hintQ : IsIntegral ℚ (x : L8) := Algebra.IsIntegral.isIntegral _
  have htop : IntermediateField.adjoin ℚ {(x : L8)} = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hintQ.isAlgebraic, hgen, IntermediateField.top_toSubalgebra]
  have h8 : (minpoly ℚ (x : L8)).natDegree = 8 := by
    rw [← IntermediateField.adjoin.finrank hintQ, htop, IntermediateField.finrank_top', L8_finrank]
  have hdegZ : (minpoly ℤ (x : L8)).natDegree = 8 := by
    rw [← h8, minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint, (minpoly.monic hint).natDegree_map]
  have hx' : aeval (x : L8) p = 0 := by rw [← coe_aeval, hx]; rfl
  have hdvd : minpoly ℤ (x : L8) ∣ p := minpoly.isIntegrallyClosed_dvd hint hx'
  rw [← RingOfIntegers.minpoly_coe]
  exact (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hp hdvd (by rw [hdeg, hdegZ])).symm

theorem ne_zero_of_70 {k : Type*} [Field k] (h : (70 : k) ≠ 0) :
    (2 : k) ≠ 0 ∧ (5 : k) ≠ 0 ∧ (7 : k) ≠ 0 := by
  have e : (70 : k) = 2 * 5 * 7 := by norm_num
  rw [e] at h
  exact ⟨left_ne_zero_of_mul (left_ne_zero_of_mul h), right_ne_zero_of_mul (left_ne_zero_of_mul h),
    right_ne_zero_of_mul h⟩

theorem ne_zero_257 {k : Type*} [Field k] (h : (70 : k) ≠ 0) (a b c : ℕ) :
    (2 : k) ^ a * 5 ^ b * 7 ^ c ≠ 0 := by
  obtain ⟨h2, h5, h7⟩ := ne_zero_of_70 h
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h5)) (pow_ne_zero _ h7)

end Helpers

/-! ## A generating root of `f_η` -/

/-- A root `θ ∈ L8` of `f_η` generating `L8`. -/
structure Root (s : Solution) where
  θ : L8
  root : aeval θ (fpoly s.η) = 0
  gen : Algebra.adjoin ℚ {θ} = ⊤

variable {s : Solution}

/-- Putz's hypothesis `ℚ[t]/(f_η) ≅ L8` gives a generating root. -/
theorem exists_root_of_equiv (e : AdjoinRoot (fpoly s.η) ≃ₐ[ℚ] L8) :
    ∃ θ : L8, aeval θ (fpoly s.η) = 0 ∧ Algebra.adjoin ℚ {θ} = ⊤ := by
  refine ⟨e (AdjoinRoot.root _), ?_, ?_⟩
  · have := aeval_algHom_apply (e : AdjoinRoot (fpoly s.η) →ₐ[ℚ] L8) (AdjoinRoot.root _) (fpoly s.η)
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero] at this
    exact this
  · have := Algebra.adjoin_image ℚ (e : AdjoinRoot (fpoly s.η) →ₐ[ℚ] L8) {AdjoinRoot.root _}
    rw [Set.image_singleton, AdjoinRoot.adjoinRoot_eq_top, Algebra.map_top] at this
    rw [show e (AdjoinRoot.root (fpoly s.η)) = (e : AdjoinRoot (fpoly s.η) →ₐ[ℚ] L8) (AdjoinRoot.root _) from rfl,
      this]
    exact (AlgHom.range_eq_top _).mpr e.surjective

theorem nonempty_root_of_nonempty_equiv (he : Nonempty (AdjoinRoot (fpoly s.η) ≃ₐ[ℚ] L8)) :
    Nonempty (Root s) := by
  obtain ⟨e⟩ := he
  obtain ⟨θ, h1, h2⟩ := exists_root_of_equiv e
  exact ⟨⟨θ, h1, h2⟩⟩

namespace Root

variable (R : Root s)

theorem Z_ne' : (s.Z : L8) ≠ 0 := Int.cast_ne_zero.mpr s.Z_ne

theorem X_ne' : (s.X : L8) ≠ 0 := Int.cast_ne_zero.mpr s.X_ne

theorem Y_ne' : (s.Y : L8) ≠ 0 := Int.cast_ne_zero.mpr s.Y_ne

/-- The equation of `θ` with denominators cleared: `Z⁷·4θ⁵ψ(θ) = X⁵(4θ - 1)`. -/
theorem key : (s.Z : L8) ^ 7 * (100 * R.θ ^ 8 + 80 * R.θ ^ 7 + 56 * R.θ ^ 6 + 56 * R.θ ^ 5) =
    (s.X : L8) ^ 5 * (4 * R.θ - 1) := by
  have hθ := R.root
  have hη : algebraMap ℚ L8 s.η = (s.X : L8) ^ 5 * ((s.Z : L8) ^ 7)⁻¹ := by
    simp [Solution.η, div_eq_mul_inv]
  rw [aeval_fpoly, hη] at hθ
  have hinv : (s.Z : L8) ^ 7 * ((s.Z : L8) ^ 7)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ Z_ne')
  linear_combination (s.Z : L8) ^ 7 * hθ + (s.X : L8) ^ 5 * (4 * R.θ - 1) * hinv

theorem θ_ne_zero : R.θ ≠ 0 := by
  intro h0
  have h := R.key
  rw [h0] at h
  have h5 : (s.X : L8) ^ 5 = 0 := by linear_combination h
  exact X_ne' (pow_eq_zero_iff (by norm_num) |>.mp h5)

theorem four_θ_sub_one_ne_zero : 4 * R.θ - 1 ≠ 0 := by
  intro h0
  have h := R.key
  have hθ : R.θ = 1 / 4 := by linear_combination h0 / 4
  rw [hθ] at h
  have h1 : (s.Z : L8) ^ 7 * (4900 / 65536) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact Z_ne' (pow_eq_zero_iff (by norm_num) |>.mp h2)
  · norm_num at h2

end Root

/-! ## `w = 10 Z θ` -/

variable (s) in
/-- `Gw = w⁸ + 8Zw⁷ + 56Z²w⁶ + 560Z³w⁵ - 400000X⁵w + 1000000X⁵Z`. -/
def Gw : ℤ[X] := X ^ 8 + C (8 * s.Z) * X ^ 7 + C (56 * s.Z ^ 2) * X ^ 6 + C (560 * s.Z ^ 3) * X ^ 5 -
  C (400000 * s.X ^ 5) * X + C (1000000 * s.X ^ 5 * s.Z)

variable (s) in
theorem Gw_natDegree : (Gw s).natDegree = 8 := by unfold Gw; compute_degree!

variable (s) in
theorem Gw_monic : (Gw s).Monic := by unfold Gw; monicity!

theorem aeval_Gw {A : Type*} [CommRing A] [Algebra ℤ A] (y : A) :
    aeval y (Gw s) = y ^ 8 + 8 * s.Z * y ^ 7 + 56 * s.Z ^ 2 * y ^ 6 + 560 * s.Z ^ 3 * y ^ 5 -
      400000 * s.X ^ 5 * y + 1000000 * s.X ^ 5 * s.Z := by
  simp only [Gw, map_add, map_sub, map_mul, map_pow, aeval_X, eq_intCast, map_intCast, map_ofNat]

theorem aeval_Gw_derivative {A : Type*} [CommRing A] [Algebra ℤ A] (y : A) :
    aeval y (derivative (Gw s)) = 8 * y ^ 7 + 56 * s.Z * y ^ 6 + 336 * s.Z ^ 2 * y ^ 5 +
      2800 * s.Z ^ 3 * y ^ 4 - 400000 * s.X ^ 5 := by
  simp only [Gw, derivative_add, derivative_sub, derivative_mul, derivative_C, derivative_X_pow, derivative_X,
    zero_mul, zero_add, mul_one, add_zero]
  simp only [map_add, map_sub, map_mul, map_pow, aeval_X, eq_intCast, map_intCast, map_ofNat, map_natCast]
  push_cast
  ring

theorem mem_adjoin_of_eq {x y : L8} (p : ℚ[X]) (h : y = aeval x p) : y ∈ Algebra.adjoin ℚ {x} :=
  h ▸ aeval_mem_adjoin_singleton ℚ x

theorem eq_cast {k : Type*} [CommRing k] : (s.X : k) ^ 5 + (s.Y : k) ^ 2 = (s.Z : k) ^ 7 := by
  exact_mod_cast congrArg (Int.cast : ℤ → k) s.eq

namespace Root

variable (R : Root s)

/-- `w = 10 Z θ`. -/
def w : L8 := 10 * s.Z * R.θ

theorem aeval_w : aeval R.w (Gw s) = 0 := by
  rw [w, aeval_Gw]
  linear_combination (1000000 * (s.Z : L8)) * R.key

/-- `w = 10 Z θ` as an algebraic integer. -/
def wI : 𝓞 L8 := mkInt R.w (Gw s) (Gw_monic s) R.aeval_w

@[simp] theorem coe_wI : (R.wI : L8) = 10 * s.Z * R.θ := rfl

theorem aeval_wI : aeval R.wI (Gw s) = 0 := aeval_mkInt _ _ _ _

theorem adjoin_wI : Algebra.adjoin ℚ {(R.wI : L8)} = ⊤ := by
  refine adjoin_eq_top_of_mem R.gen (mem_adjoin_of_eq (C ((10 * s.Z : ℚ))⁻¹ * X) ?_)
  have hZ := Z_ne' (s := s)
  simp only [coe_wI, map_mul, aeval_C, aeval_X, map_inv₀, map_mul, map_ofNat, map_intCast]
  field_simp

variable {k : Type*} [Field k] (r : 𝓞 L8 →+* k)

theorem minpoly_wI : minpoly ℤ R.wI = Gw s :=
  minpoly_eq_of_gen _ _ (Gw_monic s) (Gw_natDegree s) R.aeval_wI R.adjoin_wI

theorem aeval_res_wI : aeval (r R.wI) (Gw s) = 0 := by
  rw [← ringHom_aeval, R.aeval_wI, map_zero]

/-! ### `q ∤ XY` -/

/-- If `r(70XY) ≠ 0` then `Gw'(w)` survives: `A·Gw + B·Gw' = 140000000000·X⁵(X⁵ - Z⁷)`. -/
theorem wI_derivative_ne_zero (h : (70 : k) * s.X * s.Y ≠ 0) :
    r (aeval R.wI (derivative (Gw s))) ≠ 0 := by
  have h70 : (70 : k) ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul h)
  have hX : (s.X : k) ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul h)
  have hY : (s.Y : k) ≠ 0 := right_ne_zero_of_mul h
  have hG := R.aeval_res_wI r
  rw [aeval_Gw] at hG
  rw [ringHom_aeval, aeval_Gw_derivative]
  intro hD
  have heq := eq_cast (s := s) (k := k)
  set y := r R.wI
  have h0 : ((2 : k) ^ 11 * 5 ^ 10 * 7 ^ 1) * ((s.X : k) ^ 5 * (s.Y : k) ^ 2) = 0 := by
    linear_combination
      (8 * y ^ 6 + 80 * s.Z * y ^ 5 + 584 * s.Z ^ 2 * y ^ 4 + 4768 * s.Z ^ 3 * y ^ 3 +
        14560 * s.Z ^ 4 * y ^ 2 + 44800 * s.Z ^ 5 * y + 140000 * s.Z ^ 6) * hG -
      (-350000 * s.X ^ 5 + y ^ 7 + 11 * s.Z * y ^ 6 + 90 * s.Z ^ 2 * y ^ 5 + 858 * s.Z ^ 3 * y ^ 4 +
        2640 * s.Z ^ 4 * y ^ 3 + 8400 * s.Z ^ 5 * y ^ 2 + 28000 * s.Z ^ 6 * y) * hD +
      140000000000 * (s.X : k) ^ 5 * heq
  exact mul_ne_zero (ne_zero_257 h70 11 10 1) (mul_ne_zero (pow_ne_zero _ hX) (pow_ne_zero _ hY)) h0

/-- The form of the statement with `r(70XYZ) ≠ 0`. -/
theorem wI_derivative_ne_zero' (h : (70 : k) * s.X * s.Y * s.Z ≠ 0) :
    r (aeval R.wI (derivative (Gw s))) ≠ 0 :=
  R.wI_derivative_ne_zero r (left_ne_zero_of_mul h)

/-- The residue `t = r(w)/(10Z)` is a root of the reduced fibre polynomial `f_η̄`, `η̄ = X⁵/Z⁷`. -/
theorem res_t_root (h : (10 : k) * s.Z ≠ 0) :
    100 * (r R.wI / (10 * s.Z)) ^ 8 + 80 * (r R.wI / (10 * s.Z)) ^ 7 + 56 * (r R.wI / (10 * s.Z)) ^ 6 +
      56 * (r R.wI / (10 * s.Z)) ^ 5 - 4 * ((s.X : k) ^ 5 / (s.Z : k) ^ 7) * (r R.wI / (10 * s.Z)) +
      (s.X : k) ^ 5 / (s.Z : k) ^ 7 = 0 := by
  have h10 : (10 : k) ≠ 0 := left_ne_zero_of_mul h
  have hZ : (s.Z : k) ≠ 0 := right_ne_zero_of_mul h
  have hG := R.aeval_res_wI r
  rw [aeval_Gw] at hG
  set y := r R.wI
  have e : (100 * (y / (10 * s.Z)) ^ 8 + 80 * (y / (10 * s.Z)) ^ 7 + 56 * (y / (10 * s.Z)) ^ 6 +
      56 * (y / (10 * s.Z)) ^ 5 - 4 * ((s.X : k) ^ 5 / (s.Z : k) ^ 7) * (y / (10 * s.Z)) +
      (s.X : k) ^ 5 / (s.Z : k) ^ 7) * ((10 : k) ^ 6 * (s.Z : k) ^ 8) =
      y ^ 8 + 8 * s.Z * y ^ 7 + 56 * s.Z ^ 2 * y ^ 6 + 560 * s.Z ^ 3 * y ^ 5 -
        400000 * s.X ^ 5 * y + 1000000 * s.X ^ 5 * s.Z := by
    field_simp
    ring
  rw [hG] at e
  exact (mul_eq_zero.mp e).resolve_right (mul_ne_zero (pow_ne_zero _ h10) (pow_ne_zero _ hZ))

/-! ### `q ∣ Z` (A1b) -/

theorem qZ (hZ : (s.Z : k) = 0) (h : (70 : k) * s.X ≠ 0) :
    r (aeval R.wI (derivative (Gw s))) ≠ 0 ∧ (r R.wI = 0 ∨ (r R.wI) ^ 7 = 400000 * (s.X : k) ^ 5) := by
  have h70 : (70 : k) ≠ 0 := left_ne_zero_of_mul h
  have hX : (s.X : k) ≠ 0 := right_ne_zero_of_mul h
  have hG := R.aeval_res_wI r
  rw [aeval_Gw] at hG
  rw [ringHom_aeval, aeval_Gw_derivative]
  set y := r R.wI
  have h1 : y * (y ^ 7 - 400000 * (s.X : k) ^ 5) = 0 := by
    linear_combination hG - (8 * y ^ 7 + 56 * s.Z * y ^ 6 + 560 * s.Z ^ 2 * y ^ 5 + 1000000 * s.X ^ 5) * hZ
  have hcases : y = 0 ∨ y ^ 7 = 400000 * (s.X : k) ^ 5 := by
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (by linear_combination h2)
  refine ⟨?_, hcases⟩
  intro hD
  rcases hcases with h2 | h2
  · have h0 : ((2 : k) ^ 7 * 5 ^ 5 * 7 ^ 0) * (s.X : k) ^ 5 = 0 := by
      linear_combination -hD + (8 * y ^ 6) * h2 + (56 * y ^ 6 + 336 * s.Z * y ^ 5 + 2800 * s.Z ^ 2 * y ^ 4) * hZ
    exact mul_ne_zero (ne_zero_257 h70 7 5 0) (pow_ne_zero _ hX) h0
  · have h0 : ((2 : k) ^ 7 * 5 ^ 5 * 7 ^ 1) * (s.X : k) ^ 5 = 0 := by
      linear_combination hD - 8 * h2 - (56 * y ^ 6 + 336 * s.Z * y ^ 5 + 2800 * s.Z ^ 2 * y ^ 4) * hZ
    exact mul_ne_zero (ne_zero_257 h70 7 5 1) (pow_ne_zero _ hX) h0

end Root

/-! ## `q ∣ X`: the cubic factor `C` and `u = X/θ` -/

variable (s) in
/-- `C = w³ + 8Zw² + 56Z²w + 560Z³`; modulo `X`, `Gw = w⁵ C`. -/
def Cpoly : ℤ[X] := X ^ 3 + C (8 * s.Z) * X ^ 2 + C (56 * s.Z ^ 2) * X + C (560 * s.Z ^ 3)

theorem aeval_Cpoly {A : Type*} [CommRing A] [Algebra ℤ A] (y : A) :
    aeval y (Cpoly s) = y ^ 3 + 8 * s.Z * y ^ 2 + 56 * s.Z ^ 2 * y + 560 * s.Z ^ 3 := by
  simp only [Cpoly, map_add, map_mul, map_pow, aeval_X, eq_intCast, map_intCast]
  push_cast
  ring

variable (s) in
/-- `Gu = u⁸ - 4Xu⁷ + 56Z⁷u³ + 56XZ⁷u² + 80X²Z⁷u + 100X³Z⁷`, the equation of `u = X/θ`. -/
def Gu : ℤ[X] := X ^ 8 - C (4 * s.X) * X ^ 7 + C (56 * s.Z ^ 7) * X ^ 3 + C (56 * s.X * s.Z ^ 7) * X ^ 2 +
  C (80 * s.X ^ 2 * s.Z ^ 7) * X + C (100 * s.X ^ 3 * s.Z ^ 7)

variable (s) in
theorem Gu_natDegree : (Gu s).natDegree = 8 := by unfold Gu; compute_degree!

variable (s) in
theorem Gu_monic : (Gu s).Monic := by unfold Gu; monicity!

theorem aeval_Gu {A : Type*} [CommRing A] [Algebra ℤ A] (y : A) :
    aeval y (Gu s) = y ^ 8 - 4 * s.X * y ^ 7 + 56 * s.Z ^ 7 * y ^ 3 + 56 * s.X * s.Z ^ 7 * y ^ 2 +
      80 * s.X ^ 2 * s.Z ^ 7 * y + 100 * s.X ^ 3 * s.Z ^ 7 := by
  simp only [Gu, map_add, map_sub, map_mul, map_pow, aeval_X, eq_intCast, map_intCast]
  push_cast
  ring

theorem aeval_Gu_derivative {A : Type*} [CommRing A] [Algebra ℤ A] (y : A) :
    aeval y (derivative (Gu s)) = 8 * y ^ 7 - 28 * s.X * y ^ 6 + 168 * s.Z ^ 7 * y ^ 2 +
      112 * s.X * s.Z ^ 7 * y + 80 * s.X ^ 2 * s.Z ^ 7 := by
  simp only [Gu, derivative_add, derivative_sub, derivative_mul, derivative_C, derivative_X_pow, derivative_X,
    zero_mul, zero_add, mul_one, add_zero]
  simp only [map_add, map_sub, map_mul, map_pow, aeval_X, eq_intCast, map_intCast, map_natCast]
  push_cast
  ring

namespace Root

variable (R : Root s)

/-- `u = X/θ`. -/
def u : L8 := s.X / R.θ

theorem aeval_u : aeval R.u (Gu s) = 0 := by
  have hθ := R.θ_ne_zero
  rw [u, aeval_Gu]
  field_simp
  linear_combination (s.X : L8) ^ 3 * R.key

/-- `u = X/θ` as an algebraic integer. -/
def uI : 𝓞 L8 := mkInt R.u (Gu s) (Gu_monic s) R.aeval_u

@[simp] theorem coe_uI : (R.uI : L8) = s.X / R.θ := rfl

theorem aeval_uI : aeval R.uI (Gu s) = 0 := aeval_mkInt _ _ _ _

theorem adjoin_uI : Algebra.adjoin ℚ {(R.uI : L8)} = ⊤ := by
  refine adjoin_eq_top_of_mem R.gen (mem_adjoin_of_eq
    (C (-(100 * (s.X : ℚ) ^ 2 * (s.Z : ℚ) ^ 7)⁻¹) * (X ^ 7 - C (4 * (s.X : ℚ)) * X ^ 6 +
      C (56 * (s.Z : ℚ) ^ 7) * X ^ 2 + C (56 * (s.X : ℚ) * (s.Z : ℚ) ^ 7) * X +
      C (80 * (s.X : ℚ) ^ 2 * (s.Z : ℚ) ^ 7))) ?_)
  have hZ := Z_ne' (s := s)
  have hX := X_ne' (s := s)
  have hθ := R.θ_ne_zero
  simp only [coe_uI, map_mul, map_add, map_sub, map_pow, map_neg, aeval_C, aeval_X, map_inv₀, map_ofNat,
    map_intCast]
  field_simp
  linear_combination R.key

theorem minpoly_uI : minpoly ℤ R.uI = Gu s :=
  minpoly_eq_of_gen _ _ (Gu_monic s) (Gu_natDegree s) R.aeval_uI R.adjoin_uI

/-- `Z⁵ C(w) = u⁵ (4w - 10Z)` in `𝓞 L8`. -/
theorem Cpoly_wI : (s.Z : 𝓞 L8) ^ 5 * aeval R.wI (Cpoly s) = R.uI ^ 5 * (4 * R.wI - 10 * s.Z) := by
  apply RingOfIntegers.ext
  have hθ := R.θ_ne_zero
  rw [aeval_Cpoly]
  simp only [map_mul, map_pow, map_add, map_sub, map_intCast, map_ofNat]
  simp only [← RingOfIntegers.coe_eq_algebraMap, coe_wI, coe_uI]
  field_simp
  linear_combination (10 * (s.Z : L8)) * R.key

variable {k : Type*} [Field k] (r : 𝓞 L8 →+* k)

/-- `q ∣ X`, `r(w) ≠ 0`: `r(w)` is a root of `C` and `Gw'(w)` survives. -/
theorem qX_wI (hX : (s.X : k) = 0) (h : (70 : k) * s.Z ≠ 0) (hw : r R.wI ≠ 0) :
    r (aeval R.wI (derivative (Gw s))) ≠ 0 ∧ aeval (r R.wI) (Cpoly s) = 0 := by
  have h70 : (70 : k) ≠ 0 := left_ne_zero_of_mul h
  have hZ : (s.Z : k) ≠ 0 := right_ne_zero_of_mul h
  have hG := R.aeval_res_wI r
  rw [aeval_Gw] at hG
  rw [ringHom_aeval, aeval_Gw_derivative, aeval_Cpoly]
  set y := r R.wI
  have h1 : y ^ 5 * (y ^ 3 + 8 * s.Z * y ^ 2 + 56 * s.Z ^ 2 * y + 560 * s.Z ^ 3) = 0 := by
    linear_combination hG - (-400000 * (s.X : k) ^ 4 * y + 1000000 * (s.X : k) ^ 4 * s.Z) * hX
  have hC : y ^ 3 + 8 * s.Z * y ^ 2 + 56 * s.Z ^ 2 * y + 560 * s.Z ^ 3 = 0 :=
    (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hw)
  refine ⟨?_, hC⟩
  intro hD
  have h2 : y ^ 4 * (y * (3 * y ^ 2 + 16 * s.Z * y + 56 * s.Z ^ 2)) = 0 := by
    linear_combination hD - 5 * y ^ 4 * hC + 400000 * (s.X : k) ^ 4 * hX
  have hC' : 3 * y ^ 2 + 16 * s.Z * y + 56 * s.Z ^ 2 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (pow_ne_zero _ hw))).resolve_left hw
  have h0 : ((2 : k) ^ 4 * 5 ^ 5 * 7 ^ 1) * (s.Z : k) ^ 4 = 0 := by
    linear_combination (653 * (s.Z : k) - 39 * y) * hC +
      (13 * y ^ 2 - 183 * s.Z * y - 280 * s.Z ^ 2) * hC'
  exact mul_ne_zero (ne_zero_257 h70 4 5 1) (pow_ne_zero _ hZ) h0

/-- `q ∣ X`, `r(w) = 0`: then `r(u)⁵ = -56 Z⁷`, so `r(u) ≠ 0`, and `Gu'(u)` survives. -/
theorem qX_uI (hX : (s.X : k) = 0) (h : (70 : k) * s.Z ≠ 0) (hw : r R.wI = 0) :
    r R.uI ≠ 0 ∧ (r R.uI) ^ 5 = -56 * (s.Z : k) ^ 7 ∧ r (aeval R.uI (derivative (Gu s))) ≠ 0 := by
  have h70 : (70 : k) ≠ 0 := left_ne_zero_of_mul h
  have hZ : (s.Z : k) ≠ 0 := right_ne_zero_of_mul h
  obtain ⟨h2, h5, h7⟩ := ne_zero_of_70 h70
  have hid := congrArg r R.Cpoly_wI
  rw [map_mul, ringHom_aeval, aeval_Cpoly, hw] at hid
  simp only [map_mul, map_pow, map_sub, map_intCast, map_ofNat, hw] at hid
  set v := r R.uI
  have hv5 : v ^ 5 = -56 * (s.Z : k) ^ 7 := by
    have h10 : (10 : k) * s.Z ≠ 0 := mul_ne_zero (by
      have : (10 : k) = 2 * 5 := by norm_num
      rw [this]; exact mul_ne_zero h2 h5) hZ
    apply mul_left_cancel₀ h10
    linear_combination hid
  have hv : v ≠ 0 := by
    intro h0
    rw [h0] at hv5
    have : (56 : k) * (s.Z : k) ^ 7 = 0 := by linear_combination hv5
    have e56 : (56 : k) = 2 ^ 3 * 7 := by norm_num
    rw [e56] at this
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2) h7) (pow_ne_zero _ hZ) this
  refine ⟨hv, hv5, ?_⟩
  rw [ringHom_aeval, aeval_Gu_derivative]
  intro hD
  have h0 : ((2 : k) ^ 3 * 5 ^ 1 * 7 ^ 1) * (v ^ 2 * (s.Z : k) ^ 7) = 0 := by
    linear_combination -hD + 8 * v ^ 2 * hv5 +
      (-28 * v ^ 6 + 112 * s.Z ^ 7 * v + 80 * s.X * s.Z ^ 7) * hX
  exact mul_ne_zero (ne_zero_257 h70 3 1 1) (mul_ne_zero (pow_ne_zero _ hv) (pow_ne_zero _ hZ)) h0

end Root

end

end X2Y5Z7.Aux
