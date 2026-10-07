module

public import X2Y5Z7.Auxiliary.GenDegreeSum
public import X2Y5Z7.Auxiliary.Distinct
public import X2Y5Z7.Auxiliary.Generators

@[expose] public section

/-! # The residues of the Putz root at the primes of `L₈` above an auxiliary prime

For a solution with Putz root `θ` and a residue map `r : 𝓞 L₈ → k` onto a finite field of characteristic `q`
with `70XYZ ≢ 0`, the residue `t = r(w)/(10Z)` of `θ` (`w = 10Zθ ∈ 𝓞 L₈`) is a root of
`f̄(t) = 100t⁸ + 80t⁷ + 56t⁶ + 56t⁵ − 4η̄t + η̄` (`t_root`), generates `k` (so its minimal polynomial over
`F_q` has degree `[k : F_q]`, `t_natDegree`), and residue maps with different kernels give different minimal
polynomials (`t_minpoly_ne`). This is the "admissible family" of Proposition 5.3. -/

namespace X2Y5Z7.Assembly

open Polynomial NumberField X2Y5Z7.Aux

noncomputable section

variable {q : ℕ} [Fact q.Prime]

theorem aeval_comp_smul {A : Type*} [Field A] [Algebra (ZMod q) A] (c : ZMod q) (hc : c ≠ 0)
    (n : (ZMod q)[X]) (z : A) : aeval (algebraMap _ A c * z) (n.comp (C c⁻¹ * X)) = aeval z n := by
  rw [aeval_comp]
  simp only [map_mul, aeval_C, aeval_X]
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]

/-- Minimal polynomials of scalar multiples: `minpoly (c x) = minpoly (c y)` implies `minpoly x = minpoly y`. -/
theorem minpoly_eq_of_smul {k₁ k₂ : Type*} [Field k₁] [Field k₂] [Algebra (ZMod q) k₁] [Algebra (ZMod q) k₂]
    [Finite k₁] (c : ZMod q) (hc : c ≠ 0) (x : k₁) (y : k₂)
    (h : minpoly (ZMod q) (algebraMap _ k₁ c * x) = minpoly (ZMod q) (algebraMap _ k₂ c * y)) :
    minpoly (ZMod q) x = minpoly (ZMod q) y := by
  have hx : IsIntegral (ZMod q) x := IsIntegral.of_finite (ZMod q) x
  set n := minpoly (ZMod q) x
  have hdvd : minpoly (ZMod q) (algebraMap _ k₁ c * x) ∣ n.comp (C c⁻¹ * X) :=
    minpoly.dvd _ _ (by rw [aeval_comp_smul c hc n x, minpoly.aeval])
  rw [h] at hdvd
  have hy : aeval y n = 0 := by
    obtain ⟨p, hp⟩ := hdvd
    have := congrArg (aeval (algebraMap _ k₂ c * y)) hp
    rw [aeval_comp_smul c hc n y, map_mul, minpoly.aeval, zero_mul] at this
    exact this
  exact minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hx) hy (minpoly.monic hx)

variable {s : Solution} (R : Root s) {k : Type*} [Field k] [Finite k] [Algebra (ZMod q) k]
  (r : 𝓞 L8 →+* k)

/-- The residue of the Putz root. -/
def tRes : k := r R.wI / (10 * s.Z)

/-- `10Z` as an element of `F_q`. -/
def c10Z (s : Solution) : ZMod q := 10 * (s.Z : ZMod q)

omit [Finite k] in
theorem algebraMap_c10Z : algebraMap (ZMod q) k (c10Z s) = 10 * (s.Z : k) := by
  simp [c10Z, map_mul, map_intCast, map_ofNat]

omit [Finite k] in
theorem tRes_eq :
    tRes R r = algebraMap (ZMod q) k (c10Z s)⁻¹ * r R.wI := by
  rw [tRes, map_inv₀, algebraMap_c10Z, div_eq_inv_mul]

omit [Finite k] in
theorem c10Z_ne (h : (10 : k) * s.Z ≠ 0) : c10Z (q := q) s ≠ 0 := by
  intro h0
  apply h
  rw [← algebraMap_c10Z (q := q) (k := k), h0, map_zero]

omit [Finite k] in
/-- The derivative condition for `w` at `r`. -/
theorem hd_wI (h : (70 : k) * s.X * s.Y * s.Z ≠ 0) : r (derivativeInteger R.wI) ≠ 0 := by
  rw [derivativeInteger_eq R.wI R.adjoin_wI (Gw s) (Gw_monic s) R.aeval_wI (by rw [Gw_natDegree, L8_finrank])]
  exact R.wI_derivative_ne_zero' r h

omit [Finite k] in
theorem h10_of (h : (70 : k) * s.X * s.Y * s.Z ≠ 0) : (10 : k) * s.Z ≠ 0 := by
  have h70 : (70 : k) ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h))
  have hZ : (s.Z : k) ≠ 0 := right_ne_zero_of_mul h
  have h10 : (10 : k) ≠ 0 := by
    intro h0; apply h70
    have : (70 : k) = 7 * 10 := by norm_num
    rw [this, h0, mul_zero]
  exact mul_ne_zero h10 hZ

omit [Finite k] in
/-- The residue of the Putz root is a root of the reduced fibre polynomial. -/
theorem t_root (h : (10 : k) * s.Z ≠ 0) :
    100 * tRes R r ^ 8 + 80 * tRes R r ^ 7 + 56 * tRes R r ^ 6 + 56 * tRes R r ^ 5 -
      4 * ((s.X : k) ^ 5 / (s.Z : k) ^ 7) * tRes R r + (s.X : k) ^ 5 / (s.Z : k) ^ 7 = 0 :=
  R.res_t_root r h

/-- The residue of the Putz root generates the residue field. -/
theorem t_natDegree (hr : Function.Surjective r) (h : (70 : k) * s.X * s.Y * s.Z ≠ 0) :
    (minpoly (ZMod q) (tRes R r)).natDegree = Module.finrank (ZMod q) k := by
  have h10 := h10_of h
  have hgen := generates (q := q) R.wI r hr R.adjoin_wI (hd_wI R r h)
  have hgen' : Algebra.adjoin (ZMod q) ({tRes R r} : Set k) = ⊤ := by
    apply top_unique
    rw [← hgen, Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    have : r R.wI = algebraMap (ZMod q) k (c10Z s) * tRes R r := by
      rw [tRes_eq (q := q) R r, ← mul_assoc, ← map_mul, mul_inv_cancel₀ (c10Z_ne (q := q) h10), map_one, one_mul]
    rw [this]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl)
  have pb := PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite (ZMod q) (tRes R r)) hgen'
  have h1 := (PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite (ZMod q) (tRes R r)) hgen').natDegree_minpoly
  have h2 := (PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite (ZMod q) (tRes R r)) hgen').finrank
  rw [PowerBasis.ofAdjoinEqTop_gen] at h1
  rw [h1, h2]

/-- Residue maps with different kernels give different minimal polynomials of the residues. -/
theorem t_minpoly_ne {k₂ : Type*} [Field k₂] [Finite k₂] [Algebra (ZMod q) k₂] (r₂ : 𝓞 L8 →+* k₂)
    (hr : Function.Surjective r) (hr₂ : Function.Surjective r₂) (hker : RingHom.ker r ≠ RingHom.ker r₂)
    (h : (70 : k) * s.X * s.Y * s.Z ≠ 0) (h₂ : (70 : k₂) * s.X * s.Y * s.Z ≠ 0) :
    minpoly (ZMod q) (tRes R r) ≠ minpoly (ZMod q) (tRes R r₂) := by
  intro heq
  apply minpoly_ne_of_ker_ne (q := q) R.wI R.adjoin_wI r hr (hd_wI R r h) r₂ hr₂ (hd_wI R r₂ h₂) hker
  have h10 := h10_of h
  have h10₂ := h10_of h₂
  have e1 : r R.wI = algebraMap (ZMod q) k (c10Z s) * tRes R r := by
    rw [tRes_eq (q := q) R r, ← mul_assoc, ← map_mul, mul_inv_cancel₀ (c10Z_ne (q := q) h10), map_one, one_mul]
  have e2 : r₂ R.wI = algebraMap (ZMod q) k₂ (c10Z s) * tRes R r₂ := by
    rw [tRes_eq (q := q) R r₂, ← mul_assoc, ← map_mul, mul_inv_cancel₀ (c10Z_ne (q := q) h10), map_one, one_mul]
  rw [e1, e2]
  -- scaling by `c⁻¹` recovers `tRes`, so equal minpolys of `tRes` give equal minpolys of `c · tRes`
  apply minpoly_eq_of_smul (c10Z s)⁻¹ (inv_ne_zero (c10Z_ne (q := q) h10))
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (c10Z_ne (q := q) h10), map_one, one_mul, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ (c10Z_ne (q := q) h10), map_one, one_mul]
  exact heq

end

end X2Y5Z7.Assembly
