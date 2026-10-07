module

public import X2Y5Z7.Assembly.TFamily
public import X2Y5Z7.Main.AuxAt
public import X2Y5Z7.ResidueSymbols.EResidue
public import X2Y5Z7.SymbolSets.Check

@[expose] public section

/-! # Glue for the per-prime assembly

For an auxiliary prime `q` with `q ∤ 70XYZ` (Corollary 5.5 (`q ∤ XYZ`)):
* `η̄ = X̄⁵/Z̄⁷ ∈ F_q` is neither `0` nor `1` (`etaBar_ne_zero`, `etaBar_ne_one`, using `Y² = Z⁷ − X⁵`), and the
  residue `t` of the Putz root at a prime of `L₈` above `q` is a root of `f̄_η̄` (`fb_tRes`);
* at a prime `𝔔` of `L₂₄` above the prime `r` of `L₈`, with `ι : k_r → K_𝔔` compatible with the residue maps,
  `E` is a `𝔔`-unit whose symbol is the symbol of `80000 (ι t − β) ψ(ι t)³`, provided this is nonzero
  (`unit_sym`);
* `auxAt_of` packages the symbols at all primes above `q` into `AuxAt`. -/

namespace X2Y5Z7.Assembly

open NumberField X2Y5Z7.FiniteFields X2Y5Z7.ResidueSymbols X2Y5Z7.Aux

noncomputable section

section Casts

variable {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [Algebra (ZMod q) k]

theorem intCast_ne_zero {a : ℤ} (h : ¬ (q : ℤ) ∣ a) : (a : k) ≠ 0 := by
  rw [← map_intCast (algebraMap (ZMod q) k), Ne, map_eq_zero_iff _ (algebraMap (ZMod q) k).injective,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact h

theorem h70_of {s : Solution} (h70 : (70 : ZMod q) ≠ 0) (hX : ¬ (q : ℤ) ∣ s.X) (hY : ¬ (q : ℤ) ∣ s.Y)
    (hZ : ¬ (q : ℤ) ∣ s.Z) : (70 : k) * s.X * s.Y * s.Z ≠ 0 := by
  have h : (70 : k) ≠ 0 := by
    rw [← map_ofNat (algebraMap (ZMod q) k), Ne, map_eq_zero_iff _ (algebraMap (ZMod q) k).injective]
    exact h70
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h (intCast_ne_zero hX)) (intCast_ne_zero hY)) (intCast_ne_zero hZ)

end Casts

/-- `η̄ = X̄⁵ / Z̄⁷ ∈ F_q`. -/
def etaBar (q : ℕ) [Fact q.Prime] (s : Solution) : ZMod q := (s.X : ZMod q) ^ 5 / (s.Z : ZMod q) ^ 7

variable {q : ℕ} [Fact q.Prime] {s : Solution}

theorem etaBar_ne_zero (hX : ¬ (q : ℤ) ∣ s.X) (hZ : ¬ (q : ℤ) ∣ s.Z) : etaBar q s ≠ 0 := by
  have hX' : (s.X : ZMod q) ≠ 0 := by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hX
  have hZ' : (s.Z : ZMod q) ≠ 0 := by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hZ
  exact div_ne_zero (pow_ne_zero _ hX') (pow_ne_zero _ hZ')

theorem etaBar_ne_one (hY : ¬ (q : ℤ) ∣ s.Y) (hZ : ¬ (q : ℤ) ∣ s.Z) : etaBar q s ≠ 1 := by
  have hY' : (s.Y : ZMod q) ≠ 0 := by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hY
  have hZ' : (s.Z : ZMod q) ^ 7 ≠ 0 := pow_ne_zero _ (by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hZ)
  intro h1
  rw [etaBar, div_eq_one_iff_eq hZ'] at h1
  have he : (s.X : ZMod q) ^ 5 + (s.Y : ZMod q) ^ 2 = (s.Z : ZMod q) ^ 7 := by exact_mod_cast congrArg (Int.cast : ℤ → ZMod q) s.eq
  rw [h1, add_eq_left] at he
  exact hY' (pow_eq_zero_iff (by norm_num) |>.mp he)

variable (R : Root s) {k : Type*} [Field k] [Finite k] [Algebra (ZMod q) k] (r : 𝓞 L8 →+* k)

omit [Finite k] in
theorem fb_tRes (h : (10 : k) * s.Z ≠ 0) : SymbolSets.fb (etaBar q s) (tRes R r) = 0 := by
  have hZ : (s.Z : k) ≠ 0 := right_ne_zero_of_mul h
  have he : algebraMap (ZMod q) k (etaBar q s) = (s.X : k) ^ 5 / (s.Z : k) ^ 7 := by
    rw [etaBar, map_div₀, map_pow, map_pow, map_intCast, map_intCast]
  rw [SymbolSets.fb, he]
  exact t_root R r h

omit [Finite k] in
theorem h10_map {K : Type*} [Field K] (ι : k →+* K) (h : (10 : k) * s.Z ≠ 0) : (10 : K) * s.Z ≠ 0 := by
  have := (map_ne_zero ι).mpr h
  rwa [map_mul, map_ofNat, map_intCast] at this

/-- The residue of `w/(10Z)` at `𝔔` is `ι t`. -/
theorem tres_eq (D8 : L8Prime) (D : L24Prime) (ι : D8.K →+* D.K)
    (hι : ∀ y, ι (D8.res y) = D.res (algebraMap (𝓞 L8) (𝓞 L24) y)) :
    tres R D = ι (tRes R D8.res) := by
  rw [tres, tRes, map_div₀, hι, L24Prime.res_algebraMap, map_mul, map_ofNat, map_intCast]

/-- `E` is a `𝔔`-unit whose symbol is that of `80000 (ι t − β) ψ(ι t)³`. -/
theorem unit_sym (D8 : L8Prime) (D : L24Prime) (ι : D8.K →+* D.K)
    (hι : ∀ y, ι (D8.res y) = D.res (algebraMap (𝓞 L8) (𝓞 L24) y)) (h10 : (10 : D8.K) * s.Z ≠ 0)
    (hne : 80000 * (ι (tRes R D8.res) - D.β) *
      (25 * ι (tRes R D8.res) ^ 3 + 20 * ι (tRes R D8.res) ^ 2 + 14 * ι (tRes R D8.res) + 14) ^ 3 ≠ 0) :
    ∃ h : Eu R ∈ vU D, Multiplicative.toAdd (symU D ⟨Eu R, h⟩) =
      D.sym (80000 * (ι (tRes R D8.res) - D.β) *
        (25 * ι (tRes R D8.res) ^ 3 + 20 * ι (tRes R D8.res) ^ 2 + 14 * ι (tRes R D8.res) + 14) ^ 3) := by
  have h10' := h10_map ι h10
  rw [← tres_eq R D8 D ι hι] at hne ⊢
  exact ⟨E_mem_vU R D h10' hne, symU_E R D h10' _⟩

theorem auxAt_of {m : ℕ} (P : Fin m → L24Prime) (I : Finset (Fin m → ZMod 5)) (E : L24ˣ) (v : Fin m → ZMod 5)
    (hv : v ∈ I) (h : ∀ j, ∃ hj : E ∈ vU (P j), Multiplicative.toAdd (symU (P j) ⟨E, hj⟩) = v j) :
    Main.AuxAt P I E := by
  choose hE hs using h
  exact ⟨hE, by convert hv using 1; funext j; exact hs j⟩

end

end X2Y5Z7.Assembly
