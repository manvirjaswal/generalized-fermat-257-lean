import X2Y5Z7.Residue.L24
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-! # Residues and symbols on the local ring of a prime of `L24`

A residue map `r : 𝓞 L24 →+* k` into a field with nonzero kernel defines a prime `𝔔 = ker r` (`primeOfRes`). Every
`x ∈ L24` with `v_𝔔(x) ≥ 0` can be written `x = n/d` with `n, d ∈ 𝓞 L24`, `r d ≠ 0` (Mathlib's
`exists_primeCompl_mul_eq_of_integer`), and `locRes x = r n / r d` does not depend on the choice. It is multiplicative,
extends `r`, and is nonzero exactly on the `𝔔`-units. Composing with a character `kˣ → ℤ/5` gives a homomorphism on
the group of `𝔔`-units of `L24` which kills fifth powers; an element whose fifth power is a `𝔔`-unit is itself one. -/

namespace X2Y5Z7

open IsDedekindDomain NumberField

noncomputable section

variable {k : Type*} [Field k]

/-- The prime of `𝓞 L24` which is the kernel of a residue map `r`. -/
def primeOfRes (r : 𝓞 L24 →+* k) (hr : RingHom.ker r ≠ ⊥) : HeightOneSpectrum (𝓞 L24) where
  asIdeal := RingHom.ker r
  isPrime := RingHom.ker_isPrime r
  ne_bot := hr

variable (r : 𝓞 L24 →+* k) (hr : RingHom.ker r ≠ ⊥)

/-- The valuation of the prime `ker r`. -/
abbrev vRes : Valuation L24 (WithZero (Multiplicative ℤ)) := (primeOfRes r hr).valuation L24

theorem vRes_algebraMap_eq_one_iff (z : 𝓞 L24) : vRes r hr (algebraMap (𝓞 L24) L24 z) = 1 ↔ r z ≠ 0 := by
  rw [vRes, HeightOneSpectrum.valuation_eq_one_iff_notMem]
  exact not_congr RingHom.mem_ker

theorem vRes_algebraMap_le_one (z : 𝓞 L24) : vRes r hr (algebraMap (𝓞 L24) L24 z) ≤ 1 :=
  HeightOneSpectrum.valuation_le_one _ z

theorem vRes_le_one_of_mul_eq (x : L24) (n d : 𝓞 L24) (hd : r d ≠ 0)
    (h : x * algebraMap (𝓞 L24) L24 d = algebraMap (𝓞 L24) L24 n) : vRes r hr x ≤ 1 := by
  have h1 : vRes r hr (algebraMap (𝓞 L24) L24 d) = 1 := (vRes_algebraMap_eq_one_iff r hr d).mpr hd
  have h2 := congrArg (vRes r hr) h
  rw [map_mul, h1, mul_one] at h2
  rw [h2]
  exact vRes_algebraMap_le_one r hr n

theorem exists_rep (x : L24) (hx : vRes r hr x ≤ 1) :
    ∃ p : 𝓞 L24 × 𝓞 L24, r p.2 ≠ 0 ∧ x * algebraMap (𝓞 L24) L24 p.2 = algebraMap (𝓞 L24) L24 p.1 := by
  obtain ⟨n, d, h⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (primeOfRes r hr) x hx
  refine ⟨(n, d), fun h0 => (Ideal.mem_primeCompl_iff.mp d.2) (RingHom.mem_ker.mpr h0), h⟩

open Classical in
/-- The residue of an element of the local ring at `ker r` (junk value `0` elsewhere). -/
def locRes (x : L24) : k :=
  if h : vRes r hr x ≤ 1 then r (Classical.choose (exists_rep r hr x h)).1 / r (Classical.choose (exists_rep r hr x h)).2
  else 0

theorem locRes_eq (x : L24) (n d : 𝓞 L24) (hd : r d ≠ 0)
    (h : x * algebraMap (𝓞 L24) L24 d = algebraMap (𝓞 L24) L24 n) : locRes r hr x = r n / r d := by
  have hx := vRes_le_one_of_mul_eq r hr x n d hd h
  rw [locRes, dite_eq_left hx]
  obtain ⟨hd', h'⟩ := Classical.choose_spec (exists_rep r hr x hx)
  set n' := (Classical.choose (exists_rep r hr x hx)).1
  set d' := (Classical.choose (exists_rep r hr x hx)).2
  have key : n * d' = n' * d := by
    apply IsFractionRing.injective (𝓞 L24) L24
    rw [map_mul, map_mul, ← h, ← h']
    ring
  have key' := congrArg r key
  rw [map_mul, map_mul] at key'
  rw [div_eq_div_iff hd' hd]
  linear_combination -key'

theorem locRes_algebraMap (z : 𝓞 L24) : locRes r hr (algebraMap (𝓞 L24) L24 z) = r z := by
  rw [locRes_eq r hr _ z 1 (by simp) (by simp), map_one, div_one]

theorem locRes_mul (x y : L24) (hx : vRes r hr x ≤ 1) (hy : vRes r hr y ≤ 1) :
    locRes r hr (x * y) = locRes r hr x * locRes r hr y := by
  obtain ⟨⟨n, d⟩, hd, h⟩ := exists_rep r hr x hx
  obtain ⟨⟨n', d'⟩, hd', h'⟩ := exists_rep r hr y hy
  rw [locRes_eq r hr x n d hd h, locRes_eq r hr y n' d' hd' h',
    locRes_eq r hr (x * y) (n * n') (d * d') (by rw [map_mul]; exact mul_ne_zero hd hd')
      (by rw [map_mul, map_mul, ← h, ← h']; ring), map_mul, map_mul, div_mul_div_comm]

theorem locRes_ne_zero_iff (x : L24) (hx : vRes r hr x ≤ 1) : locRes r hr x ≠ 0 ↔ vRes r hr x = 1 := by
  obtain ⟨⟨n, d⟩, hd, h⟩ := exists_rep r hr x hx
  have h1 : vRes r hr (algebraMap (𝓞 L24) L24 d) = 1 := (vRes_algebraMap_eq_one_iff r hr d).mpr hd
  have h2 := congrArg (vRes r hr) h
  rw [map_mul, h1, mul_one] at h2
  rw [locRes_eq r hr x n d hd h, h2, vRes_algebraMap_eq_one_iff, div_ne_zero_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, hd⟩⟩

/-- The `𝔔`-units of `L24`. -/
def vUnits : Subgroup L24ˣ where
  carrier := {x | vRes r hr (x : L24) = 1}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, map_mul] at hx hy ⊢
    rw [hx, hy, mul_one]
  one_mem' := by simp
  inv_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at hx ⊢
    rw [hx, inv_one]

theorem mem_vUnits (x : L24ˣ) : x ∈ vUnits r hr ↔ vRes r hr (x : L24) = 1 := Iff.rfl

theorem locRes_vUnit_ne_zero (x : vUnits r hr) : locRes r hr ((x : L24ˣ) : L24) ≠ 0 :=
  (locRes_ne_zero_iff r hr _ (le_of_eq x.2)).mpr x.2

/-- The residue map on the `𝔔`-units, as a homomorphism into `kˣ`. -/
def resHom : vUnits r hr →* kˣ where
  toFun x := Units.mk0 (locRes r hr ((x : L24ˣ) : L24)) (locRes_vUnit_ne_zero r hr x)
  map_one' := by
    ext
    simp only [OneMemClass.coe_one, Units.val_one, Units.val_mk0]
    have := locRes_algebraMap r hr 1
    rw [map_one, map_one] at this
    exact this
  map_mul' x y := by
    ext
    simp only [Subgroup.coe_mul, Units.val_mul, Units.val_mk0]
    exact locRes_mul r hr _ _ (le_of_eq x.2) (le_of_eq y.2)

@[simp] theorem resHom_apply (x : vUnits r hr) :
    (resHom r hr x : k) = locRes r hr ((x : L24ˣ) : L24) := rfl

theorem wz_pow_eq_one {x : WithZero (Multiplicative ℤ)} {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1) : x = 1 := by
  induction x using WithZero.recZeroCoe with
  | zero => rw [zero_pow hn] at h; exact absurd h zero_ne_one
  | coe u =>
    rw [← WithZero.coe_pow, ← WithZero.coe_one, WithZero.coe_inj] at h
    rw [← WithZero.coe_one, WithZero.coe_inj]
    have h2 : (n : ℤ) * Multiplicative.toAdd u = 0 := by
      rw [← nsmul_eq_mul, ← toAdd_pow, h, toAdd_one]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (Int.natCast_eq_zero.mp h3) hn
    · exact toAdd_eq_zero.mp h3

/-- An element whose `n`-th power is a `𝔔`-unit is a `𝔔`-unit. -/
theorem mem_vUnits_of_pow (y : L24ˣ) (n : ℕ) (hn : n ≠ 0) (hy : y ^ n ∈ vUnits r hr) : y ∈ vUnits r hr := by
  rw [mem_vUnits] at hy ⊢
  rw [Units.val_pow_eq_pow_val, map_pow] at hy
  exact wz_pow_eq_one hn hy

end

end X2Y5Z7
