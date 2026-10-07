import X2Y5Z7.FiniteFields.Residue
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-! # Residues and fifth-power symbols on the local ring of a prime of a number field

This is the construction of `X2Y5Z7/Residue/Local.lean` for an arbitrary number field `K` (it is used for `L₈`).
A residue map `r : 𝓞 K →+* k` into a field with nonzero kernel defines a prime `ker r` (`primeK`). Every `x ∈ K`
with `v(x) ≥ 0` can be written `x = n/d` with `n, d ∈ 𝓞 K`, `r d ≠ 0`, and `resK x = r n / r d` does not depend on
the choice. It is multiplicative and nonzero exactly on the units at `ker r` (`unitsK`).

For a model `D : FiniteFields.L8Prime` of a prime of `L₈` above `q` (Section 5 and Table 6 of the paper), the
fifth-power residue symbol of the residue is a homomorphism `symL8 D` on the group of units at that prime. -/

namespace X2Y5Z7.Norm

open IsDedekindDomain NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {k : Type*} [Field k]

/-- The prime of `𝓞 K` which is the kernel of a residue map `r`. -/
def primeK (r : 𝓞 K →+* k) (hr : RingHom.ker r ≠ ⊥) : HeightOneSpectrum (𝓞 K) where
  asIdeal := RingHom.ker r
  isPrime := RingHom.ker_isPrime r
  ne_bot := hr

variable (r : 𝓞 K →+* k) (hr : RingHom.ker r ≠ ⊥)

/-- The valuation of the prime `ker r`. -/
abbrev vK : Valuation K (WithZero (Multiplicative ℤ)) := (primeK r hr).valuation K

theorem vK_algebraMap_eq_one_iff (z : 𝓞 K) : vK r hr (algebraMap (𝓞 K) K z) = 1 ↔ r z ≠ 0 := by
  rw [vK, HeightOneSpectrum.valuation_eq_one_iff_notMem]
  exact not_congr RingHom.mem_ker

theorem vK_le_one_of_mul_eq (x : K) (n d : 𝓞 K) (hd : r d ≠ 0)
    (h : x * algebraMap (𝓞 K) K d = algebraMap (𝓞 K) K n) : vK r hr x ≤ 1 := by
  have h1 : vK r hr (algebraMap (𝓞 K) K d) = 1 := (vK_algebraMap_eq_one_iff r hr d).mpr hd
  have h2 := congrArg (vK r hr) h
  rw [map_mul, h1, mul_one] at h2
  rw [h2]
  exact HeightOneSpectrum.valuation_le_one _ n

theorem exists_repK (x : K) (hx : vK r hr x ≤ 1) :
    ∃ p : 𝓞 K × 𝓞 K, r p.2 ≠ 0 ∧ x * algebraMap (𝓞 K) K p.2 = algebraMap (𝓞 K) K p.1 := by
  obtain ⟨n, d, h⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (primeK r hr) x hx
  exact ⟨(n, d), fun h0 => (Ideal.mem_primeCompl_iff.mp d.2) (RingHom.mem_ker.mpr h0), h⟩

open Classical in
/-- The residue of an element of the local ring at `ker r` (junk value `0` elsewhere). -/
def resK (x : K) : k :=
  if h : vK r hr x ≤ 1 then
    r (Classical.choose (exists_repK r hr x h)).1 / r (Classical.choose (exists_repK r hr x h)).2
  else 0

theorem resK_eq (x : K) (n d : 𝓞 K) (hd : r d ≠ 0)
    (h : x * algebraMap (𝓞 K) K d = algebraMap (𝓞 K) K n) : resK r hr x = r n / r d := by
  have hx := vK_le_one_of_mul_eq r hr x n d hd h
  rw [resK, dite_eq_left hx]
  obtain ⟨hd', h'⟩ := Classical.choose_spec (exists_repK r hr x hx)
  set n' := (Classical.choose (exists_repK r hr x hx)).1
  set d' := (Classical.choose (exists_repK r hr x hx)).2
  have key : n * d' = n' * d := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [map_mul, map_mul, ← h, ← h']
    ring
  have key' := congrArg r key
  rw [map_mul, map_mul] at key'
  rw [div_eq_div_iff hd' hd]
  linear_combination -key'

theorem resK_mul (x y : K) (hx : vK r hr x ≤ 1) (hy : vK r hr y ≤ 1) :
    resK r hr (x * y) = resK r hr x * resK r hr y := by
  obtain ⟨⟨n, d⟩, hd, h⟩ := exists_repK r hr x hx
  obtain ⟨⟨n', d'⟩, hd', h'⟩ := exists_repK r hr y hy
  rw [resK_eq r hr x n d hd h, resK_eq r hr y n' d' hd' h',
    resK_eq r hr (x * y) (n * n') (d * d') (by rw [map_mul]; exact mul_ne_zero hd hd')
      (by rw [map_mul, map_mul, ← h, ← h']; ring), map_mul, map_mul, div_mul_div_comm]

theorem resK_one : resK r hr (1 : K) = 1 := by
  rw [resK_eq r hr 1 1 1 (by simp) (by simp), map_one, div_one]

theorem resK_ne_zero_iff (x : K) (hx : vK r hr x ≤ 1) : resK r hr x ≠ 0 ↔ vK r hr x = 1 := by
  obtain ⟨⟨n, d⟩, hd, h⟩ := exists_repK r hr x hx
  have h1 : vK r hr (algebraMap (𝓞 K) K d) = 1 := (vK_algebraMap_eq_one_iff r hr d).mpr hd
  have h2 := congrArg (vK r hr) h
  rw [map_mul, h1, mul_one] at h2
  rw [resK_eq r hr x n d hd h, h2, vK_algebraMap_eq_one_iff, div_ne_zero_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, hd⟩⟩

/-- The units of `K` at the prime `ker r`. -/
def unitsK : Subgroup Kˣ where
  carrier := {x | vK r hr (x : K) = 1}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, map_mul] at hx hy ⊢
    rw [hx, hy, mul_one]
  one_mem' := by simp
  inv_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at hx ⊢
    rw [hx, inv_one]

theorem mem_unitsK (x : Kˣ) : x ∈ unitsK r hr ↔ vK r hr (x : K) = 1 := Iff.rfl

theorem resK_unit_ne_zero (x : unitsK r hr) : resK r hr ((x : Kˣ) : K) ≠ 0 :=
  (resK_ne_zero_iff r hr _ (le_of_eq x.2)).mpr x.2

/-- The residue map on the units at `ker r`, as a homomorphism into `kˣ`. -/
def resHomK : unitsK r hr →* kˣ where
  toFun x := Units.mk0 (resK r hr ((x : Kˣ) : K)) (resK_unit_ne_zero r hr x)
  map_one' := by
    ext
    simp only [OneMemClass.coe_one, Units.val_one, Units.val_mk0]
    exact resK_one r hr
  map_mul' x y := by
    ext
    simp only [Subgroup.coe_mul, Units.val_mul, Units.val_mk0]
    exact resK_mul r hr _ _ (le_of_eq x.2) (le_of_eq y.2)

theorem wz_pow_eq_one' {x : WithZero (Multiplicative ℤ)} {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1) : x = 1 := by
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

/-- An element whose `n`-th power is a unit at `ker r` is itself one. -/
theorem mem_unitsK_of_pow (y : Kˣ) (n : ℕ) (hn : n ≠ 0) (hy : y ^ n ∈ unitsK r hr) : y ∈ unitsK r hr := by
  rw [mem_unitsK] at hy ⊢
  rw [Units.val_pow_eq_pow_val, map_pow] at hy
  exact wz_pow_eq_one' hn hy

/-- An element `x = n/d` with `n, d ∈ 𝓞 K` and `r n, r d ≠ 0` is a unit at `ker r`, with residue `r n / r d`. -/
theorem mem_unitsK_of_frac (x : Kˣ) (n d : 𝓞 K) (hn : r n ≠ 0) (hd : r d ≠ 0)
    (h : (x : K) * algebraMap (𝓞 K) K d = algebraMap (𝓞 K) K n) :
    x ∈ unitsK r hr ∧ resK r hr (x : K) = r n / r d := by
  have hres := resK_eq r hr (x : K) n d hd h
  refine ⟨(mem_unitsK r hr x).mpr ((resK_ne_zero_iff r hr _ (vK_le_one_of_mul_eq r hr _ n d hd h)).mp ?_), hres⟩
  rw [hres]
  exact div_ne_zero hn hd

/-! ## Symbols at the model primes of `L₈` -/

open FiniteFields

variable (D : L8Prime)

theorem L8res_ker_ne_bot : RingHom.ker D.res ≠ ⊥ := by
  intro h
  have hq : ((D.q : ℕ) : 𝓞 L8) ∈ RingHom.ker D.res := by
    rw [RingHom.mem_ker, map_natCast, D.char]
  rw [h, Ideal.mem_bot] at hq
  exact (Nat.cast_ne_zero.mpr D.prime.ne_zero) hq

/-- The units of `L₈` at the model prime `D`. -/
abbrev unitsL8 : Subgroup L8ˣ := unitsK D.res (L8res_ker_ne_bot D)

/-- The fifth-power symbol of a unit at the model prime `D`. -/
def symL8 : unitsL8 D →* Multiplicative (ZMod 5) where
  toFun x := Multiplicative.ofAdd (D.sym (resHomK D.res (L8res_ker_ne_bot D) x : D.K))
  map_one' := by
    rw [map_one, Units.val_one, D.sym_one, ofAdd_zero]
  map_mul' x y := by
    rw [map_mul, Units.val_mul, D.sym_mul (Units.ne_zero _) (Units.ne_zero _), ofAdd_add]

theorem symL8_apply (x : unitsL8 D) :
    Multiplicative.toAdd (symL8 D x) = D.sym (resK D.res (L8res_ker_ne_bot D) ((x : L8ˣ) : L8)) := rfl

end

end X2Y5Z7.Norm
