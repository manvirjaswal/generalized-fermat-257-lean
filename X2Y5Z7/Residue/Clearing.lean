import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Extending a residue map by clearing denominators

Let `A` be a subalgebra of a commutative ring `S`, and `r₀ : A →+* k` a ring homomorphism into a field. If an element
`D ∈ A` has `r₀ D ≠ 0` and `D z ∈ A` for every `z ∈ S`, then `z ↦ r₀ (D z) / r₀ D` is a ring homomorphism
`S →+* k` extending `r₀`, and it is the only one. This is how residue maps of a ring of integers are built from those
of an order: `D` is the derivative of a minimal polynomial, which lies in the conductor. -/

namespace X2Y5Z7

variable {R S k : Type*} [CommRing R] [CommRing S] [Algebra R S] [Field k]

/-- The extension of `r₀ : A →+* k` to `S` through the clearing element `D`. -/
def extendByClearing (A : Subalgebra R S) (r₀ : A →+* k) (D : A) (hD : r₀ D ≠ 0)
    (hcl : ∀ z : S, (D : S) * z ∈ A) : S →+* k where
  toFun z := r₀ ⟨(D : S) * z, hcl z⟩ / r₀ D
  map_one' := by
    have : (⟨(D : S) * 1, hcl 1⟩ : A) = D := Subtype.ext (mul_one _)
    rw [this, div_self hD]
  map_mul' z w := by
    have key : r₀ ⟨(D : S) * (z * w), hcl (z * w)⟩ * r₀ D =
        r₀ ⟨(D : S) * z, hcl z⟩ * r₀ ⟨(D : S) * w, hcl w⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subalgebra.coe_mul]
      ring
    field_simp
    linear_combination key
  map_zero' := by
    have : (⟨(D : S) * 0, hcl 0⟩ : A) = 0 := Subtype.ext (mul_zero _)
    rw [this, map_zero, zero_div]
  map_add' z w := by
    rw [← add_div, ← map_add]
    congr 2
    apply Subtype.ext
    simp only [Subalgebra.coe_add]
    ring

theorem extendByClearing_apply (A : Subalgebra R S) (r₀ : A →+* k) (D : A) (hD : r₀ D ≠ 0)
    (hcl : ∀ z : S, (D : S) * z ∈ A) (z : S) :
    extendByClearing A r₀ D hD hcl z = r₀ ⟨(D : S) * z, hcl z⟩ / r₀ D := rfl

/-- The extension agrees with `r₀` on `A`. -/
theorem extendByClearing_coe (A : Subalgebra R S) (r₀ : A →+* k) (D : A) (hD : r₀ D ≠ 0)
    (hcl : ∀ z : S, (D : S) * z ∈ A) (x : A) : extendByClearing A r₀ D hD hcl (x : S) = r₀ x := by
  rw [extendByClearing_apply, div_eq_iff hD, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subalgebra.coe_mul]
  ring

/-- Uniqueness: a ring homomorphism `S →+* k` is determined by its values on `A`, when some `D ∈ A` with `D S ⊆ A`
is sent to a nonzero element. -/
theorem ringHom_eq_of_clearing (A : Subalgebra R S) (f g : S →+* k) (D : S) (hDA : ∀ z : S, D * z ∈ A)
    (hD : f D ≠ 0) (hfg : ∀ x ∈ A, f x = g x) : f = g := by
  have hD1 : D ∈ A := by simpa using hDA 1
  have hgD : g D ≠ 0 := by rw [← hfg D hD1]; exact hD
  ext z
  have h := hfg (D * z) (hDA z)
  rw [map_mul, map_mul, hfg D hD1] at h
  exact mul_left_cancel₀ hgD h

end X2Y5Z7
