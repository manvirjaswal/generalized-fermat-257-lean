import X2Y5Z7.FiniteFields.Residue
import X2Y5Z7.Auxiliary.GenDegreeSum

/-! # Primes of `L8` above an auxiliary prime as residue maps

For a model `D : L8Prime` (`D.K = F_q[x]/(h_i)`, `D.res : 𝓞 L8 →+* D.K`, `a8 ↦ x`):
* `D.toResidueMap : Aux.ResidueMap L8 D.q`, with `r = D.res` (surjective since `x` generates `D.K`);
* `D.deg_toResidueMap : D.toResidueMap.deg = D.f` (`= deg h_i`);
* `ker_res_ne D E h`: if `h_i(x_E) ≠ 0` in `E.K` (checked by `eqL`), then `ker D.res ≠ ker E.res`
  (`h_i(a8)` lies in `ker D.res` but not in `ker E.res`).
Generic facts for a residue map `R : Aux.ResidueMap K q`: `(q : R.k) = 0` and `(n : R.k) ≠ 0` when
`(n : ZMod q) ≠ 0`. -/

namespace X2Y5Z7.Primes

open Polynomial NumberField X2Y5Z7.FiniteFields

noncomputable section

/-- A ring homomorphism commutes with `evL`. -/
theorem map_evL {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    ∀ L : List ℕ, f (evL a L) = evL (f a) L
  | [] => by simp [evL]
  | c :: cs => by simp [evL, map_evL f a cs]

end

end X2Y5Z7.Primes

namespace X2Y5Z7.FiniteFields.L8Prime

open Polynomial NumberField X2Y5Z7.FiniteFields X2Y5Z7.Primes

noncomputable section

variable (D : L8Prime)

/-- `x` generates `D.K`. -/
theorem adjoin_x : Algebra.adjoin (ZMod D.q) ({D.x} : Set D.K) = ⊤ := by
  rw [D.x_eq_root]; exact AdjoinRoot.adjoinRoot_eq_top

theorem res_surjective : Function.Surjective D.res :=
  Aux.surjective_of_adjoin D.res a8 (by rw [D.res_a8]; exact D.adjoin_x)

/-- The prime of `L8` given by the model `D`, as a residue map. -/
def toResidueMap : Aux.ResidueMap L8 D.q where
  k := D.K
  r := D.res
  surj := D.res_surjective

@[simp] theorem toResidueMap_r : D.toResidueMap.r = D.res := rfl

theorem finrank_K : Module.finrank (ZMod D.q) D.K = D.f := by
  rw [(AdjoinRoot.powerBasis' D.monic).finrank, AdjoinRoot.powerBasis'_dim, D.natDegree]

theorem deg_toResidueMap : D.toResidueMap.deg = D.f := D.finrank_K

/-- `r(evL a8 A) = D.ev A`. -/
theorem res_evL (A : List ℕ) : D.res (evL a8 A) = D.ev A := by
  rw [map_evL, D.res_a8, L8Prime.x_eq_root]
  rfl

theorem res_evL_self : D.res (evL a8 D.P) = 0 := by
  rw [D.res_evL, FFModel.ev, ev_eq_mk, AdjoinRoot.mk_self]

/-- Distinct kernels, certified by `h_D(x_E) ≠ 0` in `E.K`. -/
theorem ker_res_ne (E : L8Prime) (h : eqL E.q (ruleOf E.q E.P) D.P [] = false) :
    RingHom.ker D.res ≠ RingHom.ker E.res := by
  intro hk
  have h1 : evL a8 D.P ∈ RingHom.ker D.res := D.res_evL_self
  rw [hk, RingHom.mem_ker, E.res_evL] at h1
  exact E.ev_ne_zero_of_eqL _ h h1

end

end X2Y5Z7.FiniteFields.L8Prime

namespace X2Y5Z7.Primes

open Polynomial NumberField X2Y5Z7.FiniteFields

noncomputable section

section Generic

variable {K : Type*} [Field K] {q : ℕ} [Fact q.Prime]

theorem natCast_self (R : Aux.ResidueMap K q) : ((q : ℕ) : R.k) = 0 := by
  rw [← map_natCast (algebraMap (ZMod q) R.k), ZMod.natCast_self, map_zero]

theorem natCast_ne_zero (R : Aux.ResidueMap K q) (n : ℕ) (h : (n : ZMod q) ≠ 0) : (n : R.k) ≠ 0 := by
  rw [← map_natCast (algebraMap (ZMod q) R.k)]
  exact fun h0 => h ((algebraMap (ZMod q) R.k).injective (h0.trans (map_zero _).symm))

end Generic

end

end X2Y5Z7.Primes
