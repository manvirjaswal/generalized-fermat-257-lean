import X2Y5Z7.Auxiliary.Distinct

/-! # Residue degrees of several primes versus the factorization of a polynomial mod `q`

For a family of primes (residue maps onto finite fields of characteristic `q`) with pairwise distinct kernels, all
satisfying the derivative condition for `θ`, the minimal polynomials of the residues of `θ` are pairwise distinct monic
irreducibles. Hence:
* if each residue of `θ` is a root of `P ≠ 0`, the residue degrees sum to at most `deg P`;
* if `P = ∏ φ j` with `φ j` monic irreducible, each minimal polynomial is some `φ j`, injectively; if the degree sum is
  `deg P` this is a bijection, so the multiset of residue degrees is that of the `deg φ j`, and each root of `P` in
  `ZMod q` is the residue of `θ` at a prime of residue degree one. -/

namespace X2Y5Z7.Aux

open Polynomial
open scoped NumberField

noncomputable section

/-- A prime of `𝓞 K` above `q`, presented as a surjective residue map onto a finite field of characteristic `q`. -/
structure ResidueMap (K : Type*) [Field K] (q : ℕ) where
  /-- The residue field. -/
  k : Type
  [instField : Field k]
  [instFinite : Finite k]
  [instAlgebra : Algebra (ZMod q) k]
  /-- The residue map. -/
  r : 𝓞 K →+* k
  surj : Function.Surjective r

attribute [instance] ResidueMap.instField ResidueMap.instFinite ResidueMap.instAlgebra

variable {K : Type*} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]

/-- The residue degree `[k : ZMod q]`. -/
abbrev ResidueMap.deg (R : ResidueMap K q) : ℕ := Module.finrank (ZMod q) R.k

section

variable (θ : 𝓞 K) (hθ : Algebra.adjoin ℚ ({(θ : K)} : Set K) = ⊤)
  {ι : Type*} [Fintype ι] (R : ι → ResidueMap K q)
  (hker : Pairwise fun i j => RingHom.ker (R i).r ≠ RingHom.ker (R j).r)
  (hd : ∀ i, (R i).r (derivativeInteger θ) ≠ 0)

include hθ hker hd

omit [Fintype ι] in
theorem minpoly_injective : Function.Injective fun i => minpoly (ZMod q) ((R i).r θ) := by
  intro i j hij
  by_contra hne
  exact minpoly_ne_of_ker_ne θ hθ (R i).r (R i).surj (hd i) (R j).r (R j).surj (hd j) (hker hne) hij

omit [Fintype ι] in
theorem minpoly_pairwise_isCoprime :
    Pairwise (Function.onFun IsCoprime fun i => minpoly (ZMod q) ((R i).r θ)) := by
  intro i j hij
  have hi : Irreducible (minpoly (ZMod q) ((R i).r θ)) := minpoly.irreducible (IsIntegral.of_finite _ _)
  have hj : Irreducible (minpoly (ZMod q) ((R j).r θ)) := minpoly.irreducible (IsIntegral.of_finite _ _)
  change IsCoprime (minpoly (ZMod q) ((R i).r θ)) (minpoly (ZMod q) ((R j).r θ))
  rw [hi.coprime_iff_not_dvd]
  intro hdvd
  apply hij
  apply minpoly_injective θ hθ R hker hd
  exact eq_of_monic_of_associated (minpoly.monic (IsIntegral.of_finite _ _))
    (minpoly.monic (IsIntegral.of_finite _ _)) (hi.associated_of_dvd hj hdvd)

/-- The product of the minimal polynomials divides any polynomial killing all the residues of `θ`. -/
theorem prod_minpoly_dvd (P : (ZMod q)[X]) (hroot : ∀ i, aeval ((R i).r θ) P = 0) :
    ∏ i, minpoly (ZMod q) ((R i).r θ) ∣ P :=
  Fintype.prod_dvd_of_coprime (minpoly_pairwise_isCoprime θ hθ R hker hd) fun i => minpoly.dvd _ _ (hroot i)

/-- **Degree sum.** -/
theorem sum_deg_le (P : (ZMod q)[X]) (hP : P ≠ 0) (hroot : ∀ i, aeval ((R i).r θ) P = 0) :
    ∑ i, (R i).deg ≤ P.natDegree := by
  have h := natDegree_le_of_dvd (prod_minpoly_dvd θ hθ R hker hd P hroot) hP
  rw [natDegree_prod _ _ fun i _ => minpoly.ne_zero (IsIntegral.of_finite _ _)] at h
  simpa only [ResidueMap.deg, minpoly_degree θ (R _).r (R _).surj hθ (hd _)] using h

variable {κ : Type*} [Fintype κ] (φ : κ → (ZMod q)[X]) (hφm : ∀ j, (φ j).Monic)
  (hφi : ∀ j, Irreducible (φ j))

include hφm hφi

omit [Fintype ι] in
/-- Each minimal polynomial of a residue of `θ` is one of the factors `φ j`, injectively. -/
theorem exists_factor_map (hroot : ∀ i, aeval ((R i).r θ) (∏ j, φ j) = 0) :
    ∃ σ : ι → κ, Function.Injective σ ∧ ∀ i, minpoly (ZMod q) ((R i).r θ) = φ (σ i) := by
  have hex : ∀ i, ∃ j, minpoly (ZMod q) ((R i).r θ) = φ j := by
    intro i
    have hint : IsIntegral (ZMod q) ((R i).r θ) := IsIntegral.of_finite _ _
    have hdvd := minpoly.dvd _ _ (hroot i)
    obtain ⟨j, -, hj⟩ := ((minpoly.irreducible hint).prime.dvd_finsetProd_iff _).mp hdvd
    exact ⟨j, eq_of_monic_of_associated (minpoly.monic hint) (hφm j)
      ((minpoly.irreducible hint).associated_of_dvd (hφi j) hj)⟩
  choose σ hσ using hex
  refine ⟨σ, fun i i' h => minpoly_injective θ hθ R hker hd ?_, hσ⟩
  simp only [hσ, h]

omit hker hd hθ hφm in
theorem natDegree_prod_factors : (∏ j, φ j).natDegree = ∑ j, (φ j).natDegree :=
  natDegree_prod _ _ fun j _ => (hφi j).ne_zero

omit hker hφm in
/-- If moreover the residue degrees add up to `deg ∏ φ j`, the matching is a bijection. -/
theorem factor_map_bijective (hsum : ∑ i, (R i).deg = (∏ j, φ j).natDegree) (σ : ι → κ) (hσi : Function.Injective σ)
    (hσ : ∀ i, minpoly (ZMod q) ((R i).r θ) = φ (σ i)) : Function.Bijective σ := by
  classical
  refine ⟨hσi, ?_⟩
  have hdeg : ∀ i, (R i).deg = (φ (σ i)).natDegree := fun i => by
    rw [← hσ, minpoly_degree θ (R i).r (R i).surj hθ (hd i)]
  have himg : ∑ j ∈ Finset.univ.image σ, (φ j).natDegree = ∑ j, (φ j).natDegree := by
    rw [Finset.sum_image fun a _ b _ h => hσi h, ← natDegree_prod_factors φ hφi, ← hsum]
    exact Finset.sum_congr rfl fun i _ => (hdeg i).symm
  intro j
  by_contra hj
  simp only [not_exists] at hj
  have hjn : j ∉ Finset.univ.image σ := by simpa using hj
  have hlt : ∑ j ∈ Finset.univ.image σ, (φ j).natDegree < ∑ j, (φ j).natDegree :=
    Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (Finset.mem_univ j) hjn
      (hφi j).natDegree_pos (fun _ _ _ => Nat.zero_le _)
  omega

/-- Under the bijection, the multiset of residue degrees is the multiset of the degrees of the factors. -/
theorem multiset_deg_eq (hroot : ∀ i, aeval ((R i).r θ) (∏ j, φ j) = 0)
    (hsum : ∑ i, (R i).deg = (∏ j, φ j).natDegree) :
    Finset.univ.val.map (fun i => (R i).deg) = Finset.univ.val.map (fun j => (φ j).natDegree) := by
  obtain ⟨σ, hσi, hσ⟩ := exists_factor_map θ hθ R hker hd φ hφm hφi hroot
  have hb := factor_map_bijective θ hθ R hd φ hφi hsum σ hσi hσ
  let e := Equiv.ofBijective σ hb
  have hdeg : (fun i => (R i).deg) = (fun j => (φ j).natDegree) ∘ e := by
    funext i
    simp only [Function.comp_apply, e, Equiv.ofBijective_apply]
    rw [← hσ, minpoly_degree θ (R i).r (R i).surj hθ (hd i)]
  rw [hdeg, ← Multiset.map_map]
  congr 1
  have := Finset.map_univ_equiv e
  rw [← this, Finset.map_val]
  rfl

/-- Under the bijection, every root of `∏ φ j` in `ZMod q` is the residue of `θ` at a prime of residue degree one. -/
theorem exists_of_root (hroot : ∀ i, aeval ((R i).r θ) (∏ j, φ j) = 0)
    (hsum : ∑ i, (R i).deg = (∏ j, φ j).natDegree) (c : ZMod q) (hc : (∏ j, φ j).IsRoot c) :
    ∃ i, (R i).r θ = algebraMap (ZMod q) (R i).k c ∧ (R i).deg = 1 := by
  obtain ⟨σ, hσi, hσ⟩ := exists_factor_map θ hθ R hker hd φ hφm hφi hroot
  have hb := factor_map_bijective θ hθ R hd φ hφi hsum σ hσi hσ
  have hdvd : X - C c ∣ ∏ j, φ j := dvd_iff_isRoot.mpr hc
  obtain ⟨j, -, hj⟩ := ((prime_X_sub_C c).dvd_finsetProd_iff _).mp hdvd
  have hjeq : X - C c = φ j :=
    eq_of_monic_of_associated (monic_X_sub_C c) (hφm j)
      ((irreducible_X_sub_C c).associated_of_dvd (hφi j) hj)
  obtain ⟨i, rfl⟩ := hb.2 j
  refine ⟨i, ?_, ?_⟩
  · have h0 : aeval ((R i).r θ) (X - C c) = 0 := by rw [hjeq, ← hσ]; exact minpoly.aeval _ _
    rw [map_sub, aeval_X, aeval_C, sub_eq_zero] at h0
    exact h0
  · rw [ResidueMap.deg, ← minpoly_degree θ (R i).r (R i).surj hθ (hd i), hσ, ← hjeq, natDegree_X_sub_C]

end

end

end X2Y5Z7.Aux
