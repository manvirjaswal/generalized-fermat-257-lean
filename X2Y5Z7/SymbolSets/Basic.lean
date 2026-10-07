module

public import X2Y5Z7.FiniteFields.Model

@[expose] public section

/-! # Proposition 5.3: generic lemmas

* Exact polynomial arithmetic on coefficient lists over `F_q` (`pmulL`, `prodL`, `peqL`), with
  `toPoly_pmulL`, `toPoly_prodL`, `toPoly_eq_of_peqL`; evaluation at a natural number (`hornerN`) and at a list
  element of a model (`evalNL`).
* `mem_of_roots`: a root of a nonzero polynomial of degree `d` with `d` known distinct roots is one of them.
* Polynomial-level consequences for a family `m : Fin r → F_q[X]` of distinct monic irreducible divisors of a monic
  `toPoly q FM`: `g_bound` (a gcd certificate bounds the degree sum of the `m i` with `deg m i ∣ d`), `r_bound`
  (when `∑ deg m i = deg FM`, the roots in `F_q` inject into the degree-one indices), `f_match` (each `m i` is one of
  the listed irreducible factors).
* The embedding `iotaG : F_q[x]/(H) → F_q[z]/(P)`, `x ↦ α`, the element `EvG = 80000 (ι t - β) ψ(ι t)³`, its list
  computation `eList` (`ev_eList`) and the symbol `symG` with `symG_of_symCheck`. -/

namespace X2Y5Z7.SymbolSets

open Polynomial X2Y5Z7.FiniteFields

/-! ## Exact polynomial arithmetic on lists -/

/-- The product of two polynomials (no reduction). -/
def pmulL (q : ℕ) : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | a :: A, B => addL q (smulL q a B) (0 :: pmulL q A B)

/-- The product of a list of polynomials. -/
def prodL (q : ℕ) : List (List ℕ) → List ℕ
  | [] => [1]
  | A :: As => pmulL q A (prodL q As)

/-- Equality of polynomials over `F_q`. -/
def peqL (q : ℕ) (A B : List ℕ) : Bool := isZeroL q (subL q A B)

/-- `A(c) mod q` (Horner). -/
def hornerN (q c : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: A => (a + c * hornerN q c A) % q

/-- `A(Y)` in the model with rule `N`, for a polynomial `A` with natural coefficients (Horner). -/
def evalNL (q : ℕ) (N Y : List ℕ) : List ℕ → List ℕ
  | [] => []
  | c :: cs => addL q [c % q] (mulL q N Y (evalNL q N Y cs))

section Exact

variable {R : Type*} [CommRing R] {q : ℕ} {x : R}

theorem evL_pmulL (hq : (q : R) = 0) : ∀ A B : List ℕ, evL x (pmulL q A B) = evL x A * evL x B
  | [], B => by simp [pmulL]
  | a :: A, B => by
    rw [pmulL, evL_addL hq, evL_smulL hq, evL_cons, evL_pmulL hq A B, evL_cons]; push_cast; ring

theorem evL_prodL (hq : (q : R) = 0) : ∀ As : List (List ℕ), evL x (prodL q As) = (As.map (evL x)).prod
  | [] => by simp [prodL]
  | A :: As => by rw [prodL, evL_pmulL hq, evL_prodL hq As]; simp

theorem evL_eq_of_peqL (hq0 : 0 < q) (hq : (q : R) = 0) {A B : List ℕ} (h : peqL q A B = true) :
    evL x A = evL x B := by
  have := evL_eq_zero_of_isZeroL (x := x) hq _ h
  rwa [evL_subL hq0 hq, sub_eq_zero] at this

theorem map_evL {S : Type*} [CommRing S] (f : R →+* S) (y : R) : ∀ A : List ℕ, f (evL y A) = evL (f y) A
  | [] => by simp
  | c :: cs => by simp [map_evL f y cs]

theorem length_evalNL {N : List ℕ} (hf : 0 < N.length) (Y : List ℕ) :
    ∀ A : List ℕ, (evalNL q N Y A).length ≤ N.length
  | [] => by simp [evalNL]
  | c :: cs => by
    rw [evalNL, length_addL]
    exact max_le (by simp; omega) (length_mulL hf _ _ (length_evalNL hf Y cs))

theorem evL_evalNL {N : List ℕ} (hM : IsModel q N x) (Y : List ℕ) :
    ∀ A : List ℕ, evL x (evalNL q N Y A) = evL (evL x Y) A
  | [] => by simp [evalNL]
  | c :: cs => by
    rw [evalNL, evL_addL hM.char, evL_mulL hM _ _ (length_evalNL hM.fpos Y cs), evL_evalNL hM Y cs]
    simp [natCast_mod hM.char]

end Exact

theorem charX (q : ℕ) : ((q : ℕ) : (ZMod q)[X]) = 0 := by
  rw [← Polynomial.C_eq_natCast, ZMod.natCast_self, map_zero]

theorem toPoly_eq_evL (q : ℕ) : ∀ A : List ℕ, toPoly q A = evL (X : (ZMod q)[X]) A
  | [] => rfl
  | c :: cs => by simp [toPoly, toPoly_eq_evL q cs]

theorem toPoly_fun (q : ℕ) : toPoly q = evL (X : (ZMod q)[X]) := funext (toPoly_eq_evL q)

theorem toPoly_pmulL (q : ℕ) (A B : List ℕ) : toPoly q (pmulL q A B) = toPoly q A * toPoly q B := by
  rw [toPoly_fun]; exact evL_pmulL (charX q) A B

theorem toPoly_prodL (q : ℕ) (As : List (List ℕ)) : toPoly q (prodL q As) = (As.map (toPoly q)).prod := by
  rw [toPoly_fun]; exact evL_prodL (charX q) As

theorem toPoly_addL (q : ℕ) (A B : List ℕ) : toPoly q (addL q A B) = toPoly q A + toPoly q B := by
  rw [toPoly_fun]; exact evL_addL (charX q) A B

theorem toPoly_subL {q : ℕ} (hq0 : 0 < q) (A B : List ℕ) : toPoly q (subL q A B) = toPoly q A - toPoly q B := by
  rw [toPoly_fun]; exact evL_subL hq0 (charX q) A B

theorem toPoly_eq_of_peqL {q : ℕ} (hq0 : 0 < q) {A B : List ℕ} (h : peqL q A B = true) :
    toPoly q A = toPoly q B := by
  rw [toPoly_fun]; exact evL_eq_of_peqL hq0 (charX q) h

theorem toPoly_X (q : ℕ) : toPoly q [0, 1] = X := by simp [toPoly]

theorem toPoly_ne_zero {q : ℕ} {A : List ℕ} (h : isZeroL q A = false) : toPoly q A ≠ 0 := fun h0 => by
  rw [isZeroL_of_toPoly_eq_zero q A h0] at h; exact Bool.noConfusion h

theorem hornerN_eq (q c : ℕ) : ∀ A : List ℕ, ((hornerN q c A : ℕ) : ZMod q) = (toPoly q A).eval (c : ZMod q)
  | [] => by simp [hornerN, toPoly]
  | a :: A => by
    rw [hornerN, ZMod.natCast_mod]; simp [toPoly, hornerN_eq q c A]

/-! ## Roots in a field -/

/-- A root of `p ≠ 0` is one of `natDegree p` distinct known roots. -/
theorem mem_of_roots {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [Algebra (ZMod q) K] {p : (ZMod q)[X]}
    (hp : p ≠ 0) (rs : List K) (hnd : rs.Nodup) (hlen : rs.length = p.natDegree) (hr : ∀ a ∈ rs, aeval a p = 0)
    {t : K} (ht : aeval t p = 0) : t ∈ rs := by
  classical
  by_contra hn
  have hp' : p.map (algebraMap (ZMod q) K) ≠ 0 := Polynomial.map_ne_zero hp
  have hsub : (insert t rs.toFinset).val ⊆ (p.map (algebraMap (ZMod q) K)).roots := by
    intro a ha
    rw [Finset.mem_val] at ha
    rw [mem_roots hp', IsRoot, eval_map_algebraMap]
    rcases Finset.mem_insert.mp ha with rfl | h
    · exact ht
    · exact hr a (List.mem_toFinset.mp h)
  have := card_le_degree_of_subset_roots hsub
  rw [Finset.card_insert_of_notMem (by simpa using hn), List.toFinset_card_of_nodup hnd, natDegree_map] at this
  omega

/-! ## A family of distinct monic irreducible divisors -/

section Family

variable {q : ℕ} [hq : Fact q.Prime] {r : ℕ} (m : Fin r → (ZMod q)[X]) (hirr : ∀ i, Irreducible (m i))
  (hmon : ∀ i, (m i).Monic) (hinj : Function.Injective m)

include hirr hmon hinj in
theorem pairwise_coprime : Pairwise (Function.onFun IsCoprime m) := by
  intro i j hij
  change IsCoprime (m i) (m j)
  rw [(hirr i).coprime_iff_not_dvd]
  intro hdvd
  exact hij (hinj (eq_of_monic_of_associated (hmon i) (hmon j) ((hirr i).associated_of_dvd (hirr j) hdvd)))

include hirr hmon hinj in
theorem prod_dvd (S : Finset (Fin r)) (p : (ZMod q)[X]) (h : ∀ i ∈ S, m i ∣ p) : ∏ i ∈ S, m i ∣ p :=
  Finset.prod_dvd_of_coprime (fun _ _ _ _ hij => pairwise_coprime m hirr hmon hinj hij) h

include hirr in
theorem natDegree_prod_m (S : Finset (Fin r)) : (∏ i ∈ S, m i).natDegree = ∑ i ∈ S, (m i).natDegree :=
  natDegree_prod _ _ fun i _ => (hirr i).ne_zero

/-- The image of `X^(q^d)` in `F_q[X]/(FM)`, computed by `powL`, differs from `X^(q^d)` by a multiple of `FM`. -/
theorem dvd_frob {FM : List ℕ} (hv : validP FM = true) (d : ℕ) :
    toPoly q FM ∣ toPoly q (powL q (ruleOf q FM) [0, 1] (q ^ d)) - X ^ (q ^ d) := by
  have h := ev_powL hq.out.pos hv [0, 1] (q ^ d)
  rw [ev_eq_mk, ev_eq_mk, toPoly_X, ← map_pow] at h
  exact AdjoinRoot.mk_eq_mk.mp h

include hirr hmon hinj in
/-- **Gcd certificates.** If `A·FM + B·(X^(q^d) mod FM - X) = g ≠ 0`, the `m i` of degree dividing `d` have degree
sum at most `deg g < length g`. -/
theorem g_bound {FM g A B : List ℕ} (hv : validP FM = true) (d : ℕ) (hdvd : ∀ i, m i ∣ toPoly q FM)
    (hid : toPoly q A * toPoly q FM + toPoly q B * (toPoly q (powL q (ruleOf q FM) [0, 1] (q ^ d)) - X) =
      toPoly q g) (hg : toPoly q g ≠ 0) :
    ∑ i ∈ Finset.univ.filter (fun i => (m i).natDegree ∣ d), (m i).natDegree < g.length := by
  have hdiv : ∀ i ∈ Finset.univ.filter (fun i => (m i).natDegree ∣ d), m i ∣ toPoly q g := by
    intro i hi
    have hd : (m i).natDegree ∣ d := (Finset.mem_filter.mp hi).2
    have h1 : m i ∣ X ^ q ^ d - X := by
      have := dvd_X_pow_card_pow_sub_X_of_natDegree_dvd (hirr i) hd
      rwa [ZMod.card] at this
    have h2 : m i ∣ toPoly q (powL q (ruleOf q FM) [0, 1] (q ^ d)) - X := by
      have := dvd_add ((hdvd i).trans (dvd_frob hv d)) h1
      rwa [sub_add_sub_cancel] at this
    rw [← hid]
    exact dvd_add (dvd_mul_of_dvd_right (hdvd i) _) (dvd_mul_of_dvd_right h2 _)
  have h := natDegree_le_of_dvd (prod_dvd m hirr hmon hinj _ _ hdiv) hg
  rw [natDegree_prod_m m hirr] at h
  have h2 : (toPoly q g).natDegree < g.length := by
    rw [natDegree_lt_iff_degree_lt hg]; exact degree_toPoly_lt q g
  omega

include hirr hmon hinj in
/-- **Roots in `F_q`.** If `∑ deg m i = deg FM`, distinct roots of `FM` in `F_q` inject into the indices with
`deg m i = 1`. -/
theorem r_bound {FM : List ℕ} (hv : validP FM = true) (hdvd : ∀ i, m i ∣ toPoly q FM)
    (hsum : ∑ i, (m i).natDegree = FM.length - 1) (rs : List ℕ) (hnd : rs.Nodup) (hlt : ∀ c ∈ rs, c < q)
    (hroot : ∀ c ∈ rs, (toPoly q FM).eval (c : ZMod q) = 0) :
    rs.length ≤ (Finset.univ.filter (fun i => (m i).natDegree = 1)).card := by
  classical
  obtain ⟨hmonF, hdegF⟩ := toPoly_monic (q := q) hv
  have hprod : toPoly q FM = ∏ i, m i := by
    refine eq_of_monic_of_dvd_of_natDegree_le (monic_prod_of_monic _ _ fun i _ => hmon i) hmonF
      (prod_dvd m hirr hmon hinj _ _ fun i _ => hdvd i) ?_
    rw [hdegF, natDegree_prod_m m hirr, hsum]; simp
  have hex : ∀ c ∈ rs, ∃ i, m i = X - C (c : ZMod q) := by
    intro c hc
    have hdv : X - C (c : ZMod q) ∣ ∏ i, m i := by
      rw [← hprod]; exact dvd_iff_isRoot.mpr (hroot c hc)
    obtain ⟨i, -, hi⟩ := ((prime_X_sub_C (c : ZMod q)).dvd_finsetProd_iff _).mp hdv
    exact ⟨i, (eq_of_monic_of_associated (monic_X_sub_C _) (hmon i)
      ((irreducible_X_sub_C _).associated_of_dvd (hirr i) hi)).symm⟩
  by_cases hr0 : rs = []
  · simp [hr0]
  obtain ⟨i0, -⟩ := hex (rs.head hr0) (List.head_mem hr0)
  let f : ZMod q → Fin r := fun a => if h : ∃ i, m i = X - C a then h.choose else i0
  have hf : ∀ a, (∃ i, m i = X - C a) → m (f a) = X - C a := by
    intro a ha
    simp only [f, dite_eq_left ha]
    exact ha.choose_spec
  let S := (rs.map (fun c : ℕ => (c : ZMod q))).toFinset
  have hS : S.card = rs.length := by
    rw [List.toFinset_card_of_nodup, List.length_map]
    refine hnd.map_on fun a ha b hb hab => ?_
    have := congrArg ZMod.val hab
    rwa [ZMod.val_cast_of_lt (hlt a ha), ZMod.val_cast_of_lt (hlt b hb)] at this
  have hmem : ∀ a ∈ S, ∃ i, m i = X - C a := by
    intro a ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact hex c hc
  rw [← hS]
  refine Finset.card_le_card_of_injOn f (fun a ha => ?_) (fun a ha b hb hab => ?_)
  · rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [hf a (hmem a ha)]; exact natDegree_X_sub_C a⟩
  · have := (hf a (hmem a ha)).symm.trans (hab ▸ hf b (hmem b hb))
    exact C_injective (sub_right_injective this)

include hirr hmon in
/-- **Factorizations.** If `FM = ∏ φ` with the `φ` irreducible and monic, each `m i` is one of them. -/
theorem f_match {FM : List ℕ} (phis : List (List ℕ)) (hvφ : ∀ φ ∈ phis, validP φ = true)
    (hirrφ : ∀ φ ∈ phis, Irreducible (toPoly q φ)) (hprod : toPoly q FM = (phis.map (toPoly q)).prod)
    (hdvd : ∀ i, m i ∣ toPoly q FM) (i : Fin r) : ∃ j, ∃ hj : j < phis.length, m i = toPoly q phis[j] := by
  have h := hdvd i
  rw [hprod] at h
  obtain ⟨a, ha, hia⟩ := ((hirr i).prime.dvd_prod_iff).mp h
  obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp ha
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hφ
  exact ⟨j, hj, eq_of_monic_of_associated (hmon i) (toPoly_monic (hvφ _ hφ)).1
    ((hirr i).associated_of_dvd (hirrφ _ hφ) hia)⟩

end Family

/-! ## The embedding, the element `E` and its symbol -/

/-- The check that `x ↦ α` defines `F_q[x]/(H) → F_q[z]/(P)`: `P` valid and `H(α) = 0`. -/
def iotaOK (q : ℕ) (H P alpha : List ℕ) : Bool :=
  validP P && eqL q (ruleOf q P) (evalNL q (ruleOf q P) alpha H) []

theorem ev_evalNL {q : ℕ} (hq0 : 0 < q) {P : List ℕ} (hv : validP P = true) (Y A : List ℕ) :
    FiniteFields.ev q P (evalNL q (ruleOf q P) Y A) = evL (FiniteFields.ev q P Y) A :=
  evL_evalNL (isModel_root hq0 hv) Y A

theorem iotaOK_eval₂ {q : ℕ} (hq0 : 0 < q) {H P alpha : List ℕ} (h : iotaOK q H P alpha = true) :
    (toPoly q H).eval₂ (algebraMap (ZMod q) (AdjoinRoot (toPoly q P))) (FiniteFields.ev q P alpha) = 0 := by
  simp only [iotaOK, Bool.and_eq_true] at h
  have := ev_eq_of_eqL hq0 h.1 _ _ h.2
  rw [ev_evalNL hq0 h.1] at this
  rw [← aeval_def, aeval_toPoly, this, ev_nil]

/-- The embedding `F_q[x]/(H) → F_q[z]/(P)`, `x ↦ α = ev alpha`. -/
noncomputable def iotaG (q : ℕ) (hq0 : 0 < q) (H P alpha : List ℕ) (h : iotaOK q H P alpha = true) :
    AdjoinRoot (toPoly q H) →+* AdjoinRoot (toPoly q P) :=
  AdjoinRoot.lift _ _ (iotaOK_eval₂ hq0 h)

theorem iotaG_root (q : ℕ) (hq0 : 0 < q) (H P alpha : List ℕ) (h : iotaOK q H P alpha = true) :
    iotaG q hq0 H P alpha h (AdjoinRoot.root (toPoly q H)) = FiniteFields.ev q P alpha :=
  AdjoinRoot.lift_root _

theorem iotaG_ev (q : ℕ) (hq0 : 0 < q) (H P alpha : List ℕ) (h : iotaOK q H P alpha = true) (A : List ℕ) :
    iotaG q hq0 H P alpha h (FiniteFields.ev q H A) = FiniteFields.ev q P (evalNL q (ruleOf q P) alpha A) := by
  have hv : validP P = true := by simp only [iotaOK, Bool.and_eq_true] at h; exact h.1
  rw [FiniteFields.ev, map_evL, iotaG_root, ev_evalNL hq0 hv]

/-- `E = 80000 (y - β) (25y³ + 20y² + 14y + 14)³`. -/
def EvF {K : Type*} [CommRing K] (β y : K) : K := 80000 * (y - β) * (25 * y ^ 3 + 20 * y ^ 2 + 14 * y + 14) ^ 3

/-- The list computation of `E` at `ι(root list r)` in `F_q[z]/(P)`. -/
def eList (q : ℕ) (P alpha beta r : List ℕ) : List ℕ :=
  smulL q 80000 (mulL q (ruleOf q P) (subL q (evalNL q (ruleOf q P) alpha r) beta)
    (powL q (ruleOf q P) (evalNL q (ruleOf q P) (evalNL q (ruleOf q P) alpha r) [14, 14, 20, 25]) 3))

theorem ev_eList (q : ℕ) (hq0 : 0 < q) (H P alpha beta : List ℕ) (h : iotaOK q H P alpha = true) (A : List ℕ) :
    FiniteFields.ev q P (eList q P alpha beta A) = EvF (FiniteFields.ev q P beta) (iotaG q hq0 H P alpha h (FiniteFields.ev q H A)) := by
  have hv : validP P = true := by simp only [iotaOK, Bool.and_eq_true] at h; exact h.1
  have hM := isModel_root hq0 hv
  rw [iotaG_ev, eList, ev_smulL hq0 hv, ev_mulL hq0 hv _ _ (by
    rw [← length_ruleOf q P]; exact length_powL hM.fpos _ _), ev_powL hq0 hv, ev_evalNL hq0 hv]
  rw [show FiniteFields.ev q P (subL q (evalNL q (ruleOf q P) alpha A) beta) =
    FiniteFields.ev q P (evalNL q (ruleOf q P) alpha A) - FiniteFields.ev q P beta from evL_subL hM.qpos hM.char _ _]
  simp only [EvF, evL_cons, evL_nil]
  push_cast
  ring

/-- The fifth-power symbol of `F_q[z]/(P)` with respect to `ζ` (as `FFModel.sym`). -/
noncomputable def symG (q : ℕ) [Fact q.Prime] (P : List ℕ) [Fact (Irreducible (toPoly q P))] (zeta : ℕ)
    (x : AdjoinRoot (toPoly q P)) : ZMod 5 :=
  symK ((zeta : ℕ) : AdjoinRoot (toPoly q P)) ((q ^ (P.length - 1) - 1) / 5) x

theorem symG_of_symCheck (q : ℕ) [hq : Fact q.Prime] (P : List ℕ) [hP : Fact (Irreducible (toPoly q P))]
    (zeta : ℕ) (hff : ffCheck q P zeta = true) (A : List ℕ) (s : ℕ) (h : symCheck q P zeta A s = true) :
    FiniteFields.ev q P A ≠ 0 ∧ symG q P zeta (FiniteFields.ev q P A) = s :=
  FFModel.sym_of_symCheck ⟨q, P, zeta, hq.out, hP.out, hff⟩ A s h

end X2Y5Z7.SymbolSets
