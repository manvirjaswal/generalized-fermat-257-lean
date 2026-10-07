module

public import X2Y5Z7.SymbolSets.Basic
public import Mathlib.Data.List.GetD

@[expose] public section

/-! # Proposition 5.3: the certificate checker and its soundness

`Data` describes the residue-field models at one prime `q`: the `r` primes of `L8` (`k_i = F_q[x]/(H i)`), the `m`
primes of `L24` (`K_k = F_q[z]/(P k)`, above `If k`, with the images `alpha k`, `beta k` of `a`, `b` and the
fifth root of unity `zeta`). For `η = e ∈ {2, …, q-1}` a certificate (`Cert`) is one of

* `R rs`: distinct roots of `f̄ₘ = f̄/100` in `F_q`, more than there are degree-one primes;
* `G d g A B`: `A f̄ₘ + B (X^(q^d) mod f̄ₘ - X) = g ≠ 0` with `length g ≤ ∑_{d_i ∣ d} d_i`;
* `F phis cands`: `f̄ₘ = ∏ φ` with Rabin certificates for the `φ`, and for each prime `i` of `L8` the candidates
  `(j, [(root, syms)])`: all the roots of `φ_j` in `k_i` (for every `j` with `deg φ_j = d_i`), and for each root the
  symbols at the primes of `L24` above `i`. The checker enumerates all injective choices (`combo`) and tests that the
  resulting symbol vector is in `ILN`.

`main`: if all certificates check, then for every `η ∉ {0, 1}` and every admissible family `t i ∈ k_i` (roots of
`fb η`, `deg minpoly (t i) = d_i`, distinct minimal polynomials), the symbol vector of
`E_k = 80000 (ι_k t - β_k) ψ(ι_k t)³` (`EvD`) is in the list `Ilist`, and all `E_k ≠ 0`. -/

namespace X2Y5Z7.SymbolSets

open Polynomial X2Y5Z7.FiniteFields

/-- The residue-field data at one prime `q`. -/
structure Data (r m : ℕ) where
  zeta : ℕ
  H : Fin r → List ℕ
  P : Fin m → List ℕ
  If : Fin m → Fin r
  alpha : Fin m → List ℕ
  beta : Fin m → List ℕ

/-- The residue degree `d_i = deg H i`. -/
def Data.d {r m : ℕ} (D : Data r m) (i : Fin r) : ℕ := (D.H i).length - 1

/-- The data checks: all `H i` valid, and for each `k`: `ffCheck` and `H (If k) (α_k) = 0`. -/
def dataCheck (q : ℕ) {r m : ℕ} (D : Data r m) : Bool :=
  (List.finRange r).all (fun i => validP (D.H i)) &&
    (List.finRange m).all (fun k => ffCheck q (D.P k) D.zeta && iotaOK q (D.H (D.If k)) (D.P k) (D.alpha k))

/-- A candidate `(j, root, syms)`. -/
abbrev Cand := ℕ × List ℕ × List ℕ

/-- The certificate for one `η`. -/
inductive Cert
  | R (roots : List ℕ)
  | G (d : ℕ) (g A B : List ℕ)
  | F (phis : List (List ℕ × List (ℕ × List ℕ))) (cands : List (List (ℕ × List (List ℕ × List ℕ))))

/-- `f̄ = 100t⁸ + 80t⁷ + 56t⁶ + 56t⁵ - 4et + e` (constant first). -/
def fbL (q e : ℕ) : List ℕ := [e, (q - 4) * e, 0, 0, 0, 56, 56, 80, 100]

/-- `f̄ₘ = f̄ / 100`. -/
def fbmL (q e : ℕ) : List ℕ := smulL q (100 ^ (q - 2) % q) (fbL q e)

def degSumDvd {r m : ℕ} (D : Data r m) (dd : ℕ) : ℕ := ((List.finRange r).map fun i => if D.d i ∣ dd then D.d i else 0).sum

def deg1Count {r m : ℕ} (D : Data r m) : ℕ := ((List.finRange r).map fun i => if D.d i = 1 then 1 else 0).sum

def degTotal {r m : ℕ} (D : Data r m) : ℕ := ((List.finRange r).map fun i => D.d i).sum

def rCheck (q : ℕ) {r m : ℕ} (D : Data r m) (FM rs : List ℕ) : Bool :=
  decide rs.Nodup && rs.all (fun c => decide (c < q) && hornerN q c FM == 0) &&
    degTotal D == FM.length - 1 && decide (deg1Count D < rs.length)

def gCheck (q : ℕ) {r m : ℕ} (D : Data r m) (FM : List ℕ) (dd : ℕ) (g A B : List ℕ) : Bool :=
  !isZeroL q g && decide (g.length ≤ degSumDvd D dd) &&
    peqL q (addL q (pmulL q A FM) (pmulL q B (subL q (powL q (ruleOf q FM) [0, 1] (q ^ dd)) [0, 1]))) g

/-- All pairs satisfy `f`. -/
def allPairs {α : Type*} (f : α → α → Bool) : List α → Bool
  | [] => true
  | a :: l => l.all (f a) && allPairs f l

/-- The candidates `(j, root, syms)` of one prime of `L8`. -/
def flat (L : List (ℕ × List (List ℕ × List ℕ))) : List Cand :=
  L.flatMap (fun c => c.2.map (fun x => (c.1, x.1, x.2)))

/-- One candidate factor `c = (j, [(root, syms)])` at the prime `i` of `L8`: `j` is a factor index, the roots are
`deg φ_j` distinct roots of `φ_j` in `k_i`, and the symbols are right at the primes of `L24` above `i`. -/
def candCheck (q : ℕ) {r m : ℕ} (D : Data r m) (phis : List (List ℕ)) (i : Fin r) (c : ℕ × List (List ℕ × List ℕ)) : Bool :=
  decide (c.1 < phis.length) && c.2.length == (phis.getD c.1 []).length - 1 &&
    allPairs (fun a b => !eqL q (ruleOf q (D.H i)) a.1 b.1) c.2 &&
    c.2.all (fun x => eqL q (ruleOf q (D.H i)) (evalNL q (ruleOf q (D.H i)) x.1 (phis.getD c.1 [])) [] &&
      (List.finRange m).all (fun k => D.If k != i ||
        symCheck q (D.P k) D.zeta (eList q (D.P k) (D.alpha k) (D.beta k) x.1) (x.2.getD k 0)))

/-- Every factor of degree `d` has a candidate entry. -/
def complete (phis : List (List ℕ)) (d : ℕ) (L : List (ℕ × List (List ℕ × List ℕ))) : Bool :=
  (List.range phis.length).all (fun j => (phis.getD j []).length - 1 != d || L.any (fun c => c.1 == j))

/-- The symbol vector of a choice of candidates (one per prime of `L8`). -/
def vecOf {r m : ℕ} (D : Data r m) (cs : List Cand) : List ℕ :=
  (List.finRange m).map (fun k => (cs.getD (D.If k) (0, [], [])).2.2.getD k 0)

/-- Enumeration of all choices; the injective ones must give a vector in `ILN`. -/
def combo {r m : ℕ} (D : Data r m) (ILN : List (List ℕ)) : List (List Cand) → List Cand → Bool
  | [], acc => !decide ((acc.reverse.map Prod.fst).Nodup) || decide (vecOf D acc.reverse ∈ ILN)
  | L :: Ls, acc => L.all (fun c => combo D ILN Ls (c :: acc))

def fCheck (q : ℕ) {r m : ℕ} (D : Data r m) (ILN : List (List ℕ)) (FM : List ℕ) (phis : List (List ℕ × List (ℕ × List ℕ)))
    (cands : List (List (ℕ × List (List ℕ × List ℕ)))) : Bool :=
  phis.all (fun p => irrCheck q p.1 p.2) && peqL q (prodL q (phis.map Prod.fst)) FM &&
    (List.finRange r).all (fun i => complete (phis.map Prod.fst) (D.d i) (cands.getD i []) &&
      (cands.getD i []).all (candCheck q D (phis.map Prod.fst) i)) &&
    combo D ILN ((List.finRange r).map (fun i : Fin r => flat (cands.getD i.val []))) []

/-- The check of the certificate for `η = e`. -/
def certCheck (q : ℕ) {r m : ℕ} (D : Data r m) (ILN : List (List ℕ)) (e : ℕ) : Cert → Bool
  | .R rs => decide (5 < q) && 100 * (100 ^ (q - 2) % q) % q == 1 && validP (fbmL q e) && rCheck q D (fbmL q e) rs
  | .G dd g A B => decide (5 < q) && 100 * (100 ^ (q - 2) % q) % q == 1 && validP (fbmL q e) &&
      gCheck q D (fbmL q e) dd g A B
  | .F phis cands => decide (5 < q) && 100 * (100 ^ (q - 2) % q) % q == 1 && validP (fbmL q e) &&
      fCheck q D ILN (fbmL q e) phis cands

/-- `ILN` (vectors as lists) is contained in `Ilist`. -/
def ilCheck (m : ℕ) (ILN : List (List ℕ)) (Ilist : List (Fin m → ZMod 5)) : Bool :=
  ILN.all (fun v => Ilist.any (fun w => (List.finRange m).all fun k => decide (w k = ((v.getD k 0 : ℕ) : ZMod 5))))

/-! ## Soundness of the pieces -/

/-- `fb η t = 100t⁸ + 80t⁷ + 56t⁶ + 56t⁵ - 4ηt + η`. -/
def fb {q : ℕ} {K : Type*} [CommRing K] [Algebra (ZMod q) K] (η : ZMod q) (t : K) : K :=
  100 * t ^ 8 + 80 * t ^ 7 + 56 * t ^ 6 + 56 * t ^ 5 - 4 * algebraMap (ZMod q) K η * t + algebraMap (ZMod q) K η

theorem evL_fbmL {q : ℕ} {K : Type*} [CommRing K] [Algebra (ZMod q) K] (h5 : 5 < q)
    (hinv : 100 * (100 ^ (q - 2) % q) % q = 1) (e : ℕ) (t : K) (ht : fb (e : ZMod q) t = 0) :
    evL t (fbmL q e) = 0 := by
  have hq : ((q : ℕ) : K) = 0 := by
    rw [← map_natCast (algebraMap (ZMod q) K), ZMod.natCast_self, map_zero]
  have h100 : ((100 : ℕ) : K) * ((100 ^ (q - 2) % q : ℕ) : K) = 1 := by
    rw [← Nat.cast_mul, ← natCast_mod hq, hinv, Nat.cast_one]
  have hfb : evL t (fbL q e) = fb (e : ZMod q) t := by
    simp only [fbL, fb, evL_cons, evL_nil, map_natCast]
    rw [Nat.cast_mul, Nat.cast_sub (by omega), hq]
    push_cast; ring
  rw [fbmL, evL_smulL hq, hfb, ht, mul_zero]

theorem pairwise_of_allPairs {α : Type*} (f : α → α → Bool) :
    ∀ l : List α, allPairs f l = true → l.Pairwise (fun a b => f a b = true)
  | [] => fun _ => List.Pairwise.nil
  | a :: l => fun h => by
    simp only [allPairs, Bool.and_eq_true, List.all_eq_true] at h
    exact List.Pairwise.cons h.1 (pairwise_of_allPairs f l h.2)

theorem combo_sound {r m : ℕ} (D : Data r m) (ILN : List (List ℕ)) : ∀ (Ls : List (List Cand)) (acc : List Cand),
    combo D ILN Ls acc = true → ∀ cs : List Cand, List.Forall₂ (· ∈ ·) cs Ls →
    ((acc.reverse ++ cs).map Prod.fst).Nodup → vecOf D (acc.reverse ++ cs) ∈ ILN
  | [], acc, h, cs, hcs, hnd => by
    rw [List.forall₂_nil_right_iff.mp hcs, List.append_nil] at hnd ⊢
    simp only [combo, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at h
    exact h.resolve_left (not_not.mpr hnd)
  | L :: Ls, acc, h, cs, hcs, hnd => by
    obtain ⟨c, cs', hc, hcs', rfl⟩ := List.forall₂_cons_right_iff.mp hcs
    simp only [combo, List.all_eq_true] at h
    have := combo_sound D ILN Ls (c :: acc) (h c hc) cs' hcs' (by simpa using hnd)
    simpa using this

theorem forall₂_ofFn {α : Type*} : ∀ {n : ℕ} (f : Fin n → α) (g : Fin n → List α), (∀ i, f i ∈ g i) →
    List.Forall₂ (· ∈ ·) (List.ofFn f) (List.ofFn g)
  | 0, _, _, _ => by simp
  | n + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ]
    exact List.Forall₂.cons (h 0) (forall₂_ofFn _ _ fun i => h i.succ)

theorem sum_finRange {n : ℕ} (f : Fin n → ℕ) : ((List.finRange n).map f).sum = ∑ i, f i :=
  (Fin.sum_univ_def f).symm

/-! ## The main soundness theorem -/

section Main

variable (q : ℕ) [hq : Fact q.Prime] {r m : ℕ} (D : Data r m) [hH : ∀ i, Fact (Irreducible (toPoly q (D.H i)))]
  [hP : ∀ k, Fact (Irreducible (toPoly q (D.P k)))]

omit hq hH hP in
theorem iotaOK_of_dataCheck (hD : dataCheck q D = true) (k : Fin m) :
    iotaOK q (D.H (D.If k)) (D.P k) (D.alpha k) = true := by
  simp only [dataCheck, Bool.and_eq_true, List.all_eq_true] at hD
  exact (hD.2 k (List.mem_finRange k)).2

omit hq hH hP in
theorem ffCheck_of_dataCheck (hD : dataCheck q D = true) (k : Fin m) : ffCheck q (D.P k) D.zeta = true := by
  simp only [dataCheck, Bool.and_eq_true, List.all_eq_true] at hD
  exact (hD.2 k (List.mem_finRange k)).1

omit hq hH hP in
theorem validH_of_dataCheck (hD : dataCheck q D = true) (i : Fin r) : validP (D.H i) = true := by
  simp only [dataCheck, Bool.and_eq_true, List.all_eq_true] at hD
  exact hD.1 i (List.mem_finRange i)

/-- The embedding `ι_k : k_{If k} → K_k`. -/
noncomputable def iotaD (hD : dataCheck q D = true) (k : Fin m) :
    AdjoinRoot (toPoly q (D.H (D.If k))) →+* AdjoinRoot (toPoly q (D.P k)) :=
  iotaG q hq.out.pos _ _ _ (iotaOK_of_dataCheck q D hD k)

theorem iotaD_root (hD : dataCheck q D = true) (k : Fin m) :
    iotaD q D hD k (AdjoinRoot.root (toPoly q (D.H (D.If k)))) = FiniteFields.ev q (D.P k) (D.alpha k) :=
  iotaG_root _ _ _ _ _ _

/-- `E_k(t) = 80000 (ι_k t - β_k) ψ(ι_k t)³`. -/
noncomputable def EvD (hD : dataCheck q D = true) (k : Fin m) (t : AdjoinRoot (toPoly q (D.H (D.If k)))) :
    AdjoinRoot (toPoly q (D.P k)) :=
  EvF (FiniteFields.ev q (D.P k) (D.beta k)) (iotaD q D hD k t)

omit hP in
/-- The consequences of a candidate check at the prime `i`: if `t` is a root of `φ_j`, it is one of the listed
roots, whose symbols are the listed ones. -/
theorem cand_sound (hD : dataCheck q D = true) (phis : List (List ℕ)) (hvφ : ∀ φ ∈ phis, validP φ = true)
    (i : Fin r) (c : ℕ × List (List ℕ × List ℕ)) (hc : candCheck q D phis i c = true)
    (t : AdjoinRoot (toPoly q (D.H i))) (ht : aeval t (toPoly q (phis.getD c.1 [])) = 0) :
    ∃ x ∈ c.2, t = FiniteFields.ev q (D.H i) x.1 ∧ ∀ k, (hk : D.If k = i) →
      symCheck q (D.P k) D.zeta (eList q (D.P k) (D.alpha k) (D.beta k) x.1) (x.2.getD k 0) = true := by
  have hq0 := hq.out.pos
  have hvH := validH_of_dataCheck q D hD i
  simp only [candCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨hj, hlen⟩, hpairs⟩, hroots⟩ := hc
  have hφv : validP (phis.getD c.1 []) = true := by
    rw [List.getD_eq_getElem _ _ hj]; exact hvφ _ (List.getElem_mem hj)
  obtain ⟨hmon, hdeg⟩ := toPoly_monic (q := q) hφv
  have hmem := mem_of_roots (q := q) hmon.ne_zero (c.2.map fun x => FiniteFields.ev q (D.H i) x.1) ?_ ?_ ?_ ht
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hmem
    refine ⟨x, hx, rfl, fun k hk => ?_⟩
    have := ((hroots x hx).2 k (List.mem_finRange k))
    simpa [hk] using this
  · refine (pairwise_of_allPairs _ _ hpairs).map _ fun a b hab => ?_
    simp only [Bool.not_eq_true'] at hab
    exact ev_ne_of_eqL hvH _ _ hab
  · rw [List.length_map, hlen, hdeg]; simp
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    have := ev_eq_of_eqL hq0 hvH _ _ (hroots x hx).1
    rwa [ev_evalNL hq0 hvH, ev_nil, ← aeval_toPoly (q := q)] at this

/-- The symbol of `E_k` at a listed root. -/
theorem sym_sound (hD : dataCheck q D = true) (k : Fin m) (A : List ℕ) (s : ℕ)
    (h : symCheck q (D.P k) D.zeta (eList q (D.P k) (D.alpha k) (D.beta k) A) s = true) :
    EvD q D hD k (FiniteFields.ev q (D.H (D.If k)) A) ≠ 0 ∧
      symG q (D.P k) D.zeta (EvD q D hD k (FiniteFields.ev q (D.H (D.If k)) A)) = s := by
  have := symG_of_symCheck q (D.P k) D.zeta (ffCheck_of_dataCheck q D hD k) _ s h
  rwa [ev_eList q hq.out.pos (D.H (D.If k)) (D.P k) (D.alpha k) (D.beta k) (iotaOK_of_dataCheck q D hD k)] at this

/-- **Soundness of the certificates (Proposition 5.3 at one prime `q`).** -/
theorem main (hD : dataCheck q D = true) (ILN : List (List ℕ)) (Ilist : List (Fin m → ZMod 5))
    (hIL : ilCheck m ILN Ilist = true) (certs : List (ℕ × Cert))
    (hc : certs.all (fun p => certCheck q D ILN p.1 p.2) = true) (hcov : ∀ e, 2 ≤ e → e < q → e ∈ certs.map Prod.fst)
    (η : ZMod q) (h0 : η ≠ 0) (h1 : η ≠ 1) (t : ∀ i, AdjoinRoot (toPoly q (D.H i))) (hr : ∀ i, fb η (t i) = 0)
    (hd : ∀ i, (minpoly (ZMod q) (t i)).natDegree = D.d i)
    (hdist : ∀ i j, i ≠ j → D.d i = D.d j → minpoly (ZMod q) (t i) ≠ minpoly (ZMod q) (t j)) :
    (∀ k, EvD q D hD k (t (D.If k)) ≠ 0) ∧
      ∃ w ∈ Ilist, w = fun k => symG q (D.P k) D.zeta (EvD q D hD k (t (D.If k))) := by
  classical
  have hq0 := hq.out.pos
  -- the certificate for `e = η.val`
  set e := η.val with he
  have hηe : η = (e : ZMod q) := (ZMod.natCast_zmod_val η).symm
  have he2 : 2 ≤ e := by
    by_contra hlt
    interval_cases h : e
    · exact h0 (by rw [hηe]; simp)
    · exact h1 (by rw [hηe]; simp)
  obtain ⟨⟨e', cert⟩, hmemc, he'⟩ := List.mem_map.mp (hcov e he2 (ZMod.val_lt η))
  simp only at he'
  subst he'
  have hcc : certCheck q D ILN e cert = true := by
    simp only [List.all_eq_true] at hc; exact hc _ hmemc
  -- the minimal polynomials
  set mm : Fin r → (ZMod q)[X] := fun i => minpoly (ZMod q) (t i) with hmm
  have hint : ∀ i, IsIntegral (ZMod q) (t i) := fun i => by
    have : Module.Finite (ZMod q) (AdjoinRoot (toPoly q (D.H i))) :=
      (AdjoinRoot.powerBasis (hH i).out.ne_zero).finite
    exact IsIntegral.of_finite (ZMod q) (t i)
  have hirr : ∀ i, Irreducible (mm i) := fun i => minpoly.irreducible (hint i)
  have hmon : ∀ i, (mm i).Monic := fun i => minpoly.monic (hint i)
  have hinj : Function.Injective mm := by
    intro i j hij
    by_contra hne
    have hdd : D.d i = D.d j := by rw [← hd i, ← hd j]; exact congrArg natDegree hij
    exact hdist i j hne hdd hij
  have hdegm : ∀ i, (mm i).natDegree = D.d i := hd
  -- common checks
  have hcommon : 5 < q ∧ 100 * (100 ^ (q - 2) % q) % q = 1 ∧ validP (fbmL q e) = true := by
    cases cert <;> simp only [certCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcc <;>
      exact ⟨hcc.1.1.1, hcc.1.1.2, hcc.1.2⟩
  obtain ⟨h5, hinv, hvF⟩ := hcommon
  have hdvd : ∀ i, mm i ∣ toPoly q (fbmL q e) := fun i => by
    apply minpoly.dvd
    rw [aeval_toPoly]
    exact evL_fbmL h5 hinv e (t i) (hηe ▸ hr i)
  cases cert with
  | R rs =>
    exfalso
    simp only [certCheck, rCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hcc
    obtain ⟨-, ⟨⟨hnd, hrs⟩, htot⟩, hcount⟩ := hcc
    have hb := r_bound mm hirr hmon hinj hvF hdvd (by
      rw [← htot, degTotal, sum_finRange]; exact Finset.sum_congr rfl fun i _ => hdegm i) rs hnd
      (fun c hc => (hrs c hc).1) (fun c hc => by rw [← hornerN_eq, (hrs c hc).2, Nat.cast_zero])
    have : (Finset.univ.filter (fun i => (mm i).natDegree = 1)).card = deg1Count D := by
      rw [deg1Count, sum_finRange, Finset.card_filter]
      exact Finset.sum_congr rfl fun i _ => by rw [hdegm]
    omega
  | G dd g A B =>
    exfalso
    simp only [certCheck, gCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hcc
    obtain ⟨-, ⟨hg0, hglen⟩, hid⟩ := hcc
    have hid' := toPoly_eq_of_peqL hq0 hid
    rw [toPoly_addL, toPoly_pmulL, toPoly_pmulL, toPoly_subL hq0, toPoly_X] at hid'
    have hb := g_bound mm hirr hmon hinj hvF dd hdvd hid' (toPoly_ne_zero hg0)
    have : ∑ i ∈ Finset.univ.filter (fun i => (mm i).natDegree ∣ dd), (mm i).natDegree = degSumDvd D dd := by
      rw [degSumDvd, sum_finRange, Finset.sum_filter]
      exact Finset.sum_congr rfl fun i _ => by rw [hdegm]
    omega
  | F phis cands =>
    simp only [certCheck, fCheck, Bool.and_eq_true, List.all_eq_true] at hcc
    obtain ⟨-, ⟨⟨hirrφ, hprod⟩, hcands⟩, hcombo⟩ := hcc
    set phis' := phis.map Prod.fst with hphis'
    have hvφ : ∀ φ ∈ phis', validP φ = true := by
      intro φ hφ
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hφ
      have := hirrφ p hp
      simp only [irrCheck, Bool.and_eq_true] at this
      exact this.1.1.1
    have hirrφ' : ∀ φ ∈ phis', Irreducible (toPoly q φ) := by
      intro φ hφ
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hφ
      exact irreducible_of_irrCheck (hirrφ p hp)
    have hprod' : toPoly q (fbmL q e) = (phis'.map (toPoly q)).prod := by
      rw [← toPoly_prodL]; exact (toPoly_eq_of_peqL hq0 hprod).symm
    -- the choice of a candidate for each prime of `L8`
    have hchoice : ∀ i : Fin r, ∃ ct : Cand, ct ∈ flat (cands.getD i []) ∧ mm i = toPoly q (phis'.getD ct.1 []) ∧
        t i = FiniteFields.ev q (D.H i) ct.2.1 ∧ ∀ k, (hk : D.If k = i) →
          symCheck q (D.P k) D.zeta (eList q (D.P k) (D.alpha k) (D.beta k) ct.2.1) (ct.2.2.getD k 0) = true := by
      intro i
      obtain ⟨j, hj, hmj⟩ := f_match mm hirr hmon phis' hvφ hirrφ' hprod' hdvd i
      obtain ⟨hcomp, hcc⟩ := hcands i (List.mem_finRange i)
      have hφv := hvφ _ (List.getElem_mem hj)
      have hdj : (phis'[j]).length - 1 = D.d i := by
        rw [← hdegm i, hmj, (toPoly_monic hφv).2]; simp
      simp only [complete, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq,
        List.any_eq_true, beq_iff_eq] at hcomp
      obtain ⟨c, hc, hcj⟩ := (hcomp j hj).resolve_left (by rw [List.getD_eq_getElem _ _ hj]; exact not_not.mpr hdj)
      have hroot : aeval (t i) (toPoly q (phis'.getD c.1 [])) = 0 := by
        rw [hcj, List.getD_eq_getElem _ _ hj, ← hmj]; exact minpoly.aeval _ _
      obtain ⟨x, hx, htx, hsym⟩ := cand_sound q D hD phis' hvφ i c (hcc c hc) (t i) hroot
      refine ⟨(c.1, x.1, x.2), ?_, ?_, htx, hsym⟩
      · simp only [flat, List.mem_flatMap, List.mem_map]; exact ⟨c, hc, x, hx, rfl⟩
      · simp only; rw [hcj, List.getD_eq_getElem _ _ hj]; exact hmj
    choose C hCmem hCm hCt hCsym using hchoice
    have hCinj : Function.Injective (fun i => (C i).1) := by
      intro i i' h
      apply hinj
      have h' : (C i).1 = (C i').1 := h
      rw [hCm i, hCm i', h']
    have hcs := combo_sound D ILN _ [] hcombo (List.ofFn C)
      (by rw [← List.ofFn_eq_map]; exact forall₂_ofFn _ _ hCmem)
      (by simp only [List.reverse_nil, List.nil_append, List.map_ofFn]; exact List.nodup_ofFn.mpr hCinj)
    simp only [List.reverse_nil, List.nil_append] at hcs
    have hvec : ∀ k : Fin m, (vecOf D (List.ofFn C)).getD k 0 = (C (D.If k)).2.2.getD k 0 := by
      intro k
      simp [vecOf]
    have hsymk : ∀ k, EvD q D hD k (t (D.If k)) ≠ 0 ∧
        symG q (D.P k) D.zeta (EvD q D hD k (t (D.If k))) = (((C (D.If k)).2.2.getD k 0 : ℕ) : ZMod 5) := by
      intro k
      rw [hCt (D.If k)]
      exact sym_sound q D hD k _ _ (hCsym (D.If k) k rfl)
    refine ⟨fun k => (hsymk k).1, ?_⟩
    simp only [ilCheck, List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at hIL
    obtain ⟨w, hw, hwk⟩ := hIL _ hcs
    refine ⟨w, hw, funext fun k => ?_⟩
    rw [hwk k (List.mem_finRange k), hvec k, (hsymk k).2]

end Main

end X2Y5Z7.SymbolSets
