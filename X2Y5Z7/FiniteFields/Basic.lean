import X2Y5Z7.Arith.Poly
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Field.ZMod

/-! # Explicit finite fields: list arithmetic modulo `(q, P)`

An element of `F_q[z]/(P)` is a list `A : List ℕ` of coefficients (constant first), standing for `Σ Aᵢ zⁱ`.
`P` is monic of degree `f`, written `P = P' ++ [1]`; the reduction rule is `z^f = Σ Nᵢ zⁱ` with `N = -P' mod q`
(`ruleOf q P`). All operations are structural recursions on lists of natural numbers, reduced `% q`, so the kernel
evaluates them (`decide +kernel`).

Soundness is proved in any commutative ring `R` with an element `x` such that `(q : R) = 0` and `x ^ f = evL x N`
(`IsModel`), where `evL x A = Σ Aᵢ xⁱ`. The main instance is `AdjoinRoot (toPoly q P)` with its root (`isModel_root`).

* `addL`, `smulL`, `negL`, `subL`, `mulXL`, `mulL`, `reduceL`, `powL`, `evalP1L`, `evalP2L`, `eqL`.
* `evL_mulL`, `evL_powL`, `evL_evalP1L` (`= P1.eval`), `evL_evalP2L` (`= P2.eval`), `evL_eq_of_eqL`.
* `toPoly q A : (ZMod q)[X]`, `ev q P A : AdjoinRoot (toPoly q P)`, and the decision lemmas `ev_eq_of_eqL`,
  `ev_ne_of_eqL` (for prime `q` and monic `P` of positive degree; the power-basis argument is a degree count). -/

namespace X2Y5Z7.FiniteFields

open Polynomial

/-! ## List operations -/

/-- `Σ Aᵢ xⁱ` (Horner). -/
def evL {R : Type*} [CommRing R] (x : R) : List ℕ → R
  | [] => 0
  | c :: cs => (c : R) + x * evL x cs

def addL (q : ℕ) : List ℕ → List ℕ → List ℕ
  | [], B => B
  | a :: A, [] => a :: A
  | a :: A, b :: B => (a + b) % q :: addL q A B

def smulL (q c : ℕ) (A : List ℕ) : List ℕ := A.map (fun a => c * a % q)

def negL (q : ℕ) (A : List ℕ) : List ℕ := A.map (fun a => (q - a % q) % q)

def subL (q : ℕ) (A B : List ℕ) : List ℕ := addL q A (negL q B)

/-- Multiplication by `x`, for `A` of length at most `f = N.length`. -/
def mulXL (q : ℕ) (N A : List ℕ) : List ℕ :=
  addL q (0 :: A.take (N.length - 1)) (smulL q (A.getD (N.length - 1) 0) N)

/-- `A · B`, Horner over `A`; `B` must have length at most `f`. The result has length at most `f`. -/
def mulL (q : ℕ) (N : List ℕ) : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | a :: A, B => addL q (smulL q a B) (mulXL q N (mulL q N A B))

/-- Reduction to length at most `f`. -/
def reduceL (q : ℕ) (N A : List ℕ) : List ℕ := mulL q N A [1]

/-- `B ^ n`, naive. -/
def powNaive (q : ℕ) (N B : List ℕ) : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => mulL q N B (powNaive q N B n)

/-- `acc · B ^ n` by binary exponentiation; `B`, `acc` of length at most `f`. -/
def powAux (q : ℕ) (N : List ℕ) : ℕ → List ℕ → ℕ → List ℕ → List ℕ
  | 0, B, n, acc => mulL q N (powNaive q N B n) acc
  | fuel + 1, B, n, acc =>
    if n = 0 then acc
    else powAux q N fuel (mulL q N B B) (n / 2) (if n % 2 = 1 then mulL q N B acc else acc)

/-- `B ^ n`. -/
def powL (q : ℕ) (N B : List ℕ) (n : ℕ) : List ℕ := powAux q N 64 (reduceL q N B) n [1]

/-- The residue of an integer, as a natural number below `q`. -/
def intMod (q : ℕ) (c : ℤ) : ℕ := (c % (q : ℤ)).toNat

/-- `p(Y)` for an integer polynomial `p` (Horner). -/
def evalP1L (q : ℕ) (N Y : List ℕ) : P1 → List ℕ
  | [] => []
  | c :: cs => addL q [intMod q c] (mulL q N Y (evalP1L q N Y cs))

/-- `F(X, Y)` for a bivariate integer polynomial `F` (Horner in `Y`). -/
def evalP2L (q : ℕ) (N X Y : List ℕ) : P2 → List ℕ
  | [] => []
  | r :: F => addL q (evalP1L q N X r) (mulL q N Y (evalP2L q N X Y F))

/-- All coefficients vanish mod `q`. -/
def isZeroL (q : ℕ) (A : List ℕ) : Bool := A.all (fun a => a % q == 0)

/-- Equality test: the reduced difference vanishes. -/
def eqL (q : ℕ) (N A B : List ℕ) : Bool := isZeroL q (reduceL q N (subL q A B))

/-- The reduction rule of a monic `P = P' ++ [1]`: `z^f = -P'(z)`. -/
def ruleOf (q : ℕ) (P : List ℕ) : List ℕ := negL q P.dropLast

/-! ## Soundness in a model -/

/-- `x` satisfies the reduction rule `x^f = N(x)` in a ring of characteristic dividing `q`. -/
structure IsModel {R : Type*} [CommRing R] (q : ℕ) (N : List ℕ) (x : R) : Prop where
  qpos : 0 < q
  fpos : 0 < N.length
  char : (q : R) = 0
  rule : x ^ N.length = evL x N

section Model

variable {R : Type*} [CommRing R] {q : ℕ} {N : List ℕ} {x : R}

@[simp] theorem evL_nil : evL x [] = 0 := rfl
@[simp] theorem evL_cons (c : ℕ) (cs : List ℕ) : evL x (c :: cs) = (c : R) + x * evL x cs := rfl

theorem evL_append (A B : List ℕ) : evL x (A ++ B) = evL x A + x ^ A.length * evL x B := by
  induction A with
  | nil => simp
  | cons a A ih => simp [ih]; ring

theorem natCast_mod (hq : (q : R) = 0) (a : ℕ) : ((a % q : ℕ) : R) = a := by
  conv_rhs => rw [← Nat.mod_add_div a q]
  push_cast; rw [hq]; ring

theorem evL_addL (hq : (q : R) = 0) : ∀ A B : List ℕ, evL x (addL q A B) = evL x A + evL x B
  | [], B => by simp [addL]
  | a :: A, [] => by simp [addL]
  | a :: A, b :: B => by
    simp only [addL, evL_cons, natCast_mod hq, evL_addL hq A B, Nat.cast_add]; ring

theorem length_addL : ∀ A B : List ℕ, (addL q A B).length = max A.length B.length
  | [], B => by simp [addL]
  | a :: A, [] => by simp [addL]
  | a :: A, b :: B => by simp [addL, length_addL A B, Nat.succ_max_succ]

theorem evL_smulL (hq : (q : R) = 0) (c : ℕ) : ∀ A : List ℕ, evL x (smulL q c A) = c * evL x A
  | [] => by simp [smulL]
  | a :: A => by
    have := evL_smulL hq c A
    simp only [smulL, List.map_cons, evL_cons] at this ⊢
    rw [this, natCast_mod hq]; push_cast; ring

@[simp] theorem length_smulL (c : ℕ) (A : List ℕ) : (smulL q c A).length = A.length := by simp [smulL]

theorem evL_negL (hq0 : 0 < q) (hq : (q : R) = 0) : ∀ A : List ℕ, evL x (negL q A) = - evL x A
  | [] => by simp [negL]
  | a :: A => by
    have := evL_negL hq0 hq A
    simp only [negL, List.map_cons, evL_cons] at this ⊢
    rw [this, natCast_mod hq, Nat.cast_sub (Nat.mod_lt a hq0).le, natCast_mod hq, hq]; ring

@[simp] theorem length_negL (A : List ℕ) : (negL q A).length = A.length := by simp [negL]

theorem evL_subL (hq0 : 0 < q) (hq : (q : R) = 0) (A B : List ℕ) :
    evL x (subL q A B) = evL x A - evL x B := by
  rw [subL, evL_addL hq, evL_negL hq0 hq, sub_eq_add_neg]

/-- `evL` of a list of length at most one more than `n`, split at `n`. -/
theorem evL_take_getD (A : List ℕ) (n : ℕ) (hA : A.length ≤ n + 1) :
    evL x A = evL x (A.take n) + x ^ n * (A.getD n 0 : R) := by
  induction A generalizing n with
  | nil => simp
  | cons a A ih =>
    cases n with
    | zero =>
      obtain rfl : A = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hA; omega)
      simp
    | succ n =>
      simp only [List.length_cons] at hA
      rw [evL_cons, ih n (by omega), List.take_succ_cons, evL_cons, List.getD_cons_succ]; ring

theorem evL_mulXL (hM : IsModel q N x) (A : List ℕ) (hA : A.length ≤ N.length) :
    evL x (mulXL q N A) = x * evL x A := by
  obtain ⟨m, hm⟩ : ∃ m, N.length = m + 1 := ⟨N.length - 1, by have := hM.fpos; omega⟩
  have hrule := hM.rule
  rw [hm] at hrule hA
  simp only [mulXL, hm, Nat.add_sub_cancel]
  rw [evL_addL hM.char, evL_smulL hM.char, evL_cons, Nat.cast_zero, zero_add, evL_take_getD A m hA, ← hrule]
  ring

theorem length_mulXL (hf : 0 < N.length) (A : List ℕ) : (mulXL q N A).length ≤ N.length := by
  rw [mulXL, length_addL]
  simp only [List.length_cons, List.length_take, length_smulL]
  omega

theorem length_mulL (hf : 0 < N.length) : ∀ (A B : List ℕ), B.length ≤ N.length →
    (mulL q N A B).length ≤ N.length
  | [], B, _ => by simp [mulL]
  | a :: A, B, hB => by
    rw [mulL, length_addL, length_smulL]
    exact max_le hB (length_mulXL hf _)

theorem evL_mulL (hM : IsModel q N x) : ∀ (A B : List ℕ), B.length ≤ N.length →
    evL x (mulL q N A B) = evL x A * evL x B
  | [], B, _ => by simp [mulL]
  | a :: A, B, hB => by
    rw [mulL, evL_addL hM.char, evL_smulL hM.char, evL_mulXL hM _ (length_mulL hM.fpos A B hB),
      evL_mulL hM A B hB, evL_cons]; ring

theorem length_reduceL (hf : 0 < N.length) (A : List ℕ) : (reduceL q N A).length ≤ N.length :=
  length_mulL hf A [1] (by simp; omega)

theorem evL_reduceL (hM : IsModel q N x) (A : List ℕ) : evL x (reduceL q N A) = evL x A := by
  rw [reduceL, evL_mulL hM A [1] (by simp; exact hM.fpos)]; simp

theorem length_powNaive (hf : 0 < N.length) (B : List ℕ) : ∀ n, (powNaive q N B n).length ≤ N.length
  | 0 => by simp [powNaive]; omega
  | n + 1 => length_mulL hf _ _ (length_powNaive hf B n)

theorem evL_powNaive (hM : IsModel q N x) (B : List ℕ) : ∀ n, evL x (powNaive q N B n) = evL x B ^ n
  | 0 => by simp [powNaive]
  | n + 1 => by
    rw [powNaive, evL_mulL hM _ _ (length_powNaive hM.fpos B n), evL_powNaive hM B n]; ring

theorem length_powAux (hf : 0 < N.length) : ∀ (fuel : ℕ) (B : List ℕ) (n : ℕ) (acc : List ℕ),
    B.length ≤ N.length → acc.length ≤ N.length → (powAux q N fuel B n acc).length ≤ N.length
  | 0, B, n, acc, _, hacc => length_mulL hf _ _ hacc
  | fuel + 1, B, n, acc, hB, hacc => by
    rw [powAux]
    split_ifs
    · exact hacc
    · exact length_powAux hf fuel _ _ _ (length_mulL hf _ _ hB) (length_mulL hf _ _ hacc)
    · exact length_powAux hf fuel _ _ _ (length_mulL hf _ _ hB) hacc

theorem evL_powAux (hM : IsModel q N x) : ∀ (fuel : ℕ) (B : List ℕ) (n : ℕ) (acc : List ℕ),
    B.length ≤ N.length → acc.length ≤ N.length →
    evL x (powAux q N fuel B n acc) = evL x acc * evL x B ^ n
  | 0, B, n, acc, _, hacc => by
    rw [powAux, evL_mulL hM _ _ hacc, evL_powNaive hM]; ring
  | fuel + 1, B, n, acc, hB, hacc => by
    have hsq : evL x (mulL q N B B) = evL x B * evL x B := evL_mulL hM B B hB
    have hn : n = 2 * (n / 2) + n % 2 := (Nat.div_add_mod n 2).symm
    rw [powAux]
    split_ifs with h0 h1
    · subst h0; simp
    · rw [evL_powAux hM fuel _ _ _ (length_mulL hM.fpos _ _ hB) (length_mulL hM.fpos _ _ hacc), hsq,
        evL_mulL hM _ _ hacc]
      conv_rhs => rw [hn, h1]
      ring
    · have h2 : n % 2 = 0 := by omega
      rw [evL_powAux hM fuel _ _ _ (length_mulL hM.fpos _ _ hB) hacc, hsq]
      conv_rhs => rw [hn, h2]
      ring

theorem length_powL (hf : 0 < N.length) (B : List ℕ) (n : ℕ) : (powL q N B n).length ≤ N.length :=
  length_powAux hf _ _ _ _ (length_reduceL hf B) (by simp; omega)

theorem evL_powL (hM : IsModel q N x) (B : List ℕ) (n : ℕ) : evL x (powL q N B n) = evL x B ^ n := by
  rw [powL, evL_powAux hM _ _ _ _ (length_reduceL hM.fpos B) (by simp; exact hM.fpos), evL_reduceL hM]
  simp

theorem intCast_intMod (hq0 : 0 < q) (hq : (q : R) = 0) (c : ℤ) : ((intMod q c : ℕ) : R) = (c : R) := by
  have hnn : 0 ≤ c % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hq0.ne')
  rw [intMod, ← Int.cast_natCast, Int.toNat_of_nonneg hnn]
  rw [Int.emod_def]; push_cast; rw [hq]; ring

theorem length_evalP1L (hf : 0 < N.length) (Y : List ℕ) : ∀ p : P1, (evalP1L q N Y p).length ≤ N.length
  | [] => by simp [evalP1L]
  | c :: cs => by
    rw [evalP1L, length_addL]
    exact max_le (by simp; omega) (length_mulL hf _ _ (length_evalP1L hf Y cs))

theorem evL_evalP1L (hM : IsModel q N x) (Y : List ℕ) : ∀ p : P1,
    evL x (evalP1L q N Y p) = P1.eval (evL x Y) p
  | [] => by simp [evalP1L]
  | c :: cs => by
    rw [evalP1L, evL_addL hM.char, evL_mulL hM _ _ (length_evalP1L hM.fpos Y cs), evL_evalP1L hM Y cs,
      P1.eval_cons]
    simp [intCast_intMod hM.qpos hM.char]

theorem length_evalP2L (hf : 0 < N.length) (X Y : List ℕ) : ∀ F : P2,
    (evalP2L q N X Y F).length ≤ N.length
  | [] => by simp [evalP2L]
  | r :: F => by
    rw [evalP2L, length_addL]
    exact max_le (length_evalP1L hf X r) (length_mulL hf _ _ (length_evalP2L hf X Y F))

theorem evL_evalP2L (hM : IsModel q N x) (X Y : List ℕ) : ∀ F : P2,
    evL x (evalP2L q N X Y F) = P2.eval (evL x X) (evL x Y) F
  | [] => by simp [evalP2L]
  | r :: F => by
    rw [evalP2L, evL_addL hM.char, evL_mulL hM _ _ (length_evalP2L hM.fpos X Y F), evL_evalP1L hM,
      evL_evalP2L hM X Y F, P2.eval_cons]

theorem evL_eq_zero_of_isZeroL (hq : (q : R) = 0) : ∀ A : List ℕ, isZeroL q A = true → evL x A = 0
  | [], _ => rfl
  | a :: A, h => by
    simp only [isZeroL, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rw [evL_cons, ← natCast_mod hq a, h.1, evL_eq_zero_of_isZeroL hq A h.2]; simp

theorem evL_eq_of_eqL (hM : IsModel q N x) (A B : List ℕ) (h : eqL q N A B = true) : evL x A = evL x B := by
  have := evL_eq_zero_of_isZeroL (x := x) hM.char _ h
  rwa [evL_reduceL hM, evL_subL hM.qpos hM.char, sub_eq_zero] at this

end Model

/-! ## Polynomials and the model `AdjoinRoot (toPoly q P)` -/

/-- The polynomial `Σ Aᵢ Xⁱ` over `ZMod q`. -/
noncomputable def toPoly (q : ℕ) : List ℕ → (ZMod q)[X]
  | [] => 0
  | c :: cs => C (c : ZMod q) + X * toPoly q cs

theorem coeff_toPoly (q : ℕ) : ∀ (A : List ℕ) (n : ℕ), (toPoly q A).coeff n = (A.getD n 0 : ZMod q)
  | [], n => by simp [toPoly]
  | c :: cs, 0 => by simp [toPoly]
  | c :: cs, n + 1 => by
    simp [toPoly, coeff_toPoly q cs n]

theorem getD_eq_zero_of_length_le : ∀ (A : List ℕ) (n : ℕ), A.length ≤ n → A.getD n 0 = 0
  | [], n, _ => by simp
  | a :: A, 0, h => by simp at h
  | a :: A, n + 1, h => by
    rw [List.getD_cons_succ]; exact getD_eq_zero_of_length_le A n (by simp at h; omega)

theorem degree_toPoly_lt (q : ℕ) (A : List ℕ) : (toPoly q A).degree < A.length := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_toPoly, getD_eq_zero_of_length_le A m hm, Nat.cast_zero]

theorem aeval_toPoly {q : ℕ} {R : Type*} [CommRing R] [Algebra (ZMod q) R] (x : R) :
    ∀ A : List ℕ, aeval x (toPoly q A) = evL x A
  | [] => by simp [toPoly]
  | c :: cs => by simp [toPoly, aeval_toPoly x cs, map_natCast]

theorem isZeroL_of_toPoly_eq_zero (q : ℕ) : ∀ A : List ℕ, toPoly q A = 0 → isZeroL q A = true
  | [], _ => rfl
  | a :: A, h => by
    have h0 := congrArg (fun p => p.coeff 0) h
    have h1 : toPoly q A = 0 := by
      ext n
      have := congrArg (fun p => p.coeff (n + 1)) h
      simpa [coeff_toPoly] using this
    simp only [coeff_toPoly, List.getD_cons_zero, coeff_zero, ZMod.natCast_eq_zero_iff] at h0
    simp only [isZeroL, List.all_cons, Bool.and_eq_true, beq_iff_eq]
    exact ⟨Nat.mod_eq_zero_of_dvd h0, isZeroL_of_toPoly_eq_zero q A h1⟩

theorem toPoly_append (q : ℕ) (A B : List ℕ) : toPoly q (A ++ B) = toPoly q A + X ^ A.length * toPoly q B := by
  induction A with
  | nil => simp [toPoly]
  | cons a A ih => simp [toPoly, ih, pow_succ]; ring

/-- A valid model polynomial: monic (last coefficient `1`) of degree at least `1`. -/
def validP (P : List ℕ) : Bool := P.getLast? == some 1 && 2 ≤ P.length

theorem eq_of_validP {P : List ℕ} (h : validP P = true) : P = P.dropLast ++ [1] ∧ 0 < P.dropLast.length := by
  simp only [validP, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  refine ⟨(List.dropLast_append_getLast? 1 (by rw [h.1]; rfl)).symm, ?_⟩
  simp; omega

theorem length_ruleOf (q : ℕ) (P : List ℕ) : (ruleOf q P).length = P.dropLast.length := by simp [ruleOf]

theorem toPoly_monic {q : ℕ} [Nontrivial (ZMod q)] {P : List ℕ} (h : validP P = true) :
    (toPoly q P).Monic ∧ (toPoly q P).natDegree = P.dropLast.length := by
  obtain ⟨hP, -⟩ := eq_of_validP h
  set P' := P.dropLast
  rw [hP, toPoly_append]
  have ht : toPoly q [1] = 1 := by simp [toPoly]
  rw [ht, mul_one]
  have hlt : (toPoly q P').degree < (X ^ P'.length : (ZMod q)[X]).degree := by
    rw [degree_X_pow]; exact degree_toPoly_lt q P'
  refine ⟨(monic_X_pow _).add_of_right hlt, ?_⟩
  rw [natDegree_add_eq_right_of_degree_lt hlt, natDegree_X_pow]

/-- The element `Σ Aᵢ zⁱ` of `AdjoinRoot (toPoly q P)`. -/
noncomputable def ev (q : ℕ) (P A : List ℕ) : AdjoinRoot (toPoly q P) := evL (AdjoinRoot.root (toPoly q P)) A

theorem ev_eq_mk (q : ℕ) (P A : List ℕ) : ev q P A = AdjoinRoot.mk (toPoly q P) (toPoly q A) := by
  rw [ev, ← aeval_toPoly (q := q), AdjoinRoot.aeval_eq]

theorem isModel_root {q : ℕ} (hq : 0 < q) {P : List ℕ} (h : validP P = true) :
    IsModel q (ruleOf q P) (AdjoinRoot.root (toPoly q P)) := by
  obtain ⟨hP, hf⟩ := eq_of_validP h
  have hchar : ((q : ℕ) : AdjoinRoot (toPoly q P)) = 0 := by
    have := (map_natCast (algebraMap (ZMod q) (AdjoinRoot (toPoly q P))) q).symm
    rwa [ZMod.natCast_self, map_zero] at this
  refine ⟨hq, by rw [length_ruleOf]; exact hf, hchar, ?_⟩
  have h0 : evL (AdjoinRoot.root (toPoly q P)) P = 0 := by
    rw [← aeval_toPoly (q := q), AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have e := congrArg (evL (AdjoinRoot.root (toPoly q P))) hP
  rw [evL_append] at e
  simp only [evL_cons, evL_nil, Nat.cast_one, mul_zero, add_zero, mul_one] at e
  rw [ruleOf, length_negL, evL_negL hq hchar]
  linear_combination h0 - e

theorem ev_eq_of_eqL {q : ℕ} (hq : 0 < q) {P : List ℕ} (h : validP P = true) (A B : List ℕ)
    (hAB : eqL q (ruleOf q P) A B = true) : ev q P A = ev q P B :=
  evL_eq_of_eqL (isModel_root hq h) A B hAB

/-- The degree argument (independence of the power basis): a nonzero list of length `≤ f` is nonzero in
`AdjoinRoot (toPoly q P)`. -/
theorem ev_ne_zero_of_isZeroL {q : ℕ} [Fact q.Prime] {P : List ℕ} (h : validP P = true) (A : List ℕ)
    (hA : A.length ≤ P.dropLast.length) (hz : isZeroL q A = false) : ev q P A ≠ 0 := by
  obtain ⟨hmon, hdeg⟩ := toPoly_monic (q := q) h
  intro h0
  rw [ev_eq_mk, AdjoinRoot.mk_eq_zero] at h0
  have hne : toPoly q A ≠ 0 := fun h' => by rw [isZeroL_of_toPoly_eq_zero q A h'] at hz; exact Bool.noConfusion hz
  have h1 := natDegree_le_of_dvd h0 hne
  have h2 : (toPoly q A).natDegree < A.length := by
    rw [natDegree_lt_iff_degree_lt hne]; exact degree_toPoly_lt q A
  omega

theorem ev_ne_of_eqL {q : ℕ} [Fact q.Prime] {P : List ℕ} (h : validP P = true) (A B : List ℕ)
    (hAB : eqL q (ruleOf q P) A B = false) : ev q P A ≠ ev q P B := by
  have hM := isModel_root (Fact.out : q.Prime).pos h
  intro hE
  apply ev_ne_zero_of_isZeroL h (reduceL q (ruleOf q P) (subL q A B))
    (by rw [← length_ruleOf q P]; exact length_reduceL hM.fpos _) hAB
  rw [ev, evL_reduceL hM, evL_subL hM.qpos hM.char]
  exact sub_eq_zero.mpr hE

theorem ev_evalP1L {q : ℕ} (hq : 0 < q) {P : List ℕ} (h : validP P = true) (Y : List ℕ) (p : P1) :
    ev q P (evalP1L q (ruleOf q P) Y p) = P1.eval (ev q P Y) p :=
  evL_evalP1L (isModel_root hq h) Y p

theorem ev_evalP2L {q : ℕ} (hq : 0 < q) {P : List ℕ} (h : validP P = true) (X Y : List ℕ) (F : P2) :
    ev q P (evalP2L q (ruleOf q P) X Y F) = P2.eval (ev q P X) (ev q P Y) F :=
  evL_evalP2L (isModel_root hq h) X Y F

theorem ev_powL {q : ℕ} (hq : 0 < q) {P : List ℕ} (h : validP P = true) (B : List ℕ) (n : ℕ) :
    ev q P (powL q (ruleOf q P) B n) = ev q P B ^ n :=
  evL_powL (isModel_root hq h) B n

theorem ev_mulL {q : ℕ} (hq : 0 < q) {P : List ℕ} (h : validP P = true) (A B : List ℕ)
    (hB : B.length ≤ P.dropLast.length) : ev q P (mulL q (ruleOf q P) A B) = ev q P A * ev q P B :=
  evL_mulL (isModel_root hq h) A B (by rw [length_ruleOf]; exact hB)

theorem ev_smulL {q : ℕ} (hq : 0 < q) {P : List ℕ} (h : validP P = true) (c : ℕ) (A : List ℕ) :
    ev q P (smulL q c A) = c * ev q P A :=
  evL_smulL (isModel_root hq h).char c A

@[simp] theorem ev_nil (q : ℕ) (P : List ℕ) : ev q P [] = 0 := rfl

theorem ev_const (q : ℕ) (P : List ℕ) (c : ℕ) : ev q P [c] = c := by simp [ev]

end X2Y5Z7.FiniteFields
