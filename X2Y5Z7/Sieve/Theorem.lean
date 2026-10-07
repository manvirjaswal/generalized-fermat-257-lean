import X2Y5Z7.Sieve.Identities
import X2Y5Z7.Sieve.CheckRun

/-! # Theorem 7.1 of the paper (the sieve)

There is no `c ∈ 𝔽₅²⁴` satisfying the three conditions (N), (V) and (Q) of Theorem 7.1. The data are those printed
in the paper (`Data.lean`).

The proof: (N) and (V) put `c` in the affine space `c₀ + span(d₁, …, d₁₀)` of (A.2). After an invertible change of
coordinates `x`, the symbol vector at `181` depends only on the first six coordinates of `x` and determines them, and
the symbol vector at `311` then determines the last four. So `c` is determined by its symbol vectors
`i1 ∈ I(181)` and `i2 ∈ I(311)`, and the finite check of `Check.lean` runs through all `59 · 240` pairs. -/

namespace X2Y5Z7.Sieve

open Matrix Cert

/-- Condition (N): `NM c ≡ TT (mod 5)`. -/
def CondN (c : Fin 24 → ZMod 5) : Prop :=
  (NM.map (Int.cast : ℤ → ZMod 5)) *ᵥ c = fun i => ((TT i : ℤ) : ZMod 5)

/-- Condition (V): `c₃ = 2`, `c₅ = 3` and `c₂ = c₄ = c₆ = c₇ = c₈ = 0` (the paper's indices; 0-based here). -/
def CondV (c : Fin 24 → ZMod 5) : Prop :=
  c 2 = 2 ∧ c 4 = 3 ∧ c 1 = 0 ∧ c 3 = 0 ∧ c 5 = 0 ∧ c 6 = 0 ∧ c 7 = 0

/-- Condition (Q): `M_q c ∈ I(q)` for `q = 181, 311, 131, 251, 101`. -/
def CondQ (c : Fin 24 → ZMod 5) : Prop :=
  M181 *ᵥ c ∈ I181 ∧ M311 *ᵥ c ∈ I311 ∧ M131 *ᵥ c ∈ I131 ∧ M251 *ᵥ c ∈ I251 ∧ M101 *ᵥ c ∈ I101

/-! ## Step 1: (N) and (V) as one linear system -/

theorem mulVec_apply_row {m : ℕ} (M : Matrix (Fin m) (Fin 24) (ZMod 5)) (c : Fin 24 → ZMod 5) (i : Fin m) :
    (M *ᵥ c) i = M i ⬝ᵥ c := rfl

theorem constraints (c : Fin 24 → ZMod 5) (hN : CondN c) (hV : CondV c) : A *ᵥ c = b := by
  have hV' : ∀ k : Fin 7, c (vIdx k) = vVal k := by
    obtain ⟨h2, h4, h1, h3, h5, h6, h7⟩ := hV
    intro k
    fin_cases k <;> simp [vIdx, vVal, h1, h2, h3, h4, h5, h6, h7]
  funext i
  refine Fin.addCases (m := 10) (n := 7) (fun i => ?_) (fun k => ?_) i
  · have h := congrFun hN i
    rw [mulVec_apply_row, b_N i, show A (Fin.castAdd 7 i) = fun j => ((NM i j : ℤ) : ZMod 5) from
      funext (A_rows_N i)]
    exact h
  · rw [mulVec_apply_row, A_rows_V k, single_dotProduct, one_mul, b_V k, hV' k]

/-! ## Step 2: the affine space and the coordinates `x` -/

/-- The coordinates of `c` in the affine space. -/
def coords (c : Fin 24 → ZMod 5) : Fin 10 → ZMod 5 := Pinv *ᵥ (S *ᵥ (c - c0))

theorem param (c : Fin 24 → ZMod 5) (hA : A *ᵥ c = b) : c = c0 + W *ᵥ coords c := by
  have h1 : (1 - Dm * S) *ᵥ (c - c0) = 0 := by
    rw [← R_mul_A, ← mulVec_mulVec, mulVec_sub, hA, A_c0, sub_self, mulVec_zero]
  rw [sub_mulVec, one_mulVec, sub_eq_zero, ← mulVec_mulVec] at h1
  rw [coords, W_eq, ← mulVec_mulVec, mulVec_mulVec _ P Pinv, P_mul_Pinv, one_mulVec, ← h1,
    add_sub_cancel]

/-! ## Step 3: the symbol vectors in the coordinates `x` -/

/-- The first six coordinates. -/
def x1 (x : Fin 10 → ZMod 5) : Fin 6 → ZMod 5 := fun j => x (Fin.castAdd 4 j)

/-- The last four coordinates. -/
def x2 (x : Fin 10 → ZMod 5) : Fin 4 → ZMod 5 := fun j => x (Fin.natAdd 6 j)

theorem symbols {m : ℕ} (M : Matrix (Fin m) (Fin 24) (ZMod 5)) (a : Fin m → ZMod 5)
    (G1 : Matrix (Fin m) (Fin 6) (ZMod 5)) (G2 : Matrix (Fin m) (Fin 4) (ZMod 5))
    (ha : M *ᵥ c0 = a) (hG1 : ∀ i j, (M * W) i (Fin.castAdd 4 j) = G1 i j)
    (hG2 : ∀ i j, (M * W) i (Fin.natAdd 6 j) = G2 i j) (x : Fin 10 → ZMod 5) :
    M *ᵥ (c0 + W *ᵥ x) = a + G1 *ᵥ x1 x + G2 *ᵥ x2 x := by
  have hsplit : (M * W) *ᵥ x = G1 *ᵥ x1 x + G2 *ᵥ x2 x := by
    funext i
    show ∑ j : Fin (6 + 4), (M * W) i j * x j = ∑ j, G1 i j * x1 x j + ∑ j, G2 i j * x2 x j
    rw [Fin.sum_univ_add]
    simp only [x1, x2, hG1, hG2]
  rw [mulVec_add, ha, mulVec_mulVec, hsplit, add_assoc]

/-! ## Step 4: the conditions at 181 and 311 determine the coordinates -/

theorem x1_eq (x : Fin 10 → ZMod 5) (i1 : Fin 11 → ZMod 5)
    (h : a181 + G1_181 *ᵥ x1 x + G2_181 *ᵥ x2 x = i1) : x1 x = L1 *ᵥ (i1 - a181) := by
  rw [← h, G2_181_zero, zero_mulVec, add_zero, add_sub_cancel_left, mulVec_mulVec, L1_mul, one_mulVec]

theorem x2_eq (x : Fin 10 → ZMod 5) (i2 : Fin 11 → ZMod 5)
    (h : a311 + G1_311 *ᵥ x1 x + G2_311 *ᵥ x2 x = i2) :
    x2 x = L2 *ᵥ (i2 - a311 - G1_311 *ᵥ x1 x) := by
  rw [← h, add_assoc, add_sub_cancel_left, add_sub_cancel_left, mulVec_mulVec, L2_mul, one_mulVec]

/-! ## Step 5: the theorem -/

/-- **Theorem 7.1.** No `c ∈ 𝔽₅²⁴` satisfies (N), (V) and (Q). -/
theorem sieve (c : Fin 24 → ZMod 5) (hN : CondN c) (hV : CondV c) (hQ : CondQ c) : False := by
  obtain ⟨h181, h311, h131, h251, h101⟩ := hQ
  set x := coords c
  have hc : c = c0 + W *ᵥ x := param c (constraints c hN hV)
  have s181 := symbols M181 a181 G1_181 G2_181 a181_eq G1_181_eq G2_181_eq x
  have s311 := symbols M311 a311 G1_311 G2_311 a311_eq G1_311_eq G2_311_eq x
  have s131 := symbols M131 a131 G1_131 G2_131 a131_eq G1_131_eq G2_131_eq x
  have s251 := symbols M251 a251 G1_251 G2_251 a251_eq G1_251_eq G2_251_eq x
  have s101 := symbols M101 a101 G1_101 G2_101 a101_eq G1_101_eq G2_101_eq x
  rw [← hc] at s181 s311 s131 s251 s101
  -- the symbol vectors at 181 and 311 determine the coordinates
  have hx1 := x1_eq x _ s181.symm
  have hx2 := x2_eq x _ s311.symm
  -- the row of the check for `i1 = M181 c`
  have hi1 : List.ofFn (M181 *ᵥ c) ∈ rows181.map Prod.fst := by
    rw [rows_cover, ← I181L_eq]
    exact (mem_map_ofFn _ _).2 h181
  obtain ⟨r, hr, hr1⟩ := List.mem_map.1 hi1
  have hrow : rowOK r = true := List.all_eq_true.1 rows_ok r hr
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at hrow
  obtain ⟨⟨hrx1, hrg⟩, hrest⟩ := hrow
  -- the list forms of `x1` and `g = G1_311 x1`
  have ex1 : r.2.1 = List.ofFn (x1 x) := by
    rw [← hrx1, hr1, ← L1L_eq, ← a181L_eq, subL_ofFn, mvL_rowsOf, ← hx1]
  have eg : r.2.2 = List.ofFn (G1_311 *ᵥ x1 x) := by
    rw [← hrg, ex1, ← G1_311L_eq, mvL_rowsOf]
  rcases hrest with h | h
  · -- the symbol vector at 181 of the point is `i1`
    apply h
    rw [ex1, hr1, ← a181L_eq, ← G1_181L_eq, mvL_rowsOf, addL_ofFn, s181, G2_181_zero, zero_mulVec, add_zero]
  · -- the pair `(i1, i2)` with `i2 = M311 c` passes, which the check excludes
    have hi2 : List.ofFn (M311 *ᵥ c) ∈ I311L := by
      rw [← I311L_eq]
      exact (mem_map_ofFn _ _).2 h311
    have hp := List.all_eq_true.1 h _ hi2
    simp only [pairFails, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hp
    have ex2 : mvL L2L (subL (subL (List.ofFn (M311 *ᵥ c)) a311L) r.2.2) = List.ofFn (x2 x) := by
      rw [eg, ← L2L_eq, ← a311L_eq, subL_ofFn, subL_ofFn, mvL_rowsOf, ← hx2]
    rw [ex2, ex1, eg] at hp
    simp only [← a311L_eq, ← a131L_eq, ← a251L_eq, ← a101L_eq, ← G2_311L_eq, ← G1_131L_eq, ← G2_131L_eq,
      ← G1_251L_eq, ← G2_251L_eq, ← G1_101L_eq, ← G2_101L_eq, mvL_rowsOf, addL_ofFn] at hp
    rw [← s131, ← s251, ← s101, ← I131L_eq, ← I251L_eq, ← I101L_eq, mem_map_ofFn, mem_map_ofFn,
      mem_map_ofFn, add_assoc, ← add_assoc a311, ← s311] at hp
    rcases hp with ((h1 | h1) | h1) | h1
    · exact h1 rfl
    · exact h1 h131
    · exact h1 h251
    · exact h1 h101

end X2Y5Z7.Sieve
