module

public import X2Y5Z7.FiniteFields.Irreducible
public import X2Y5Z7.FiniteFields.Symbol
public import X2Y5Z7.SUnits.Data
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

/-! # Finite-field models of residue fields, with symbols

* `FFModel`: a prime `q ≡ 1 mod 5`, a monic irreducible `P` over `F_q` (`Irreducible (toPoly q P)`) and `ζ ∈ ℕ`
  whose image is a primitive fifth root of unity. `D.K = AdjoinRoot (toPoly q P)` is a field with `q^f` elements
  (`card_K`); `D.ev A = Σ Aᵢ zⁱ`; `D.sym : D.K → ZMod 5` is the fifth-power residue symbol, with `sym_spec`:
  `x ≠ 0 → x^((q^f - 1)/5) = ζ^(sym x).val`, and `sym_mul`, `sym_one`, `sym_inv`, `sym_div`, `sym_pow_five`.
* `symCheck`: computable test with `sym_of_symCheck : symCheck … A s = true → D.ev A ≠ 0 ∧ D.sym (D.ev A) = s`.
* `L8Prime`: a model `k_i = F_q[x]/(h_i)` of the residue field of a prime of `L8`, with `h(x) = 0`, `h'(x) ≠ 0`.
* `L24Prime`: a model `K` of the residue field of a prime of `L24`, with `α, β ∈ K`, `h(α) = 0`, `h_i(α) = 0`,
  `h'(α) ≠ 0`, `ψ(β) = 0`, `m₅'(5β) ≠ 0`, and the symbols `sym (B_j(α, β)) = row j` of the S-unit basis
  (`L24Prime.sym_imgB`), with `B_j(α, β) = P2.eval α β (Bnum j) / Bden j` (`imgB`), numerator and denominator nonzero.
  All facts follow from one Boolean check `l24Check`, evaluated by `decide +kernel`. -/

namespace X2Y5Z7.FiniteFields

open Polynomial

/-- `h' = 8x⁷ + 28x⁶ - 168x⁵ - 840x⁴ - 560x³ + 1680x² + 1680x - 480`. -/
def hP1d : P1 := [-480, 1680, 1680, -560, -840, -168, 28, 8]

/-- `ψ = 25y³ + 20y² + 14y + 14`. -/
def psiP1 : P1 := [14, 14, 20, 25]

/-- `m₅' = 3y² + 8y + 14`, where `m₅(y) = y³ + 4y² + 14y + 70 = 5 ψ(y/5)`. -/
def m5dP1 : P1 := [14, 8, 3]

/-- The field-level checks: `P` valid, `q ≡ 1 mod 5`, `ζ⁵ ≡ 1`, `ζ ≠ 1` in `K`. -/
def ffCheck (q : ℕ) (P : List ℕ) (zeta : ℕ) : Bool :=
  validP P && q % 5 == 1 && zeta ^ 5 % q == 1 && !eqL q (ruleOf q P) [zeta] [1]

/-- An explicit finite field `F_q[z]/(P)` with a primitive fifth root of unity `ζ ∈ F_q`. -/
structure FFModel where
  q : ℕ
  P : List ℕ
  zeta : ℕ
  prime : q.Prime
  irred : Irreducible (toPoly q P)
  fcheck : ffCheck q P zeta = true

namespace FFModel

variable (D : FFModel)

/-- The degree `f`. -/
def f : ℕ := D.P.length - 1

/-- The field. -/
abbrev K : Type := AdjoinRoot (toPoly D.q D.P)

instance : Fact D.q.Prime := ⟨D.prime⟩
instance : Fact (Irreducible (toPoly D.q D.P)) := ⟨D.irred⟩

/-- `Σ Aᵢ zⁱ ∈ K`. -/
noncomputable def ev (A : List ℕ) : D.K := FiniteFields.ev D.q D.P A

/-- The exponent `(q^f - 1)/5`. -/
def e : ℕ := (D.q ^ D.f - 1) / 5

/-- `ζ` in `K`. -/
noncomputable def zetaK : D.K := (D.zeta : D.K)

/-- The fifth-power residue symbol of `K` with respect to `ζ`. -/
noncomputable def sym (x : D.K) : ZMod 5 := symK D.zetaK D.e x

theorem valid : validP D.P = true := by
  have := D.fcheck; simp only [ffCheck, Bool.and_eq_true] at this; exact this.1.1.1

theorem q5 : D.q % 5 = 1 := by
  have := D.fcheck; simp only [ffCheck, Bool.and_eq_true, beq_iff_eq] at this; exact this.1.1.2

theorem zeta5 : D.zeta ^ 5 % D.q = 1 := by
  have := D.fcheck; simp only [ffCheck, Bool.and_eq_true, beq_iff_eq] at this; exact this.1.2

theorem zeta1 : eqL D.q (ruleOf D.q D.P) [D.zeta] [1] = false := by
  have := D.fcheck; simp only [ffCheck, Bool.and_eq_true, Bool.not_eq_true'] at this; exact this.2

theorem qpos : 0 < D.q := D.prime.pos

theorem isModel : IsModel D.q (ruleOf D.q D.P) (AdjoinRoot.root (toPoly D.q D.P)) := isModel_root D.qpos D.valid

theorem char : ((D.q : ℕ) : D.K) = 0 := D.isModel.char

theorem monic : (toPoly D.q D.P).Monic := (toPoly_monic D.valid).1

theorem natDegree : (toPoly D.q D.P).natDegree = D.f := by
  rw [(toPoly_monic D.valid).2, f]; simp

instance : Module.Finite (ZMod D.q) D.K := (AdjoinRoot.powerBasis' D.monic).finite

instance : Finite D.K := Module.finite_of_finite (ZMod D.q)

noncomputable instance : Fintype D.K := Fintype.ofFinite _

theorem card_K : Fintype.card D.K = D.q ^ D.f := by
  rw [Module.card_eq_pow_finrank (K := ZMod D.q), (AdjoinRoot.powerBasis' D.monic).finrank,
    AdjoinRoot.powerBasis'_dim, ZMod.card, D.natDegree]

theorem e_mul_five : D.e * 5 = D.q ^ D.f - 1 := by
  have h : D.q ^ D.f % 5 = 1 := by rw [Nat.pow_mod, D.q5, one_pow, Nat.one_mod]
  rw [e]; omega

theorem pow_e_mul_five (x : D.K) (hx : x ≠ 0) : x ^ (D.e * 5) = 1 := by
  rw [D.e_mul_five, ← D.card_K]; exact FiniteField.pow_card_sub_one_eq_one x hx

@[simp] theorem ev_const (c : ℕ) : D.ev [c] = (c : D.K) := FiniteFields.ev_const _ _ c

theorem zetaK_prim : IsPrimitiveRoot D.zetaK 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5 : D.zetaK ^ 5 = 1 := by
    rw [zetaK, ← Nat.cast_pow, ← natCast_mod D.char, D.zeta5, Nat.cast_one]
  have h1 : D.zetaK ≠ 1 := by
    have := ev_ne_of_eqL D.valid _ _ D.zeta1
    rw [FiniteFields.ev_const, FiniteFields.ev_const, Nat.cast_one] at this
    exact this
  have := IsPrimitiveRoot.orderOf D.zetaK
  rwa [orderOf_eq_prime h5 h1] at this

theorem sym_spec {x : D.K} (hx : x ≠ 0) : x ^ ((D.q ^ D.f - 1) / 5) = D.zetaK ^ (D.sym x).val :=
  symK_spec D.zetaK_prim D.pow_e_mul_five hx

theorem sym_eq_iff {x : D.K} (hx : x ≠ 0) (s : ZMod 5) : D.sym x = s ↔ x ^ D.e = D.zetaK ^ s.val :=
  symK_eq_iff D.zetaK_prim D.pow_e_mul_five hx s

theorem sym_mul {x y : D.K} (hx : x ≠ 0) (hy : y ≠ 0) : D.sym (x * y) = D.sym x + D.sym y :=
  symK_mul D.zetaK_prim D.pow_e_mul_five hx hy

theorem sym_one : D.sym 1 = 0 := symK_one D.zetaK_prim D.pow_e_mul_five

theorem sym_inv {x : D.K} (hx : x ≠ 0) : D.sym x⁻¹ = - D.sym x := symK_inv D.zetaK_prim D.pow_e_mul_five hx

theorem sym_div {x y : D.K} (hx : x ≠ 0) (hy : y ≠ 0) : D.sym (x / y) = D.sym x - D.sym y :=
  symK_div D.zetaK_prim D.pow_e_mul_five hx hy

theorem sym_pow {x : D.K} (hx : x ≠ 0) (n : ℕ) : D.sym (x ^ n) = n * D.sym x :=
  symK_pow D.zetaK_prim D.pow_e_mul_five hx n

theorem sym_pow_five {x : D.K} (hx : x ≠ 0) : D.sym (x ^ 5) = 0 := symK_pow_five D.zetaK_prim D.pow_e_mul_five hx

/-! ### Computation -/

theorem ev_eq_zero_of_eqL (A : List ℕ) (h : eqL D.q (ruleOf D.q D.P) A [] = true) : D.ev A = 0 :=
  ev_eq_of_eqL D.qpos D.valid A [] h

theorem ev_ne_zero_of_eqL (A : List ℕ) (h : eqL D.q (ruleOf D.q D.P) A [] = false) : D.ev A ≠ 0 :=
  ev_ne_of_eqL D.valid A [] h

theorem ev_evalP1L (Y : List ℕ) (p : P1) : D.ev (evalP1L D.q (ruleOf D.q D.P) Y p) = P1.eval (D.ev Y) p :=
  FiniteFields.ev_evalP1L D.qpos D.valid Y p

theorem ev_evalP2L (X Y : List ℕ) (F : P2) :
    D.ev (evalP2L D.q (ruleOf D.q D.P) X Y F) = P2.eval (D.ev X) (D.ev Y) F :=
  FiniteFields.ev_evalP2L D.qpos D.valid X Y F

theorem ev_smulL (c : ℕ) (A : List ℕ) : D.ev (smulL D.q c A) = c * D.ev A := FiniteFields.ev_smulL D.qpos D.valid c A

/-- Division by a natural number `d`, given an inverse `inv` of `d` mod `q`. -/
theorem ev_div_natCast (A : List ℕ) (d inv : ℕ) (h : d * inv % D.q = 1) :
    (d : D.K) ≠ 0 ∧ D.ev A / (d : D.K) = D.ev (smulL D.q inv A) := by
  have h1 : (d : D.K) * (inv : D.K) = 1 := by
    rw [← Nat.cast_mul, ← natCast_mod D.char, h, Nat.cast_one]
  have hd : (d : D.K) ≠ 0 := left_ne_zero_of_mul_eq_one h1
  refine ⟨hd, ?_⟩
  rw [D.ev_smulL, div_eq_iff hd]
  linear_combination -(D.ev A) * h1

end FFModel

/-- The computable symbol test: `A ≠ 0` and `A^((q^f - 1)/5) = ζ^s` in `F_q[z]/(P)`, with `s < 5`. -/
def symCheck (q : ℕ) (P : List ℕ) (zeta : ℕ) (A : List ℕ) (s : ℕ) : Bool :=
  s < 5 && !eqL q (ruleOf q P) A [] &&
    eqL q (ruleOf q P) (powL q (ruleOf q P) A ((q ^ (P.length - 1) - 1) / 5)) [zeta ^ s % q]

theorem FFModel.sym_of_symCheck (D : FFModel) (A : List ℕ) (s : ℕ) (h : symCheck D.q D.P D.zeta A s = true) :
    D.ev A ≠ 0 ∧ D.sym (D.ev A) = s := by
  simp only [symCheck, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨hs, hz⟩, hp⟩ := h
  have hA := D.ev_ne_zero_of_eqL A hz
  refine ⟨hA, ?_⟩
  rw [D.sym_eq_iff hA, ZMod.val_cast_of_lt hs]
  have := ev_eq_of_eqL D.qpos D.valid _ _ hp
  rw [ev_powL D.qpos D.valid, FiniteFields.ev_const, natCast_mod D.char] at this
  have h2 : D.ev A ^ ((D.q ^ (D.P.length - 1) - 1) / 5) = ((D.zeta ^ s : ℕ) : D.K) := this
  rw [Nat.cast_pow] at h2
  exact h2

/-- The check for one S-unit `B_j`: the inverse of `Bden j`, the numerator is nonzero, and the symbol is `s`. -/
def bCheck (q : ℕ) (P : List ℕ) (zeta : ℕ) (alpha beta : List ℕ) (j : Fin 24) (s : ℕ) : Bool :=
  Bden j * (Bden j ^ (q - 2) % q) % q == 1 &&
    !eqL q (ruleOf q P) (evalP2L q (ruleOf q P) alpha beta (Bnum j)) [] &&
    symCheck q P zeta (smulL q (Bden j ^ (q - 2) % q) (evalP2L q (ruleOf q P) alpha beta (Bnum j))) s

/-- The symbols of all 24 S-units against the row `row`. -/
def rowCheck (q : ℕ) (P : List ℕ) (zeta : ℕ) (alpha beta row : List ℕ) : Bool :=
  (List.finRange 24).all (fun j => bCheck q P zeta alpha beta j (row.getD j 0))

/-- All the checks for a prime of `L24`. -/
def l24Check (q : ℕ) (P : List ℕ) (zeta : ℕ) (hi alpha beta row : List ℕ) : Bool :=
  eqL q (ruleOf q P) (evalP1L q (ruleOf q P) alpha hP1) [] &&
    eqL q (ruleOf q P) (evalP1L q (ruleOf q P) alpha (hi.map (fun n : ℕ => (n : ℤ)))) [] &&
    !eqL q (ruleOf q P) (evalP1L q (ruleOf q P) alpha hP1d) [] &&
    eqL q (ruleOf q P) (evalP1L q (ruleOf q P) beta psiP1) [] &&
    !eqL q (ruleOf q P) (evalP1L q (ruleOf q P) (smulL q 5 beta) m5dP1) [] &&
    rowCheck q P zeta alpha beta row

/-- The checks for a prime of `L8`: `h(x) = 0`, `h'(x) ≠ 0` at the root `x`. -/
def l8Check (q : ℕ) (P : List ℕ) : Bool :=
  eqL q (ruleOf q P) (evalP1L q (ruleOf q P) [0, 1] hP1) [] &&
    !eqL q (ruleOf q P) (evalP1L q (ruleOf q P) [0, 1] hP1d) []

/-- A model of the residue field of a prime `𝔮_i` of `L8` above `q`: `P = h_i`, the root is `a mod 𝔮_i`. -/
structure L8Prime extends FFModel where
  /-- The index `i` of the prime (1-based, as in `models.txt`). -/
  i : ℕ
  check : l8Check q P = true

/-- A model of the residue field of a prime `𝔔` of `L24` above `q`, with the images `α`, `β` of `a`, `b`. -/
structure L24Prime extends FFModel where
  /-- The index `i` of the prime of `L8` below (1-based). -/
  i : ℕ
  /-- The index `l` of the prime above `𝔮_i` (1-based). -/
  l : ℕ
  /-- The factor `h_i` of `h` mod `q` (monic, constant first). -/
  hi : List ℕ
  alpha : List ℕ
  beta : List ℕ
  /-- The symbols of `B_1, …, B_24`. -/
  row : List ℕ
  check : l24Check q P zeta hi alpha beta row = true

namespace L8Prime

variable (D : L8Prime)

/-- The root `x` of `h_i`, the image of `a`. -/
noncomputable def x : D.K := D.ev [0, 1]

theorem x_eq_root : D.x = AdjoinRoot.root (toPoly D.q D.P) := ev_X _ _

theorem h_x : P1.eval D.x hP1 = 0 := by
  have := D.check; simp only [l8Check, Bool.and_eq_true] at this
  rw [x, ← D.ev_evalP1L]; exact D.ev_eq_zero_of_eqL _ this.1

theorem hd_x : P1.eval D.x hP1d ≠ 0 := by
  have := D.check; simp only [l8Check, Bool.and_eq_true, Bool.not_eq_true'] at this
  rw [x, ← D.ev_evalP1L]; exact D.ev_ne_zero_of_eqL _ this.2

end L8Prime

namespace L24Prime

variable (D : L24Prime)

/-- The image of `a`. -/
noncomputable def α : D.K := D.ev D.alpha

/-- The image of `b`. -/
noncomputable def β : D.K := D.ev D.beta

/-- The image of the S-unit `B_j`. -/
noncomputable def imgB (j : Fin 24) : D.K := P2.eval D.α D.β (Bnum j) / (Bden j : D.K)

/-- The symbol matrix row as a function. -/
def rowF (j : Fin 24) : ZMod 5 := (D.row.getD j 0 : ZMod 5)

theorem checks : l24Check D.q D.P D.zeta D.hi D.alpha D.beta D.row = true := D.check

/-- `h(α) = 0`. -/
theorem h_α : P1.eval D.α hP1 = 0 := by
  have := D.checks; simp only [l24Check, Bool.and_eq_true, Bool.not_eq_true'] at this
  rw [α, ← D.ev_evalP1L]; exact D.ev_eq_zero_of_eqL _ this.1.1.1.1.1

/-- `h_i(α) = 0`. -/
theorem hi_α : P1.eval D.α (D.hi.map (fun n : ℕ => (n : ℤ))) = 0 := by
  have := D.checks; simp only [l24Check, Bool.and_eq_true, Bool.not_eq_true'] at this
  rw [α, ← D.ev_evalP1L]; exact D.ev_eq_zero_of_eqL _ this.1.1.1.1.2

/-- `h'(α) ≠ 0`. -/
theorem hd_α : P1.eval D.α hP1d ≠ 0 := by
  have := D.checks; simp only [l24Check, Bool.and_eq_true, Bool.not_eq_true'] at this
  rw [α, ← D.ev_evalP1L]; exact D.ev_ne_zero_of_eqL _ this.1.1.1.2

/-- `ψ(β) = 0`. -/
theorem psi_β : P1.eval D.β psiP1 = 0 := by
  have := D.checks; simp only [l24Check, Bool.and_eq_true, Bool.not_eq_true'] at this
  rw [β, ← D.ev_evalP1L]; exact D.ev_eq_zero_of_eqL _ this.1.1.2

/-- `m₅'(5β) ≠ 0`. -/
theorem m5d_β : P1.eval (5 * D.β) m5dP1 ≠ 0 := by
  have := D.checks; simp only [l24Check, Bool.and_eq_true, Bool.not_eq_true'] at this
  have := D.ev_ne_zero_of_eqL _ this.1.2
  rwa [D.ev_evalP1L, D.ev_smulL, Nat.cast_ofNat] at this

theorem bCheck_true (j : Fin 24) : bCheck D.q D.P D.zeta D.alpha D.beta j (D.row.getD j 0) = true := by
  have := D.checks; simp only [l24Check, Bool.and_eq_true] at this
  have := this.2
  simp only [rowCheck, List.all_eq_true] at this
  exact this j (List.mem_finRange j)

/-- The numerator of `B_j(α, β)` is nonzero. -/
theorem num_ne (j : Fin 24) : P2.eval D.α D.β (Bnum j) ≠ 0 := by
  have := D.bCheck_true j
  simp only [bCheck, Bool.and_eq_true, Bool.not_eq_true'] at this
  rw [α, β, ← D.ev_evalP2L]; exact D.ev_ne_zero_of_eqL _ this.1.2

/-- The denominator `Bden j` is nonzero in `K`. -/
theorem den_ne (j : Fin 24) : (Bden j : D.K) ≠ 0 := by
  have := D.bCheck_true j
  simp only [bCheck, Bool.and_eq_true, beq_iff_eq] at this
  exact (D.ev_div_natCast [] _ _ this.1.1).1

theorem imgB_ne (j : Fin 24) : D.imgB j ≠ 0 := div_ne_zero (D.num_ne j) (D.den_ne j)

/-- The symbol of `B_j(α, β)` is the `j`-th entry of the row. -/
theorem sym_imgB (j : Fin 24) : D.sym (D.imgB j) = D.rowF j := by
  have := D.bCheck_true j
  simp only [bCheck, Bool.and_eq_true, beq_iff_eq] at this
  obtain ⟨⟨hinv, -⟩, hs⟩ := this
  have h := (D.sym_of_symCheck _ _ hs).2
  rw [← (D.ev_div_natCast _ _ _ hinv).2, D.ev_evalP2L] at h
  exact h

end L24Prime

end X2Y5Z7.FiniteFields
