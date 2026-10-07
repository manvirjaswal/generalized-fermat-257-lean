import X2Y5Z7.Arith.L24
import X2Y5Z7.Integral.LUCertificate
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Integrality and relative norms in `L₈` and `L₂₄ = L₈(b)`

* `isIntegral_div_of_homog`: `w(a)/d ∈ L₈` is integral over `ℤ` if `d^n f(w(a)/d) = 0` for a monic integer
  polynomial `f = c₀ + c₁ X + … + X^n` (the homogenised polynomial `homog d w (c ++ [1])` is checked to vanish at `a`
  by an `ev8` certificate).
* The ring of integers of `L₈` has the `ℤ`-basis `ω_k = W_k(a)/820` (`Wω`), with
  `ω = 1, a, a², a³, a⁴/2, (a⁵+2a)/4, (a⁶+2a²)/4, (a⁷+176a⁶+109a⁵+130a⁴+490a³+380a²+190a+220)/820`
  (computed with PARI/GP; not used here). We only need that each `ω_k` is integral
  (`ω_isIntegral`), so that `∑ n_k ω_k` is integral for all integers `n_k` (`isIntegral_wsum`).
* For `X = x₀ + x₁ b + x₂ b²` (`x_i ∈ L₈`): `X` is a root of `t³ - T t² + S t - N` with the trace `T`, the second
  invariant `S` and the norm `N = N_{L₂₄/L₈}(X)` given by explicit forms (`cubic_rel`, `norm_rel`), so `X` is
  integral when `T, S, N` are (`isIntegral_of_cubic`). -/

namespace X2Y5Z7

open Polynomial

noncomputable section

namespace Integral

/-! ## Monic integer polynomials from lists -/

/-- The polynomial `c₀ + c₁ X + …` of a coefficient list. -/
def toPoly : P1 → ℤ[X]
  | [] => 0
  | c :: cs => C c + X * toPoly cs

theorem aeval_toPoly {R : Type*} [CommRing R] [Algebra ℤ R] (x : R) : ∀ p : P1, aeval x (toPoly p) = P1.eval x p
  | [] => by simp [toPoly]
  | c :: cs => by simp [toPoly, aeval_toPoly x cs]

theorem toPoly_monic : ∀ cs : P1, (toPoly (cs ++ [1])).Monic
  | [] => by simp [toPoly]
  | c :: cs => by
    have hq := toPoly_monic cs
    change (C c + X * toPoly (cs ++ [1])).Monic
    apply Monic.add_of_right (monic_X.mul hq)
    refine lt_of_le_of_lt degree_C_le ?_
    rw [← natDegree_pos_iff_degree_pos, natDegree_X_mul hq.ne_zero]
    omega

/-- `homog d w c` is `d^(n) · f(w/d)` for `f = c₀ + … + cₙ Xⁿ`, as a polynomial in `x` (for `c ≠ []`). -/
def homog (d : ℤ) (w : P1) : P1 → P1
  | [] => []
  | [c] => [c]
  | c :: c' :: cs => P1.add [c * d ^ (cs.length + 1)] (P1.mul w (homog d w (c' :: cs)))

theorem eval_homog {K : Type*} [Field K] (x : K) (d : ℤ) (hd : (d : K) ≠ 0) (w : P1) :
    ∀ c : P1, c ≠ [] → P1.eval x (homog d w c) = (d : K) ^ (c.length - 1) * P1.eval (P1.eval x w / d) c
  | [], h => absurd rfl h
  | [c], _ => by simp [homog]
  | c :: c' :: cs, _ => by
    have ih := eval_homog x d hd w (c' :: cs) (List.cons_ne_nil _ _)
    simp only [homog, P1.eval_add, P1.eval_mul, ih, P1.eval_cons, P1.eval_nil, mul_zero, add_zero,
      List.length_cons, Nat.add_sub_cancel, Int.cast_mul, Int.cast_pow]
    field_simp
    ring

/-- Integrality of `w(a)/d` from a monic integer polynomial `c ++ [1]` that it satisfies. -/
theorem isIntegral_div_of_homog (d : ℤ) (hd : d ≠ 0) (w cs : P1) (h : ev8 (homog d w (cs ++ [1])) = 0) :
    IsIntegral ℤ (ev8 w / d) := by
  have hd' : (d : L8) ≠ 0 := Int.cast_ne_zero.mpr hd
  refine ⟨toPoly (cs ++ [1]), toPoly_monic cs, ?_⟩
  rw [← aeval_def, aeval_toPoly]
  have h2 := eval_homog a d hd' w (cs ++ [1]) (by simp)
  rw [show P1.eval a (homog d w (cs ++ [1])) = ev8 (homog d w (cs ++ [1])) from rfl, h] at h2
  exact (mul_eq_zero.mp h2.symm).resolve_left (pow_ne_zero _ hd')

/-! ## The integral basis of `L₈` -/

/-- Numerators `W_k` of the integral basis `ω_k = W_k(a)/820` of `L₈`. -/
def Wω : List P1 :=
  [[820], [0, 820], [0, 0, 820], [0, 0, 0, 820], [0, 0, 0, 0, 410], [0, 410, 0, 0, 0, 205],
    [0, 0, 410, 0, 0, 0, 205], [220, 190, 380, 490, 130, 109, 176, 1]]

/-- `∑ n_k W_k`, so that `ev8 (wsum n Wω) / 820 = ∑ n_k ω_k`. -/
def wsum : List ℤ → List P1 → P1
  | n :: ns, w :: ws => P1.add (P1.smul n w) (wsum ns ws)
  | _, _ => []

theorem isIntegral_intCast (n : ℤ) : IsIntegral ℤ (n : L8) := by
  simpa using (isIntegral_algebraMap (R := ℤ) (A := L8) (x := n))

theorem isIntegral_wsum : ∀ (ns : List ℤ) (ws : List P1), (∀ w ∈ ws, IsIntegral ℤ (ev8 w / 820)) →
    IsIntegral ℤ (ev8 (wsum ns ws) / 820)
  | [], ws, _ => by simpa [wsum, ev8] using isIntegral_zero
  | n :: ns, [], _ => by simpa [wsum, ev8] using isIntegral_zero
  | n :: ns, w :: ws, hw => by
    have ih := isIntegral_wsum ns ws (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw'))
    have h0 := hw w List.mem_cons_self
    have e : ev8 (wsum (n :: ns) (w :: ws)) / 820 = (n : L8) * (ev8 w / 820) + ev8 (wsum ns ws) / 820 := by
      simp only [wsum, ev8, P1.eval_add, P1.eval_smul]
      ring
    rw [e]
    exact ((isIntegral_intCast n).mul h0).add ih

/-! ### The monic polynomials of the `ω_k`

`ω_isIntegral_of w cs k` takes the coefficients `cs = [c₀, …, c₇]` of the characteristic polynomial (monic of degree 8)
of `w(a)/820` and the quotient `k` of `homog 820 w (cs ++ [1])` by `h` (the instances are in `Omega.lean`). -/

theorem ω_isIntegral_of (w cs k : P1)
    (hc : P1.isZero (P1.sub (P1.smul 1 (P1.sub (homog 820 w (cs ++ [1])) [])) (P1.mul k hP1)) = true) :
    IsIntegral ℤ (ev8 w / 820) := by
  have := isIntegral_div_of_homog 820 (by norm_num) w cs
    (by rw [ev8_eq_of_cert _ [] k 1 one_ne_zero hc]; rfl)
  simpa using this

/-! ## Linear forms over `L₈`: the relative cubic -/

/-- `25 · T` for `X = x₀ + x₁ b + x₂ b²`. -/
def Tf {R : Type*} [CommRing R] (x₀ x₁ x₂ : R) : R := 75 * x₀ - 20 * x₁ - 12 * x₂

/-- `625 · S`. -/
def Sf {R : Type*} [CommRing R] (x₀ x₁ x₂ : R) : R :=
  1875 * x₀ ^ 2 - 1000 * x₀ * x₁ - 600 * x₀ * x₂ + 350 * x₁ ^ 2 + 770 * x₁ * x₂ - 364 * x₂ ^ 2

/-- `625 · N`, `N = N_{L₂₄/L₈}(X)`. -/
def Nf {R : Type*} [CommRing R] (x₀ x₁ x₂ : R) : R :=
  625 * x₀ ^ 3 - 500 * x₀ ^ 2 * x₁ - 300 * x₀ ^ 2 * x₂ + 350 * x₀ * x₁ ^ 2 + 770 * x₀ * x₁ * x₂ -
    364 * x₀ * x₂ ^ 2 - 350 * x₁ ^ 3 + 280 * x₁ ^ 2 * x₂ - 196 * x₁ * x₂ ^ 2 + 196 * x₂ ^ 3

theorem Tf_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x₀ x₁ x₂ : R) :
    f (Tf x₀ x₁ x₂) = Tf (f x₀) (f x₁) (f x₂) := by
  simp [Tf, map_sub, map_mul, map_ofNat]

theorem Sf_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x₀ x₁ x₂ : R) :
    f (Sf x₀ x₁ x₂) = Sf (f x₀) (f x₁) (f x₂) := by
  simp [Sf, map_sub, map_mul, map_add, map_pow, map_ofNat]

theorem Nf_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x₀ x₁ x₂ : R) :
    f (Nf x₀ x₁ x₂) = Nf (f x₀) (f x₁) (f x₂) := by
  simp [Nf, map_sub, map_mul, map_add, map_pow, map_ofNat]

theorem b_rel : 25 * b ^ 3 + 20 * b ^ 2 + 14 * b + 14 = 0 := by
  rw [← aeval_ψ_eq, b_root]

/-- The relative cubic: `X³ - T X² + S X - N = 0`. -/
theorem cubic_rel (x₀ x₁ x₂ : L24) :
    (x₀ + x₁ * b + x₂ * b ^ 2) ^ 3 - Tf x₀ x₁ x₂ / 25 * (x₀ + x₁ * b + x₂ * b ^ 2) ^ 2 +
      Sf x₀ x₁ x₂ / 625 * (x₀ + x₁ * b + x₂ * b ^ 2) - Nf x₀ x₁ x₂ / 625 = 0 := by
  simp only [Tf, Sf, Nf]
  linear_combination (b ^ 3 * x₂ ^ 3 / 25 + 3 * b ^ 2 * x₁ * x₂ ^ 2 / 25 - 4 * b ^ 2 * x₂ ^ 3 / 125 +
    3 * b * x₁ ^ 2 * x₂ / 25 - 8 * b * x₁ * x₂ ^ 2 / 125 + 14 * b * x₂ ^ 3 / 625 + x₁ ^ 3 / 25 -
    4 * x₁ ^ 2 * x₂ / 125 + 14 * x₁ * x₂ ^ 2 / 625 - 14 * x₂ ^ 3 / 625) * b_rel

/-- A root of a monic cubic with integral coefficients is integral. -/
theorem isIntegral_of_cubic (x t s n : L24) (ht : IsIntegral ℤ t) (hs : IsIntegral ℤ s) (hn : IsIntegral ℤ n)
    (h : x ^ 3 - t * x ^ 2 + s * x - n = 0) : IsIntegral ℤ x := by
  let R := integralClosure ℤ L24
  let p : R[X] := X ^ 3 - C ⟨t, ht⟩ * X ^ 2 + C ⟨s, hs⟩ * X - C ⟨n, hn⟩
  have hp : p.Monic := by
    simp only [p]
    monicity!
  have hx : IsIntegral R x := by
    refine ⟨p, hp, ?_⟩
    simp only [p, eval₂_sub, eval₂_add, eval₂_mul, eval₂_X_pow, eval₂_X, eval₂_C]
    exact h
  exact isIntegral_trans x hx

/-! ## The relative norm -/

theorem powerBasis24_dim : (AdjoinRoot.powerBasis ψL8_ne_zero).dim = 3 := by
  rw [AdjoinRoot.powerBasis_dim, ψL8_natDegree]

/-- The basis `1, b, b²` of `L₂₄` over `L₈`. -/
def basis3 : Module.Basis (Fin 3) L8 L24 :=
  (AdjoinRoot.powerBasis ψL8_ne_zero).basis.reindex (finCongr powerBasis24_dim)

theorem basis3_apply (i : Fin 3) : basis3 i = b ^ (i : ℕ) := by
  simp [basis3, Module.Basis.reindex_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen, b]

theorem basis3_repr (c : Fin 3 → L8) : ⇑(basis3.repr (∑ i, c i • basis3 i)) = c := by
  rw [← basis3.equivFun_symm_apply]
  exact basis3.equivFun.apply_symm_apply c

/-- `N_{L₂₄/L₈}(x₀ + x₁ b + x₂ b²) = N/625`, from the matrix of multiplication in the basis `1, b, b²`. -/
theorem norm_rel (x₀ x₁ x₂ : L8) :
    Algebra.norm L8 (algebraMap L8 L24 x₀ + algebraMap L8 L24 x₁ * b + algebraMap L8 L24 x₂ * b ^ 2) =
      Nf x₀ x₁ x₂ / 625 := by
  set X := algebraMap L8 L24 x₀ + algebraMap L8 L24 x₁ * b + algebraMap L8 L24 x₂ * b ^ 2 with hX
  let M : Matrix (Fin 3) (Fin 3) L8 :=
    !![x₀, -14 * x₂ / 25, -14 * x₁ / 25 + 56 * x₂ / 125;
       x₁, x₀ - 14 * x₂ / 25, -14 * x₁ / 25 - 14 * x₂ / 125;
       x₂, x₁ - 4 * x₂ / 5, x₀ - 4 * x₁ / 5 + 2 * x₂ / 25]
  have hsum : ∀ c₀ c₁ c₂ : L8, (∑ i, ![c₀, c₁, c₂] i • basis3 i) =
      algebraMap L8 L24 c₀ + algebraMap L8 L24 c₁ * b + algebraMap L8 L24 c₂ * b ^ 2 := by
    intro c₀ c₁ c₂
    simp only [Fin.sum_univ_three, basis3_apply, Algebra.smul_def, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.val_two,
      pow_zero, pow_one, mul_one]
  have hcol0 : X * basis3 0 = (∑ i, ![x₀, x₁, x₂] i • basis3 i) := by
    rw [hsum, basis3_apply, hX]
    simp
  have hcol1 : X * basis3 1 =
      (∑ i, ![-14 * x₂ / 25, x₀ - 14 * x₂ / 25, x₁ - 4 * x₂ / 5] i • basis3 i) := by
    rw [hsum, basis3_apply]
    simp only [hX, map_sub, map_mul, map_div₀, map_neg, map_ofNat, Fin.isValue, Fin.val_one, pow_one]
    linear_combination (algebraMap L8 L24 x₂ / 25) * b_rel
  have hcol2 : X * basis3 2 = (∑ i, ![-14 * x₁ / 25 + 56 * x₂ / 125, -14 * x₁ / 25 - 14 * x₂ / 125,
      x₀ - 4 * x₁ / 5 + 2 * x₂ / 25] i • basis3 i) := by
    rw [hsum, basis3_apply]
    simp only [hX, map_add, map_sub, map_mul, map_div₀, map_neg, map_ofNat, Fin.isValue, Fin.val_two]
    linear_combination (b * algebraMap L8 L24 x₂ / 25 + algebraMap L8 L24 x₁ / 25 -
      4 * algebraMap L8 L24 x₂ / 125) * b_rel
  have hM : Algebra.leftMulMatrix basis3 X = M := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
    · rw [hcol0, basis3_repr]; fin_cases i <;> rfl
    · rw [hcol1, basis3_repr]; fin_cases i <;> rfl
    · rw [hcol2, basis3_repr]; fin_cases i <;> rfl
  rw [Algebra.norm_eq_matrix_det basis3, hM, Matrix.det_fin_three]
  simp [M, Nf]
  ring

/-! ## Elements of `L₂₄` given by integer polynomials -/

theorem P1_eval_ringHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    ∀ p : P1, P1.eval (f x) p = f (P1.eval x p)
  | [] => by simp
  | c :: p => by simp [P1_eval_ringHom f x p]

theorem ev_three (N₀ N₁ N₂ : P1) :
    ev [N₀, N₁, N₂] = algebraMap L8 L24 (ev8 N₀) + algebraMap L8 L24 (ev8 N₁) * b +
      algebraMap L8 L24 (ev8 N₂) * b ^ 2 := by
  simp only [ev, P2.eval_cons, P2.eval_nil, aL24, P1_eval_ringHom, ev8]
  ring

/-- The `k`-th row (coefficient of `b^k`) of a bivariate polynomial. -/
def row (P : P2) (k : ℕ) : P1 := P.getD k []

theorem ev_rows (P : P2) (hP : P = [row P 0, row P 1, row P 2]) :
    ev P = algebraMap L8 L24 (ev8 (row P 0)) + algebraMap L8 L24 (ev8 (row P 1)) * b +
      algebraMap L8 L24 (ev8 (row P 2)) * b ^ 2 := by
  rw [← ev_three, ← hP]

/-- `25 T` on integer polynomials. -/
def T25p (N₀ N₁ N₂ : P1) : P1 :=
  P1.add (P1.smul 75 N₀) (P1.add (P1.smul (-20) N₁) (P1.smul (-12) N₂))

/-- `625 S` on integer polynomials. -/
def S625p (N₀ N₁ N₂ : P1) : P1 :=
  P1.add (P1.smul 1875 (P1.mul N₀ N₀)) <| P1.add (P1.smul (-1000) (P1.mul N₀ N₁)) <|
  P1.add (P1.smul (-600) (P1.mul N₀ N₂)) <| P1.add (P1.smul 350 (P1.mul N₁ N₁)) <|
  P1.add (P1.smul 770 (P1.mul N₁ N₂)) (P1.smul (-364) (P1.mul N₂ N₂))

/-- `625 N` on integer polynomials. -/
def N625p (N₀ N₁ N₂ : P1) : P1 :=
  let N₀₀ := P1.mul N₀ N₀
  let N₁₁ := P1.mul N₁ N₁
  let N₂₂ := P1.mul N₂ N₂
  P1.add (P1.smul 625 (P1.mul N₀₀ N₀)) <| P1.add (P1.smul (-500) (P1.mul N₀₀ N₁)) <|
  P1.add (P1.smul (-300) (P1.mul N₀₀ N₂)) <| P1.add (P1.smul 350 (P1.mul N₀ N₁₁)) <|
  P1.add (P1.smul 770 (P1.mul (P1.mul N₀ N₁) N₂)) <| P1.add (P1.smul (-364) (P1.mul N₀ N₂₂)) <|
  P1.add (P1.smul (-350) (P1.mul N₁₁ N₁)) <| P1.add (P1.smul 280 (P1.mul N₁₁ N₂)) <|
  P1.add (P1.smul (-196) (P1.mul N₁ N₂₂)) (P1.smul 196 (P1.mul N₂₂ N₂))

theorem ev8_T25p (N₀ N₁ N₂ : P1) : ev8 (T25p N₀ N₁ N₂) = Tf (ev8 N₀) (ev8 N₁) (ev8 N₂) := by
  simp only [T25p, Tf, ev8, P1.eval_add, P1.eval_smul]
  push_cast
  ring

theorem ev8_S625p (N₀ N₁ N₂ : P1) : ev8 (S625p N₀ N₁ N₂) = Sf (ev8 N₀) (ev8 N₁) (ev8 N₂) := by
  simp only [S625p, Sf, ev8, P1.eval_add, P1.eval_smul, P1.eval_mul]
  push_cast
  ring

theorem ev8_N625p (N₀ N₁ N₂ : P1) : ev8 (N625p N₀ N₁ N₂) = Nf (ev8 N₀) (ev8 N₁) (ev8 N₂) := by
  simp only [N625p, Nf, ev8, P1.eval_add, P1.eval_smul, P1.eval_mul]
  push_cast
  ring

theorem elem_eq (P : P2) (hP : P = [row P 0, row P 1, row P 2]) (d : ℕ) :
    ev P / (d : L24) = algebraMap L8 L24 (ev8 (row P 0) / d) + algebraMap L8 L24 (ev8 (row P 1) / d) * b +
      algebraMap L8 L24 (ev8 (row P 2) / d) * b ^ 2 := by
  rw [ev_rows P hP]
  simp only [map_div₀, map_natCast]
  ring

/-- The relative norm `N_{L₂₄/L₈}(P(a, b)/d) = (625 N)(a)/(625 d³)`. -/
theorem elem_norm (P : P2) (hP : P = [row P 0, row P 1, row P 2]) (d : ℕ) (hd : d ≠ 0) :
    Algebra.norm L8 (ev P / (d : L24)) = ev8 (N625p (row P 0) (row P 1) (row P 2)) / (625 * (d : L8) ^ 3) := by
  have hd' : (d : L8) ≠ 0 := Nat.cast_ne_zero.mpr hd
  rw [elem_eq P hP, norm_rel, ev8_N625p]
  simp only [Nf]
  field_simp

/-- Integrality of `P(a, b)/d` from the `ω`-coordinates `nT, nS, nN` of the coefficients `T, S, N` of its relative
characteristic polynomial (each hypothesis is an identity in `L₈`, proved by an `ev8` certificate). -/
theorem elem_isIntegral (P : P2) (hP : P = [row P 0, row P 1, row P 2]) (d : ℕ) (hd : d ≠ 0)
    (nT nS nN : List ℤ)
    (hT : ev8 (P1.smul 820 (T25p (row P 0) (row P 1) (row P 2))) = ev8 (P1.smul (25 * d) (wsum nT Wω)))
    (hS : ev8 (P1.smul 820 (S625p (row P 0) (row P 1) (row P 2))) = ev8 (P1.smul (625 * d ^ 2) (wsum nS Wω)))
    (hN : ev8 (P1.smul 820 (N625p (row P 0) (row P 1) (row P 2))) = ev8 (P1.smul (625 * d ^ 3) (wsum nN Wω)))
    (hω : ∀ w ∈ Wω, IsIntegral ℤ (ev8 w / 820)) :
    IsIntegral ℤ (ev P / (d : L24)) := by
  have hd' : (d : L8) ≠ 0 := Nat.cast_ne_zero.mpr hd
  set x₀ := ev8 (row P 0) / d
  set x₁ := ev8 (row P 1) / d
  set x₂ := ev8 (row P 2) / d
  rw [elem_eq P hP]
  have hsm : ∀ (c : ℤ) (p : P1), ev8 (P1.smul c p) = c * ev8 p := fun c p => P1.eval_smul a c p
  rw [hsm, hsm, ev8_T25p] at hT
  rw [hsm, hsm, ev8_S625p] at hS
  rw [hsm, hsm, ev8_N625p] at hN
  have eT : Tf x₀ x₁ x₂ / 25 = ev8 (wsum nT Wω) / 820 := by
    simp only [x₀, x₁, x₂, Tf, ev8] at hT ⊢
    push_cast at hT
    field_simp
    linear_combination hT
  have eS : Sf x₀ x₁ x₂ / 625 = ev8 (wsum nS Wω) / 820 := by
    simp only [x₀, x₁, x₂, Sf, ev8] at hS ⊢
    push_cast at hS
    field_simp
    linear_combination hS
  have eN : Nf x₀ x₁ x₂ / 625 = ev8 (wsum nN Wω) / 820 := by
    simp only [x₀, x₁, x₂, Nf, ev8] at hN ⊢
    push_cast at hN
    field_simp
    linear_combination hN
  have iT := (isIntegral_wsum nT Wω hω).map (IsScalarTower.toAlgHom ℤ L8 L24)
  have iS := (isIntegral_wsum nS Wω hω).map (IsScalarTower.toAlgHom ℤ L8 L24)
  have iN := (isIntegral_wsum nN Wω hω).map (IsScalarTower.toAlgHom ℤ L8 L24)
  rw [← eT] at iT
  rw [← eS] at iS
  rw [← eN] at iN
  simp only [IsScalarTower.coe_toAlgHom', map_div₀, map_ofNat] at iT iS iN
  refine isIntegral_of_cubic _ _ _ _ iT iS iN ?_
  have := cubic_rel (algebraMap L8 L24 x₀) (algebraMap L8 L24 x₁) (algebraMap L8 L24 x₂)
  rw [Tf_map, Sf_map, Nf_map]
  exact this

/-! ## Norms from `L₈` to `ℚ` -/

theorem powerBasis8_dim : (AdjoinRoot.powerBasis h_ne_zero).dim = 8 := by
  rw [AdjoinRoot.powerBasis_dim, h_natDegree]

/-- The basis `1, a, …, a⁷` of `L₈` over `ℚ`. -/
def basis8 : Module.Basis (Fin 8) ℚ L8 :=
  (AdjoinRoot.powerBasis h_ne_zero).basis.reindex (finCongr powerBasis8_dim)

theorem basis8_apply (i : Fin 8) : basis8 i = a ^ (i : ℕ) := by
  simp [basis8, Module.Basis.reindex_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen, a]

theorem basis8_repr (c : Fin 8 → ℚ) : ⇑(basis8.repr (∑ i, c i • basis8 i)) = c := by
  rw [← basis8.equivFun_symm_apply]
  exact basis8.equivFun.apply_symm_apply c

/-- The coefficients `h₀, …, h₇` of `h = x⁸ + h₇ x⁷ + … + h₀`. -/
def hF : Fin 8 → ℤ := ![-940, -480, 840, 560, -140, -168, -28, 4]

/-- `∑ cᵢ aⁱ`. -/
def evF (c : Fin 8 → ℤ) : L8 := ∑ i, (c i : L8) * a ^ (i : ℕ)

/-- Multiplication by `a` on coefficient vectors (reduction by `h`). -/
def mulxF (c : Fin 8 → ℤ) : Fin 8 → ℤ := fun i => (if i = 0 then 0 else c (i - 1)) - c 7 * hF i

theorem a_rel : a ^ 8 + 4 * a ^ 7 - 28 * a ^ 6 - 168 * a ^ 5 - 140 * a ^ 4 + 560 * a ^ 3 + 840 * a ^ 2 -
    480 * a - 940 = 0 := by
  rw [← P1_eval_hP1, show P1.eval a hP1 = ev8 hP1 from rfl, ev8_hP1]

theorem evF_mulxF (c : Fin 8 → ℤ) : evF (mulxF c) = a * evF c := by
  simp only [evF, mulxF, Fin.sum_univ_eight, hF]
  simp
  linear_combination (-(c 7 : L8)) * a_rel

/-- The columns of the multiplication matrix: `colF v k` are the coefficients of `aᵏ · evF v`. -/
def colF (v : Fin 8 → ℤ) (k : ℕ) : Fin 8 → ℤ := mulxF^[k] v

theorem evF_colF (v : Fin 8 → ℤ) : ∀ k : ℕ, evF (colF v k) = a ^ k * evF v
  | 0 => by simp [colF]
  | k + 1 => by
    rw [colF, Function.iterate_succ_apply', ← colF, evF_mulxF, evF_colF v k]
    ring

/-- The integer matrix `M` with `M i k = colF v k i`: `820⁻¹ M` is the matrix of multiplication by `evF v / 820`. -/
def mulMat (v : Fin 8 → ℤ) : Matrix (Fin 8) (Fin 8) ℤ := Matrix.of fun i k => colF v k i

theorem leftMulMatrix_evF (v : Fin 8 → ℤ) :
    Algebra.leftMulMatrix basis8 (evF v / 820) =
      (1 / 820 : ℚ) • (mulMat v).map (Int.cast : ℤ → ℚ) := by
  ext i k
  rw [Algebra.leftMulMatrix_eq_repr_mul, basis8_apply]
  have e : evF v / 820 * a ^ (k : ℕ) = ∑ i, ((1 / 820 : ℚ) * (mulMat v i k : ℚ)) • basis8 i := by
    rw [div_mul_eq_mul_div, mul_comm, ← evF_colF, evF]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [basis8_apply, Algebra.smul_def, mulMat]
    simp only [map_mul, map_div₀, map_one, map_ofNat, map_intCast, Matrix.of_apply]
    ring
  rw [e, basis8_repr]
  simp [Matrix.smul_apply, Matrix.map_apply]

/-- The norm `N_{L₈/ℚ}(evF v / 820)` from an LU certificate for `det M`. -/
theorem norm_evF (v : Fin 8 → ℤ) (value : ℤ) (C : LU.Certificate (mulMat v) value) :
    Algebra.norm ℚ (evF v / 820) = value / 820 ^ 8 := by
  rw [Algebra.norm_eq_matrix_det basis8, leftMulMatrix_evF, Matrix.det_smul]
  rw [show (mulMat v).map (Int.cast : ℤ → ℚ) = fun i j => ((mulMat v i j : ℤ) : ℚ) from rfl, C.determinant]
  simp only [Fintype.card_fin]
  ring

theorem ev8_ofFn (v : Fin 8 → ℤ) : ev8 (List.ofFn v) = evF v := by
  simp only [ev8, evF, List.ofFn_succ, List.ofFn_zero, P1.eval_cons, P1.eval_nil, Fin.sum_univ_eight]
  simp
  ring

/-- Products of lists of polynomials. -/
def prodList : List P1 → P1
  | [] => [1]
  | p :: ps => P1.mul p (prodList ps)

theorem ev8_prodList : ∀ ps : List P1, ev8 (prodList ps) = (ps.map ev8).prod
  | [] => by simp [prodList, ev8]
  | p :: ps => by simp [prodList, ev8_mul, ev8_prodList ps]

theorem ev_prodList2 : ∀ ps : List P2, ev (ps.foldr P2.mul [[1]]) = (ps.map ev).prod
  | [] => by simp [ev, P2.eval, P1.eval]
  | p :: ps => by simp [ev_mul, ev_prodList2 ps]

/-- The relative norm `N_{L₂₄/L₈}(P(a, b)/d) = evF v / 820`, from the certificate `hN` of `elem_isIntegral` and
`wsum nN Wω = v`. -/
theorem elem_norm_evF (P : P2) (hP : P = [row P 0, row P 1, row P 2]) (d : ℕ) (hd : d ≠ 0) (nN : List ℤ)
    (hN : ev8 (P1.smul 820 (N625p (row P 0) (row P 1) (row P 2))) = ev8 (P1.smul (625 * d ^ 3) (wsum nN Wω)))
    (v : Fin 8 → ℤ) (hv : wsum nN Wω = List.ofFn v) :
    Algebra.norm L8 (ev P / (d : L24)) = evF v / 820 := by
  have hd' : (d : L8) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hsm : ∀ (c : ℤ) (p : P1), ev8 (P1.smul c p) = c * ev8 p := fun c p => P1.eval_smul a c p
  rw [elem_norm P hP d hd, ← ev8_ofFn, ← hv]
  rw [hsm, hsm] at hN
  push_cast at hN
  field_simp
  linear_combination hN

end Integral

end

end X2Y5Z7
