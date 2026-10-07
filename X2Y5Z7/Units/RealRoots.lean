module

public import X2Y5Z7.Fields.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

/-! # The real roots of `h` and `ψ`

* `h` has at most two real roots: `h ≤ -1/16` on `[-15/4, 21/4]`, `h` is strictly decreasing on
  `(-∞, -15/4]` and strictly increasing on `[21/4, ∞)`, so each of these two half-lines holds at most one
  root. It has a real root in `(21/4, 6)`, by the intermediate value theorem.
* `ψ` is strictly increasing on `ℝ` (`ψ' = 75t² + 40t + 14 > 0`), so it has at most one real root; it has
  one in `(-1, 0)`.

The bound on `[-15/4, 21/4]` is proved on the four pieces `[-15/4, -7/4]`, `[-7/4, 0]`, `[0, 11/8]`,
`[11/8, 21/4]`: on a piece `[u, v]`, `h + 1/16` is a combination with nonpositive coefficients of the
Bernstein polynomials `(x - u)ⁱ (v - x)⁸⁻ⁱ`. For the monotonicity: as polynomials in `s`, `h(-15/4 - s)` and
`h(21/4 + s)` have positive coefficients in every positive degree. The coefficients were computed in exact
rational arithmetic; `ring` checks each identity. -/

namespace X2Y5Z7

open Polynomial

/-! ## Evaluating `h` and `ψ` -/

/-- `h` evaluated in a `ℚ`-algebra. -/
theorem aeval_h {A : Type*} [CommRing A] [Algebra ℚ A] (x : A) :
    aeval x h = x^8 + 4*x^7 - 28*x^6 - 168*x^5 - 140*x^4 + 560*x^3 + 840*x^2 - 480*x - 940 := by
  simp [h, hZ, map_ofNat]

/-- `ψ` evaluated in a `ℚ`-algebra. -/
theorem aeval_ψ {A : Type*} [CommRing A] [Algebra ℚ A] (x : A) :
    aeval x ψ = 25*x^3 + 20*x^2 + 14*x + 14 := by
  simp [ψ, ψZ, map_ofNat]

/-! ## The real roots of `h` -/

/-- `h` as a function on `ℝ`. -/
private def hPoly (x : ℝ) : ℝ :=
  x^8 + 4*x^7 - 28*x^6 - 168*x^5 - 140*x^4 + 560*x^3 + 840*x^2 - 480*x - 940

private theorem aeval_h_real (x : ℝ) : aeval x h = hPoly x := aeval_h x

private theorem hPoly_le_piece1 (x : ℝ) (h1 : -15/4 ≤ x) (h2 : x ≤ -7/4) :
    hPoly x ≤ -1/16 := by
  have hA : 0 ≤ (x + 15/4) := by linarith
  have hB : 0 ≤ (-7/4 - x) := by linarith
  have hS : 0 ≤
      (28310319/16777216) * ((-7/4 - x)^8) +
      (40006839/2097152) * ((x + 15/4) * (-7/4 - x)^7) +
      (110414073/4194304) * ((x + 15/4)^2 * (-7/4 - x)^6) +
      (35073073/2097152) * ((x + 15/4)^3 * (-7/4 - x)^5) +
      (130724685/8388608) * ((x + 15/4)^4 * (-7/4 - x)^4) +
      (25443425/2097152) * ((x + 15/4)^5 * (-7/4 - x)^3) +
      (14435673/4194304) * ((x + 15/4)^6 * (-7/4 - x)^2) +
      (232359/2097152) * ((x + 15/4)^7 * (-7/4 - x)) +
      (109679/16777216) * ((x + 15/4)^8) := by positivity
  have key : hPoly x = -1/16 - (
      (28310319/16777216) * ((-7/4 - x)^8) +
      (40006839/2097152) * ((x + 15/4) * (-7/4 - x)^7) +
      (110414073/4194304) * ((x + 15/4)^2 * (-7/4 - x)^6) +
      (35073073/2097152) * ((x + 15/4)^3 * (-7/4 - x)^5) +
      (130724685/8388608) * ((x + 15/4)^4 * (-7/4 - x)^4) +
      (25443425/2097152) * ((x + 15/4)^5 * (-7/4 - x)^3) +
      (14435673/4194304) * ((x + 15/4)^6 * (-7/4 - x)^2) +
      (232359/2097152) * ((x + 15/4)^7 * (-7/4 - x)) +
      (109679/16777216) * ((x + 15/4)^8)) := by unfold hPoly; ring
  linarith

private theorem hPoly_le_piece2 (x : ℝ) (h1 : -7/4 ≤ x) (h2 : x ≤ 0) :
    hPoly x ≤ -1/16 := by
  have hA : 0 ≤ (x + 7/4) := by linarith
  have hB : 0 ≤ (-x) := by linarith
  have hS : 0 ≤
      (109679/5764801) * ((-x)^8) +
      (18672/5764801) * ((x + 7/4) * (-x)^7) +
      (4808256/823543) * ((x + 7/4)^2 * (-x)^6) +
      (40199680/823543) * ((x + 7/4)^3 * (-x)^5) +
      (132264960/823543) * ((x + 7/4)^4 * (-x)^4) +
      (211238912/823543) * ((x + 7/4)^5 * (-x)^3) +
      (167264256/823543) * ((x + 7/4)^6 * (-x)^2) +
      (437747712/5764801) * ((x + 7/4)^7 * (-x)) +
      (61599744/5764801) * ((x + 7/4)^8) := by positivity
  have key : hPoly x = -1/16 - (
      (109679/5764801) * ((-x)^8) +
      (18672/5764801) * ((x + 7/4) * (-x)^7) +
      (4808256/823543) * ((x + 7/4)^2 * (-x)^6) +
      (40199680/823543) * ((x + 7/4)^3 * (-x)^5) +
      (132264960/823543) * ((x + 7/4)^4 * (-x)^4) +
      (211238912/823543) * ((x + 7/4)^5 * (-x)^3) +
      (167264256/823543) * ((x + 7/4)^6 * (-x)^2) +
      (437747712/5764801) * ((x + 7/4)^7 * (-x)) +
      (61599744/5764801) * ((x + 7/4)^8)) := by unfold hPoly; ring
  linarith

private theorem hPoly_le_piece3 (x : ℝ) (h1 : 0 ≤ x) (h2 : x ≤ 11/8) :
    hPoly x ≤ -1/16 := by
  have hA : 0 ≤ x := by linarith
  have hB : 0 ≤ (11/8 - x) := by linarith
  have hS : 0 ≤
      (15769534464/214358881) * ((11/8 - x)^8) +
      (137229238272/214358881) * (x * (11/8 - x)^7) +
      (492413386752/214358881) * (x^2 * (11/8 - x)^6) +
      (931336290304/214358881) * (x^3 * (11/8 - x)^5) +
      (978032312320/214358881) * (x^4 * (11/8 - x)^4) +
      (540957634560/214358881) * (x^5 * (11/8 - x)^3) +
      (125282807552/214358881) * (x^6 * (11/8 - x)^2) +
      (2548848032/214358881) * (x^7 * (11/8 - x)) +
      (359611199/214358881) * (x^8) := by positivity
  have key : hPoly x = -1/16 - (
      (15769534464/214358881) * ((11/8 - x)^8) +
      (137229238272/214358881) * (x * (11/8 - x)^7) +
      (492413386752/214358881) * (x^2 * (11/8 - x)^6) +
      (931336290304/214358881) * (x^3 * (11/8 - x)^5) +
      (978032312320/214358881) * (x^4 * (11/8 - x)^4) +
      (540957634560/214358881) * (x^5 * (11/8 - x)^3) +
      (125282807552/214358881) * (x^6 * (11/8 - x)^2) +
      (2548848032/214358881) * (x^7 * (11/8 - x)) +
      (359611199/214358881) * (x^8)) := by unfold hPoly; ring
  linarith

private theorem hPoly_le_piece4 (x : ℝ) (h1 : 11/8 ≤ x) (h2 : x ≤ 21/4) :
    hPoly x ≤ -1/16 := by
  have hA : 0 ≤ (x - 11/8) := by linarith
  have hB : 0 ≤ (21/4 - x) := by linarith
  have hS : 0 ≤
      (359611199/852891037441) * ((21/4 - x)^8) +
      (3801370352/852891037441) * ((x - 11/8) * (21/4 - x)^7) +
      (949822259792/852891037441) * ((x - 11/8)^2 * (21/4 - x)^6) +
      (9608801525568/852891037441) * ((x - 11/8)^3 * (21/4 - x)^5) +
      (39483733209760/852891037441) * ((x - 11/8)^4 * (21/4 - x)^4) +
      (82117249118464/852891037441) * ((x - 11/8)^5 * (21/4 - x)^3) +
      (87756524174592/852891037441) * ((x - 11/8)^6 * (21/4 - x)^2) +
      (41425913367552/852891037441) * ((x - 11/8)^7 * (21/4 - x)) +
      (4112435089152/852891037441) * ((x - 11/8)^8) := by positivity
  have key : hPoly x = -1/16 - (
      (359611199/852891037441) * ((21/4 - x)^8) +
      (3801370352/852891037441) * ((x - 11/8) * (21/4 - x)^7) +
      (949822259792/852891037441) * ((x - 11/8)^2 * (21/4 - x)^6) +
      (9608801525568/852891037441) * ((x - 11/8)^3 * (21/4 - x)^5) +
      (39483733209760/852891037441) * ((x - 11/8)^4 * (21/4 - x)^4) +
      (82117249118464/852891037441) * ((x - 11/8)^5 * (21/4 - x)^3) +
      (87756524174592/852891037441) * ((x - 11/8)^6 * (21/4 - x)^2) +
      (41425913367552/852891037441) * ((x - 11/8)^7 * (21/4 - x)) +
      (4112435089152/852891037441) * ((x - 11/8)^8)) := by unfold hPoly; ring
  linarith

/-- `h ≤ -1/16` on `[-15/4, 21/4]`. -/
theorem h_real_le_of_mem (x : ℝ) (h1 : -15/4 ≤ x) (h2 : x ≤ 21/4) : aeval x h ≤ -1/16 := by
  rw [aeval_h_real]
  rcases le_total x (-7/4) with h3 | h3
  · exact hPoly_le_piece1 x h1 h3
  rcases le_total x 0 with h4 | h4
  · exact hPoly_le_piece2 x h3 h4
  rcases le_total x (11/8) with h5 | h5
  · exact hPoly_le_piece3 x h4 h5
  · exact hPoly_le_piece4 x h5 h2

/-- A polynomial of degree at most 8 whose coefficients in positive degree are nonnegative, the linear one
positive, is strictly increasing on `[0, ∞)`. -/
private theorem poly8_lt {c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : ℝ} (h₁ : 0 < c₁) (h₂ : 0 ≤ c₂) (h₃ : 0 ≤ c₃)
    (h₄ : 0 ≤ c₄) (h₅ : 0 ≤ c₅) (h₆ : 0 ≤ c₆) (h₇ : 0 ≤ c₇) (h₈ : 0 ≤ c₈) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s < t) :
    c₀ + c₁*s + c₂*s^2 + c₃*s^3 + c₄*s^4 + c₅*s^5 + c₆*s^6 + c₇*s^7 + c₈*s^8 <
      c₀ + c₁*t + c₂*t^2 + c₃*t^3 + c₄*t^4 + c₅*t^5 + c₆*t^6 + c₇*t^7 + c₈*t^8 := by
  have p₁ := mul_lt_mul_of_pos_left hst h₁
  have p₂ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hst.le 2) h₂
  have p₃ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hst.le 3) h₃
  have p₄ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hst.le 4) h₄
  have p₅ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hst.le 5) h₅
  have p₆ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hst.le 6) h₆
  have p₇ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hst.le 7) h₇
  have p₈ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hst.le 8) h₈
  linarith

/-- `h` is strictly decreasing on `(-∞, -15/4]`. -/
theorem h_real_strictAntiOn : StrictAntiOn (fun x : ℝ => aeval x h) (Set.Iic (-15/4)) := by
  intro x _ y hy hxy
  simp only [aeval_h_real]
  have e : ∀ z : ℝ, hPoly z = -28314415/65536 + 1462065/2048 * (-15/4 - z) +
      3929835/1024 * (-15/4 - z)^2 + 675395/128 * (-15/4 - z)^3 + 456155/128 * (-15/4 - z)^4 +
      10479/8 * (-15/4 - z)^5 + 1043/4 * (-15/4 - z)^6 + 26 * (-15/4 - z)^7 + 1 * (-15/4 - z)^8 := by
    intro z; unfold hPoly; ring
  rw [e x, e y]
  exact poly8_lt (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by simp only [Set.mem_Iic] at hy; linarith) (by linarith)

/-- `h` is strictly increasing on `[21/4, ∞)`. -/
theorem h_real_strictMonoOn : StrictMonoOn (fun x : ℝ => aeval x h) (Set.Ici (21/4)) := by
  intro x hx y _ hxy
  simp only [aeval_h_real]
  have e : ∀ z : ℝ, hPoly z = -16064203663/65536 + 268599819/2048 * (z - 21/4) +
      353947251/1024 * (z - 21/4)^2 + 25598377/128 * (z - 21/4)^3 + 7335755/128 * (z - 21/4)^4 +
      74949/8 * (z - 21/4)^5 + 3563/4 * (z - 21/4)^6 + 46 * (z - 21/4)^7 + 1 * (z - 21/4)^8 := by
    intro z; unfold hPoly; ring
  rw [e x, e y]
  exact poly8_lt (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by simp only [Set.mem_Ici] at hx; linarith) (by linarith)

/-- Every real root of `h` lies in `(-∞, -15/4)` or in `(21/4, ∞)`. -/
theorem h_real_root_lt_or_gt {x : ℝ} (hx : aeval x h = 0) : x < -15/4 ∨ 21/4 < x := by
  rcases lt_or_ge x (-15/4) with h1 | h1
  · exact Or.inl h1
  rcases lt_or_ge (21/4) x with h2 | h2
  · exact Or.inr h2
  have := h_real_le_of_mem x h1 h2
  linarith

/-- Two real roots of `h` on the same side of `0` are equal. -/
theorem h_real_root_eq {x y : ℝ} (hx : aeval x h = 0) (hy : aeval y h = 0) (hxy : x < 0 ↔ y < 0) :
    x = y := by
  rcases h_real_root_lt_or_gt hx with hx' | hx' <;> rcases h_real_root_lt_or_gt hy with hy' | hy'
  · exact h_real_strictAntiOn.injOn (Set.mem_Iic.2 hx'.le) (Set.mem_Iic.2 hy'.le) (hx.trans hy.symm)
  · exact absurd (hxy.1 (by linarith)) (by linarith)
  · exact absurd (hxy.2 (by linarith)) (by linarith)
  · exact h_real_strictMonoOn.injOn (Set.mem_Ici.2 hx'.le) (Set.mem_Ici.2 hy'.le) (hx.trans hy.symm)

/-- `h` has at most two real roots. -/
theorem card_h_real_roots_le : Nat.card {x : ℝ // aeval x h = 0} ≤ 2 := by
  have hinj : Function.Injective (fun x : {x : ℝ // aeval x h = 0} => decide (x.1 < 0)) := by
    intro x y hxy
    exact Subtype.ext (h_real_root_eq x.2 y.2 (by simpa using hxy))
  calc Nat.card {x : ℝ // aeval x h = 0} ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
    _ = 2 := by simp

/-- `h` has a real root, in `(21/4, 6)`. -/
theorem exists_h_real_root : ∃ x : ℝ, 21/4 < x ∧ x < 6 ∧ aeval x h = 0 := by
  have hc : Continuous hPoly := by unfold hPoly; fun_prop
  have h0 : (0 : ℝ) ∈ Set.Icc (hPoly (21/4)) (hPoly 6) := by
    constructor <;> norm_num [hPoly]
  obtain ⟨x, ⟨hx1, hx2⟩, hx⟩ := intermediate_value_Icc (by norm_num) hc.continuousOn h0
  refine ⟨x, ?_, ?_, by rw [aeval_h_real, hx]⟩
  · rcases hx1.lt_or_eq with hlt | heq
    · exact hlt
    · rw [← heq] at hx; norm_num [hPoly] at hx
  · rcases hx2.lt_or_eq with hlt | heq
    · exact hlt
    · rw [heq] at hx; norm_num [hPoly] at hx

/-! ## The real root of `ψ` -/

/-- `ψ` is strictly increasing on `ℝ`. -/
theorem ψ_real_strictMono : StrictMono (fun x : ℝ => aeval x ψ) := by
  intro x y hxy
  simp only [aeval_ψ]
  have key : 25*y^3 + 20*y^2 + 14*y + 14 - (25*x^3 + 20*x^2 + 14*x + 14) =
      (y - x) * (75/4 * (x + y + 8/15)^2 + 25/4 * (x - y)^2 + 26/3) := by ring
  have : 0 < (y - x) * (75/4 * (x + y + 8/15)^2 + 25/4 * (x - y)^2 + 26/3) := by
    apply mul_pos (by linarith); positivity
  linarith

/-- Two real roots of `ψ` are equal. -/
theorem ψ_real_root_eq {x y : ℝ} (hx : aeval x ψ = 0) (hy : aeval y ψ = 0) : x = y :=
  ψ_real_strictMono.injective (hx.trans hy.symm)

/-- `ψ` has at most one real root. -/
theorem card_ψ_real_roots_le : Nat.card {x : ℝ // aeval x ψ = 0} ≤ 1 := by
  have hinj : Function.Injective (fun _ : {x : ℝ // aeval x ψ = 0} => ()) :=
    fun x y _ => Subtype.ext (ψ_real_root_eq x.2 y.2)
  calc Nat.card {x : ℝ // aeval x ψ = 0} ≤ Nat.card Unit := Nat.card_le_card_of_injective _ hinj
    _ = 1 := by simp

/-- `ψ` has a real root, in `(-1, 0)`. -/
theorem exists_ψ_real_root : ∃ x : ℝ, -1 < x ∧ x < 0 ∧ aeval x ψ = 0 := by
  have hc : Continuous (fun x : ℝ => 25*x^3 + 20*x^2 + 14*x + 14) := by fun_prop
  have h0 : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => 25*x^3 + 20*x^2 + 14*x + 14) (-1))
      ((fun x : ℝ => 25*x^3 + 20*x^2 + 14*x + 14) 0) := by
    constructor <;> norm_num
  obtain ⟨x, ⟨hx1, hx2⟩, hx⟩ := intermediate_value_Icc (by norm_num) hc.continuousOn h0
  refine ⟨x, ?_, ?_, by rw [aeval_ψ]; exact hx⟩
  · rcases hx1.lt_or_eq with hlt | heq
    · exact hlt
    · rw [← heq] at hx; norm_num at hx
  · rcases hx2.lt_or_eq with hlt | heq
    · exact hlt
    · rw [heq] at hx; norm_num at hx

end X2Y5Z7
