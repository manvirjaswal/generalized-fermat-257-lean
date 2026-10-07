module

public import Mathlib

/-!
# The generalized Fermat equation x² + y⁵ = z⁷

The statements of Theorems 1.1 and 1.2 of

  Manvir Jaswal, *The generalized Fermat equation x² + y⁵ = z⁷*, preprint, version 2, Zenodo, 2026,
  https://doi.org/10.5281/zenodo.23223027,

with the definitions they use. This file imports only Mathlib. `Solution.lean` imports the proofs, and
Comparator checks that they prove exactly these statements using only the standard axioms.

Following Putz, a *solution* of (1.1) is a triple of integers `(X, Y, Z)` with `X⁵ + Y² = Z⁷`,
`gcd(X, Y, Z) = 1` and `XYZ ≠ 0`; it gives the solution `(x, y, z) = (Y, X, Z)` of `x² + y⁵ = z⁷`. Put
`η = X⁵/Z⁷`. The statements use:

* `h = x⁸ + 4x⁷ − 28x⁶ − 168x⁵ − 140x⁴ + 560x³ + 840x² − 480x − 940` and Putz's octic field
  `L8 = ℚ[x]/(h)`, as in (1.6);
* `ψ = 25t³ + 20t² + 14t + 14`, as in (1.2), and the field `L24 = L8[t]/(ψ)` of degree 24;
* `fpoly η = 4t⁵ψ(t) − η(4t − 1)`, the polynomial `f_η` of (1.5), so that
  `AdjoinRoot (fpoly η) = ℚ[t]/(f_η)` is the algebra `A_η`.

`L8` and `L24` are fields because `h` is irreducible over `ℚ` and `ψ` over `L8` (Lemma 2.4(a) and (c)).
These two facts, `h_irreducible` and `ψL8_irreducible`, are stated here and proved in `Solution`, like
the theorems.

The theorems take two hypotheses:

* `hclass`: the class group of the ring of integers `𝓞 L24` of `L24` has no element of order 5. The
  paper proves that `L24` has class number 1 (Theorem 6.1, Appendix B); that computation is not
  formalized.
* `hPutz`, in Theorem 1.2 only: Putz's Theorem 4.33 (Theorem 2.2 of the paper), that `A_η` is
  isomorphic to `L8` for every solution.
-/

@[expose] public section

namespace X2Y5Z7

open Polynomial

noncomputable section

/-- `h` with integer coefficients. -/
def hZ : ℤ[X] := X^8 + 4*X^7 - 28*X^6 - 168*X^5 - 140*X^4 + 560*X^3 + 840*X^2 - 480*X - 940

/-- `ψ` with integer coefficients. -/
def ψZ : ℤ[X] := 25*X^3 + 20*X^2 + 14*X + 14

/-- `h = x⁸ + 4x⁷ − 28x⁶ − 168x⁵ − 140x⁴ + 560x³ + 840x² − 480x − 940` over `ℚ`. -/
def h : ℚ[X] := hZ.map (Int.castRingHom ℚ)

/-- `ψ = 25t³ + 20t² + 14t + 14` over `ℚ`. -/
def ψ : ℚ[X] := ψZ.map (Int.castRingHom ℚ)

/-- `h` is irreducible over `ℚ` (Lemma 2.4(a)). -/
theorem h_irreducible : Irreducible h := by
  sorry

instance : Fact (Irreducible h) := ⟨h_irreducible⟩

/-- Putz's octic field `L₈ = ℚ[x]/(h)`. -/
abbrev L8 := AdjoinRoot h

/-! `L8` is a number field. The next three declarations repeat the library's, proofs included: the
map `algebraMap ℚ L8` in `ψL8` below is built from this `NumberField L8` instance, and Comparator
checks that these declarations agree with the library's too. -/

theorem h_ne_zero : h ≠ 0 := h_irreducible.ne_zero

instance : FiniteDimensional ℚ L8 := (AdjoinRoot.powerBasis h_ne_zero).finite

instance : NumberField L8 := ⟨⟩

/-- `ψ` over `L₈`. -/
def ψL8 : L8[X] := ψ.map (algebraMap ℚ L8)

/-- `ψ` is irreducible over `L₈` (Lemma 2.4(c)). -/
theorem ψL8_irreducible : Irreducible ψL8 := by
  sorry

instance : Fact (Irreducible ψL8) := ⟨ψL8_irreducible⟩

/-- The field `L₂₄ = L₈[t]/(ψ)` of degree 24. -/
abbrev L24 := AdjoinRoot ψL8

/-- The polynomial `f_s(t) = 4t⁵ψ(t) − s(4t − 1)` of (1.5); `A_η = ℚ[t]/(f_η)`. -/
def fpoly (s : ℚ) : ℚ[X] := C 4 * X ^ 5 * ψ - C s * (C 4 * X - 1)

end

open NumberField

/-- **Theorem 1.1.** Let `(X, Y, Z)` be a solution of (1.1) and `η = X⁵/Z⁷`. Then `A_η = ℚ[t]/(f_η)`
is not isomorphic to `L8` as a `ℚ`-algebra, assuming `hclass`: the class group of `𝓞 L24` has no
element of order 5. -/
theorem theorem_1_1 (hclass : ∀ c : ClassGroup (𝓞 L24), c ^ 5 = 1 → c = 1)
    (X Y Z : ℤ) (hX : X ≠ 0) (hY : Y ≠ 0) (hZ : Z ≠ 0) (hg : Int.gcd (Int.gcd X Y) Z = 1)
    (h : X ^ 5 + Y ^ 2 = Z ^ 7) :
    IsEmpty (AdjoinRoot (fpoly ((X : ℚ) ^ 5 / (Z : ℚ) ^ 7)) ≃ₐ[ℚ] L8) := by
  sorry

/-- **Theorem 1.2.** Assume Putz's Theorem 4.33 (`hPutz`: for every solution `(X, Y, Z)` of (1.1),
`A_η` is isomorphic to `L8`) and `hclass`. Then `x² + y⁵ = z⁷` has no solution in nonzero integers
with `gcd(x, y, z) = 1`. -/
theorem theorem_1_2
    (hPutz : ∀ X Y Z : ℤ, X ≠ 0 → Y ≠ 0 → Z ≠ 0 → Int.gcd (Int.gcd X Y) Z = 1 → X ^ 5 + Y ^ 2 = Z ^ 7 →
      Nonempty (AdjoinRoot (fpoly ((X : ℚ) ^ 5 / (Z : ℚ) ^ 7)) ≃ₐ[ℚ] L8))
    (hclass : ∀ c : ClassGroup (𝓞 L24), c ^ 5 = 1 → c = 1)
    (x y z : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hg : Int.gcd (Int.gcd x y) z = 1) :
    x ^ 2 + y ^ 5 ≠ z ^ 7 := by
  sorry

/-- **Theorem 1.2**, the equivalent form: under the same hypotheses, `x² + y⁷ = z⁵` has no solution
in nonzero integers with `gcd(x, y, z) = 1`. -/
theorem theorem_1_2_257
    (hPutz : ∀ X Y Z : ℤ, X ≠ 0 → Y ≠ 0 → Z ≠ 0 → Int.gcd (Int.gcd X Y) Z = 1 → X ^ 5 + Y ^ 2 = Z ^ 7 →
      Nonempty (AdjoinRoot (fpoly ((X : ℚ) ^ 5 / (Z : ℚ) ^ 7)) ≃ₐ[ℚ] L8))
    (hclass : ∀ c : ClassGroup (𝓞 L24), c ^ 5 = 1 → c = 1)
    (x y z : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hg : Int.gcd (Int.gcd x y) z = 1) :
    x ^ 2 + y ^ 7 ≠ z ^ 5 := by
  sorry

/-- **Theorem 1.2**, the equivalent form: under the same hypotheses, `x⁵ + y⁷ = z²` has no solution
in nonzero integers with `gcd(x, y, z) = 1`. -/
theorem theorem_1_2_572
    (hPutz : ∀ X Y Z : ℤ, X ≠ 0 → Y ≠ 0 → Z ≠ 0 → Int.gcd (Int.gcd X Y) Z = 1 → X ^ 5 + Y ^ 2 = Z ^ 7 →
      Nonempty (AdjoinRoot (fpoly ((X : ℚ) ^ 5 / (Z : ℚ) ^ 7)) ≃ₐ[ℚ] L8))
    (hclass : ∀ c : ClassGroup (𝓞 L24), c ^ 5 = 1 → c = 1)
    (x y z : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hg : Int.gcd (Int.gcd x y) z = 1) :
    x ^ 5 + y ^ 7 ≠ z ^ 2 := by
  sorry

end X2Y5Z7
