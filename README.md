# Lean formalization: the generalized Fermat equation x² + y⁵ = z⁷

This is a Lean 4 formalization of the paper *The generalized Fermat equation x² + y⁵ = z⁷* by Manvir Jaswal
(preprint, Zenodo, 2026, https://doi.org/10.5281/zenodo.22983879).
Theorem numbers below are those of the paper.

## What is proved

`X2Y5Z7/Statements.lean` contains the main results, stated as in the paper.

**Theorem 1.1.** Let (X, Y, Z) be a solution of (1.1), that is, X⁵ + Y² = Z⁷ with gcd(X, Y, Z) = 1 and XYZ ≠ 0.
Then A_η = ℚ[t]/(f_η), with η = X⁵/Z⁷, is not isomorphic to L₈. The Lean statement assumes `hclass` (see "The
hypotheses" below).

```lean
theorem X2Y5Z7.theorem_1_1 (hclass : ∀ c : ClassGroup (𝓞 L24), c ^ 5 = 1 → c = 1)
    (X Y Z : ℤ) (hX : X ≠ 0) (hY : Y ≠ 0) (hZ : Z ≠ 0) (hg : Int.gcd (Int.gcd X Y) Z = 1)
    (h : X ^ 5 + Y ^ 2 = Z ^ 7) :
    IsEmpty (AdjoinRoot (fpoly ((X : ℚ) ^ 5 / (Z : ℚ) ^ 7)) ≃ₐ[ℚ] L8)
```

**Theorem 1.2.** Assume that for every solution of (1.1) the algebra A_η is isomorphic to L₈, as Putz's Theorem 4.33
asserts. Then x² + y⁵ = z⁷ has no solution in nonzero coprime integers. The Lean statement takes Putz's theorem as the
hypothesis `hPutz` and also assumes `hclass`.

```lean
theorem X2Y5Z7.theorem_1_2
    (hPutz : ∀ X Y Z : ℤ, X ≠ 0 → Y ≠ 0 → Z ≠ 0 → Int.gcd (Int.gcd X Y) Z = 1 → X ^ 5 + Y ^ 2 = Z ^ 7 →
      Nonempty (AdjoinRoot (fpoly ((X : ℚ) ^ 5 / (Z : ℚ) ^ 7)) ≃ₐ[ℚ] L8))
    (hclass : ∀ c : ClassGroup (𝓞 L24), c ^ 5 = 1 → c = 1)
    (x y z : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hg : Int.gcd (Int.gcd x y) z = 1) :
    x ^ 2 + y ^ 5 ≠ z ^ 7
```

The equivalent forms of Theorem 1.2 are `theorem_1_2_257` (x² + y⁷ ≠ z⁵) and `theorem_1_2_572` (x⁵ + y⁷ ≠ z²).

**Theorem 7.1** (the sieve), from the data printed in the paper, is `X2Y5Z7.Sieve.sieve`.

The other results of the paper that the proof of Theorem 1.1 uses are proved as stated there, among them:

| Paper | Lean |
|---|---|
| Proposition 3.1 (`E ∈ L₂₄(S, 5)`) | `X2Y5Z7.count_Edesc_dvd_five`, `X2Y5Z7.Edesc_mem_selmer` |
| Proposition 3.2 (the norm of `E` to `L₈`) | `X2Y5Z7.Norm.norm_Edesc` |
| Lemma 4.1 (the valuation of `E` at the prime above 2) | `X2Y5Z7.Norm.count_Edesc_P1` |
| Proposition 4.2 (`5 ∤ YZ` and the valuations of `E` at the primes above 5) | `X2Y5Z7.FiveAdic.five_not_dvd_Y`, `five_not_dvd_Z`, `count_Edesc_values` |
| Lemma 2.6 (the roots of `ψ` over `ℚ₅`, at the primes of `L₂₄` above 5) | `X2Y5Z7.FiveAdic.lemma_2_6` |
| Corollary 5.5 and Proposition 5.3 at `q = 181, 311, 131, 251, 101` | `X2Y5Z7.NotDvd.Q<q>.not_dvd`, `X2Y5Z7.SymbolSets.Q<q>.symbols_mem` |
| Proposition 6.2 (the basis `B₁, …, B₂₄` of `L₂₄(S, 5)`, `v_{P_i}(B_j) = δ_ij`) | `X2Y5Z7.Main.exists_form`, `X2Y5Z7.SUnitPrimes.count_B` |
| Lemma 6.3 (the units `u_i` of `L₈` and the norms of the `B_j`) | `X2Y5Z7.Norm.u_independent`, `X2Y5Z7.Norm.normB` |
| Section 7: (N), (V), (Q) hold for the class of `E` | `X2Y5Z7.Norm.condN_of_form`, `X2Y5Z7.Main.condV_of_form`, `X2Y5Z7.Main.compose_paper` |

All of these depend only on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). There is no
`sorry` and no `native_decide`. All computations are checked by the Lean kernel.

## The hypotheses

- **`hPutz`** is Putz's Theorem 4.33 (Theorem 2.2 of the paper), as in the statement of Theorem 1.2.
- **`hclass`** says that the class group of the ring of integers of L₂₄ has no element of order 5. The paper proves
  more, that the class number of L₂₄ is 1 (Theorem 6.1, Appendix B). That computation is not formalized here, so the
  Lean statements take this consequence of it as a hypothesis.

## The objects in the statements

These definitions are what a reader needs to check to trust the statements. Everything else is proved.

| Lean | Meaning | File |
|---|---|---|
| `hZ`, `h`, `L8 = AdjoinRoot h` | h(x) = x⁸ + 4x⁷ − 28x⁶ − 168x⁵ − 140x⁴ + 560x³ + 840x² − 480x − 940 and L₈ = ℚ[x]/(h), as in (1.6) | `X2Y5Z7/Fields/Basic.lean` |
| `ψZ`, `ψ`, `L24 = AdjoinRoot ψL8` | ψ(t) = 25t³ + 20t² + 14t + 14, as in (1.2), and L₂₄ = L₈[t]/(ψ) | `X2Y5Z7/Fields/Basic.lean` |
| `fpoly η` | f_η(t) = 4t⁵ψ(t) − η(4t − 1), as in (1.5) | `X2Y5Z7/Descent/Basic.lean` |
| `AdjoinRoot (fpoly η)` | ℚ[t]/(f_η) = A_η | Mathlib |
| `ClassGroup (𝓞 L24)` | the class group of the ring of integers of L₂₄ | Mathlib |
| `CondN`, `CondV`, `CondQ` | conditions (N), (V), (Q) of Theorem 7.1, with the printed matrices and sets | `X2Y5Z7/Sieve/Theorem.lean`, `X2Y5Z7/Sieve/Data.lean` |

`Audit.lean` prints the statements and their axioms. It also runs a few checks on these objects: L₈ and L₂₄ have
degrees 8 and 24 over ℚ, f_η expands to 100t⁸ + 80t⁷ + 56t⁶ + 56t⁵ − 4ηt + η, and the coprimality hypothesis
cannot be dropped, since (2¹⁰)² + (2⁴)⁵ = (2³)⁷.

## How the proof relates to the paper

The proof of Theorems 1.1 and 1.2 follows Section 7 of the paper: the class of `E` is written in the basis
`B₁, …, B₂₄`, its coordinates satisfy (N), (V) and (Q) at `q = 181, 311, 131, 251, 101`, and Theorem 7.1 excludes
this. Two points differ in form, not in substance:

- Section 4 of the paper works in the completions at 5 (Newton polygons, Hensel's lemma). The Lean proof of
  Proposition 4.2 works instead with the valuations at the seven prime ideals of `L₂₄` above 5 and with norms,
  which Mathlib supports; the conclusions are the same.
- The rows of the printed matrices `M_q` list the primes above `q` in another order than the residue-field models of
  the Lean files. The permutations are explicit (`X2Y5Z7.Main.σ181`, …), and the kernel checks that they carry the
  models' matrices and sets `I(q)` to the printed ones.

Not formalized: Theorem 6.1 and Appendix B (the class number of `L₂₄`), which enter only through `hclass`; and the
computations that the proof does not use (Lemma 2.1, the discriminants in Lemma 2.4, Proposition 5.4, Section 8).

## Building and checking

You need about 16 GB of RAM and 15 GB of free disk space.

1. Install Lean's version manager, `elan`, by following <https://lean-lang.org/install/>. It will download the Lean
   version named in `lean-toolchain` (v4.34.0) automatically.
2. In this folder, run:

   ```bash
   lake exe cache get
   lake build
   ```

   The first command downloads Mathlib (the version is pinned in `lake-manifest.json`) together with its prebuilt
   files, about 5 GB; this takes a few minutes. The second compiles this project's own files, which takes about
   20–45 minutes on a laptop, most of it the kernel checking the computations.
3. Print the statements and their axioms:

   ```bash
   lake env lean Audit.lean
   ```

4. Optionally, replay every declaration through Lean's independent kernel checker, one module at a time:

   ```bash
   for f in $(find X2Y5Z7 -name '*.lean'); do m=${f%.lean}; lake env leanchecker ${m//\//.} || break; done
   ```

   `lake env leanchecker X2Y5Z7` does the same in one command, but it checks all modules at once and needs far more
   memory than a laptop has.

## Where things are

| Paper | Lean |
|---|---|
| Theorems 1.1, 1.2 | `X2Y5Z7/Statements.lean`; the proof is assembled in `X2Y5Z7/Main/` |
| L₈, L₂₄: irreducibility of h and ψ, degrees, the signature of L₂₄ (parts of Lemma 2.4) | `X2Y5Z7/Fields/`, `X2Y5Z7/Arith/`, `X2Y5Z7/Units/` |
| The descent element E; Proposition 3.1 (E ∈ L₂₄(S, 5)); Proposition 3.2, Lemma 4.1, Lemma 6.3 | `X2Y5Z7/Descent/`, `X2Y5Z7/Norm/` |
| Proposition 4.2 and Lemma 2.6 (the primes above 5) | `X2Y5Z7/FiveAdic/` |
| The S-units B₁, …, B₂₄ (Table 4); the Selmer group under `hclass` (Section 6) | `X2Y5Z7/SUnits/`, `X2Y5Z7/Integral/`, `X2Y5Z7/Selmer/`, `X2Y5Z7/Reduction/` |
| Residue fields and residue symbols at the auxiliary primes (Table 6, Definition 5.1) | `X2Y5Z7/FiniteFields/`, `X2Y5Z7/Residue/`, `X2Y5Z7/ResidueSymbols/`, `X2Y5Z7/Primes/` |
| q ∤ XYZ at the five primes (Proposition 5.2, Corollary 5.5) | `X2Y5Z7/NotDvd/`, `X2Y5Z7/Auxiliary/` |
| The symbols of E lie in I(q) (Proposition 5.3) | `X2Y5Z7/SymbolSets/`, `X2Y5Z7/Assembly/` |
| Theorem 7.1 as printed | `X2Y5Z7/Sieve/` |
| Proposition 6.2(i) (`v_{P_i}(B_j) = δ_ij`) | `X2Y5Z7/SUnitPrimes/` |

Files that begin with "Generated" contain machine-produced data and certificates, such as factorizations over finite
fields, residue symbols and matrix identities. Their correctness does not depend on how they were produced: the Lean
kernel checks every fact that the proofs use.

## License

Copyright 2026 Manvir Jaswal. Released under the Apache License 2.0; see `LICENSE`.
