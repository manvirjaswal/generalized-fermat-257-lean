# Lean formalization: the generalized Fermat equation x² + y⁵ = z⁷

A Lean 4 formalization, with Mathlib, of Theorems 1.1 and 1.2 of

> Manvir Jaswal, *The generalized Fermat equation x² + y⁵ = z⁷*, preprint, version 2, Zenodo, 2026.
> <https://doi.org/10.5281/zenodo.23223027>

The archived release of this formalization, on Lean v4.34.0, is <https://doi.org/10.5281/zenodo.23065698>.
This repository moves it to Lean v4.35.0-rc2 and the module system, in the layout of the
[Palomar](https://palomar-registry.org/) registry; the theorems and their proofs are unchanged.

## What it proves

Following Putz, a *solution* is a triple of integers (X, Y, Z) with X⁵ + Y² = Z⁷, gcd(X, Y, Z) = 1 and
XYZ ≠ 0. Put η = X⁵/Z⁷ and A_η = ℚ[t]/(f_η), where f_η(t) = 4t⁵ψ(t) − η(4t − 1) and
ψ(t) = 25t³ + 20t² + 14t + 14. Let L₈ = ℚ[x]/(h) be Putz's octic field, with
h(x) = x⁸ + 4x⁷ − 28x⁶ − 168x⁵ − 140x⁴ + 560x³ + 840x² − 480x − 940, and let L₂₄ = L₈[t]/(ψ).

- `X2Y5Z7.theorem_1_1` (Theorem 1.1): for every solution, A_η is not isomorphic to L₈.
- `X2Y5Z7.theorem_1_2` (Theorem 1.2): x² + y⁵ = z⁷ has no solution in nonzero integers with
  gcd(x, y, z) = 1.
- `X2Y5Z7.theorem_1_2_257` and `X2Y5Z7.theorem_1_2_572`: the same for x² + y⁷ = z⁵ and x⁵ + y⁷ = z².

[`Challenge.lean`](Challenge.lean) states these four theorems with the definitions they use, and imports
only Mathlib. It also states `X2Y5Z7.h_irreducible` and `X2Y5Z7.ψL8_irreducible` (h is irreducible over ℚ,
and ψ over L₈), which make L₈ and L₂₄ fields. [`Solution.lean`](Solution.lean) imports the proofs from the
library `X2Y5Z7/`. They use only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with
no `sorry` and no `native_decide`; every computation is checked by the Lean kernel.

## The two hypotheses

- `hclass`: the class group of the ring of integers of L₂₄ has no element of order 5. All four theorems
  assume it. The paper proves more, that L₂₄ has class number 1 (Theorem 6.1, Appendix B); that computation
  is not formalized, so the Lean Theorem 1.1 is conditional where the paper's is not.
- `hPutz`: Putz's Theorem 4.33 (Theorem 2.2 of the paper), that A_η is isomorphic to L₈ for every solution.
  Theorem 1.2 and its two equivalent forms assume it.

Also not formalized, and not used by the proof: Lemma 2.1, the discriminants in Lemma 2.4, Proposition 5.4
and Section 8.

## Build

You need about 16 GB of RAM and 15 GB of free disk space. Install [elan](https://lean-lang.org/install/);
it fetches the Lean version named in `lean-toolchain`. Then, in this folder:

```bash
lake exe cache get   # Mathlib's prebuilt files, about 5 GB
lake build           # this project: about 15–30 minutes on a laptop
```

If the build runs short of memory, limit it to two parallel jobs: `LEAN_NUM_THREADS=2 lake build`.

`lake env lean Audit.lean` prints the statements and the axioms their proofs use, and runs a few sanity
checks on the definitions.

## Run Comparator

On Linux, with [bubblewrap](https://github.com/containers/bubblewrap) installed:

```bash
./scripts/verify-comparator.sh
```

This runs the `lake comparator` of the project's toolchain on [`comparator.json`](comparator.json), as
Palomar does. It checks that the declarations of `Solution` have exactly the types stated in `Challenge`,
that the definitions these types use are the same, that the proofs use only the permitted axioms, and that
Lean's kernel and the independent kernels NanoDa and con-ron accept them.

Without bubblewrap, for example on macOS, the script cannot run. The same comparison runs without the
sandbox, with NanoDa and Lean's kernel, as
`PATH="$(lean --print-prefix)/bin:$PATH" lake comparator --inadvisably-no-sandbox`.

`scripts/`, `Gemfile` and `Gemfile.lock` come from Palomar's
[template](https://github.com/PalomarRegistry/PalomarTemplate); the CI workflow uses them to check the Lean
sources, [`formalization.yaml`](formalization.yaml) and the licence.

## About

The formalization was done with AI systems; `formalization.yaml` records how, and what was checked.
Copyright 2026 Manvir Jaswal. Released under the Apache License 2.0; see [`LICENSE`](LICENSE).
