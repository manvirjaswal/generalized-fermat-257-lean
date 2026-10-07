module

public import X2Y5Z7

/-!
# The proofs

This module imports the library `X2Y5Z7`, which proves the declarations stated in `Challenge.lean`
under the same names:

* `X2Y5Z7.theorem_1_1`, `X2Y5Z7.theorem_1_2`, `X2Y5Z7.theorem_1_2_257` and `X2Y5Z7.theorem_1_2_572`,
  in `X2Y5Z7/Statements.lean`;
* `X2Y5Z7.h_irreducible` and `X2Y5Z7.ψL8_irreducible`, in `X2Y5Z7/Fields/Basic.lean`.

Comparator checks that each of them has exactly the type stated in `Challenge.lean`, that the
definitions these types use are the same, and that the proofs use only the axioms `propext`,
`Classical.choice` and `Quot.sound`.
-/
