module

public import X2Y5Z7.Sieve.ListAlg
public import X2Y5Z7.Sieve.CheckData

@[expose] public section

/-! # The finite check behind Theorem 7.1

A point of the affine space is determined by its symbol vectors at `181` and `311` (see `Theorem.lean`). For each
`i1 ∈ I(181)` and `i2 ∈ I(311)` the check computes that point and tests the conditions at `131`, `251` and `101`.
There are `59 · 240 = 14160` pairs. The kernel evaluates the check (`decide +kernel`), so it uses only Lean's
standard axioms. -/

namespace X2Y5Z7.Sieve.Cert

/-- For `x1` and `g = G1_311 x1` fixed, the pair with `i2` fails: either `i2` is not the symbol vector at `311` of
the point it determines, or that point fails one of the conditions at `131`, `251`, `101`. -/
def pairFails (x1 g i2 : List (ZMod 5)) : Bool :=
  let x2 := mvL L2L (subL (subL i2 a311L) g)
  !decide (addL (addL a311L g) (mvL G2_311L x2) = i2) ||
  !decide (addL (addL a131L (mvL G1_131L x1)) (mvL G2_131L x2) ∈ I131L) ||
  !decide (addL (addL a251L (mvL G1_251L x1)) (mvL G2_251L x2) ∈ I251L) ||
  !decide (addL (addL a101L (mvL G1_101L x1)) (mvL G2_101L x2) ∈ I101L)

/-- The test for one row `(i1, x1, g)` of `rows181`: `x1` and `g` are the values forced by `i1`, and every pair
`(i1, i2)` fails. -/
def rowOK (r : List (ZMod 5) × List (ZMod 5) × List (ZMod 5)) : Bool :=
  decide (mvL L1L (subL r.1 a181L) = r.2.1) && decide (mvL G1_311L r.2.1 = r.2.2) &&
  (!decide (addL a181L (mvL G1_181L r.2.1) = r.1) || I311L.all (pairFails r.2.1 r.2.2))

/-- The whole check: the rows run through `I(181)` and every row passes. -/
def allOK : Bool := decide (rows181.map Prod.fst = I181L) && rows181.all rowOK

end X2Y5Z7.Sieve.Cert
