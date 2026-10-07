import X2Y5Z7

/-! Run `lake env lean Audit.lean`. It prints the statements of the main results and the axioms their proofs use,
and runs a few sanity checks on the objects in the statements. -/

open Polynomial

-- Theorem 1.1: for a solution of (1.1), `A_η = ℚ[t]/(f_η)` is not isomorphic to `L8`.
#check @X2Y5Z7.theorem_1_1
-- Theorem 1.2 and its two equivalent forms.
#check @X2Y5Z7.theorem_1_2
#check @X2Y5Z7.theorem_1_2_257
#check @X2Y5Z7.theorem_1_2_572
-- Theorem 7.1: the sieve, from the data printed in the paper.
#check @X2Y5Z7.Sieve.sieve

#print axioms X2Y5Z7.theorem_1_1
#print axioms X2Y5Z7.theorem_1_2
#print axioms X2Y5Z7.theorem_1_2_257
#print axioms X2Y5Z7.theorem_1_2_572
#print axioms X2Y5Z7.Sieve.sieve

/-! Other results of the paper used in the proof of Theorem 1.1 (Section 7), and Lemma 4.1. -/

-- Proposition 3.2: the norm of `E` to `L8`.
#check @X2Y5Z7.Norm.norm_Edesc
-- Lemma 4.1: the valuation of `E` at the prime above 2.
#check @X2Y5Z7.Norm.count_Edesc_P1
-- Proposition 4.2: `5 ∤ YZ` and the valuations of `E` at the primes above 5.
#check @X2Y5Z7.FiveAdic.five_not_dvd_Y
#check @X2Y5Z7.FiveAdic.five_not_dvd_Z
#check @X2Y5Z7.FiveAdic.count_Edesc_values
-- Proposition 6.2(i): `v_{P_i}(B_j) = δ_ij`.
#check @X2Y5Z7.SUnitPrimes.count_B
-- Lemma 6.3: the units `u_i` of `L8` are independent modulo fifth powers, and the norms of the `B_j`.
#check @X2Y5Z7.Norm.u_independent
#check @X2Y5Z7.Norm.normB

#print axioms X2Y5Z7.Norm.norm_Edesc
#print axioms X2Y5Z7.Norm.count_Edesc_P1
#print axioms X2Y5Z7.FiveAdic.five_not_dvd_Y
#print axioms X2Y5Z7.FiveAdic.five_not_dvd_Z
#print axioms X2Y5Z7.FiveAdic.count_Edesc_values
#print axioms X2Y5Z7.SUnitPrimes.count_B
#print axioms X2Y5Z7.Norm.u_independent
#print axioms X2Y5Z7.Norm.normB

/-! Sanity checks on the statements. -/

-- `L8` and `L24` have degrees 8 and 24 over `ℚ`.
example : Module.finrank ℚ X2Y5Z7.L8 = 8 := X2Y5Z7.L8_finrank
example : Module.finrank ℚ X2Y5Z7.L24 = 24 := X2Y5Z7.L24_finrank

-- `f_η(t) = 4t⁵ψ(t) − η(4t − 1) = 100t⁸ + 80t⁷ + 56t⁶ + 56t⁵ − 4ηt + η`.
example (η t : ℚ) :
    aeval t (X2Y5Z7.fpoly η) = 100 * t ^ 8 + 80 * t ^ 7 + 56 * t ^ 6 + 56 * t ^ 5 - 4 * η * t + η := by
  rw [X2Y5Z7.aeval_fpoly]; simp

-- The coprimality hypothesis cannot be dropped: `(2¹⁰)² + (2⁴)⁵ = (2³)⁷`.
example : ((2 : ℤ) ^ 10) ^ 2 + ((2 : ℤ) ^ 4) ^ 5 = ((2 : ℤ) ^ 3) ^ 7 := by norm_num
