module

public import X2Y5Z7.Main.CondV
public import X2Y5Z7.ResidueSymbols.EResidue
public import X2Y5Z7.Norm.Theorems
public import X2Y5Z7.FiveAdic.Theorem
public import X2Y5Z7.Assembly.Q181
public import X2Y5Z7.Assembly.Q311
public import X2Y5Z7.Assembly.Q131
public import X2Y5Z7.Assembly.Q251
public import X2Y5Z7.Assembly.Q101

@[expose] public section

/-! # The proof of Theorem 1.1, as in Section 7 of the paper

Let `θ ∈ L₈` be a root of `f_η` generating `L₈` and `E = 80000 (θ − b) ψ(θ)³`. By Proposition 3.1 and the
class-group hypothesis, `E = ∏ B_j^{e_j} · z⁵` (Proposition 6.2). The vector `c = e mod 5` satisfies
* (N), by Proposition 3.2 and Lemma 6.3 (`Norm.condN_of_form`);
* (V), by Proposition 4.2 and `v_{P_i}(B_j) = δ_ij` (Proposition 6.2(i));
* (Q) at `q = 181, 311, 131, 251, 101`, by Corollary 5.5 and Proposition 5.3.
Theorem 7.1 (`Sieve.sieve`) says that no such `c` exists. -/

namespace X2Y5Z7.Main

open NumberField Polynomial IsDedekindDomain

theorem aeval_ψ_ne_zero (θ : L8) : aeval θ ψ ≠ 0 := by
  intro h
  exact ψL8_no_root θ (by rw [IsRoot, ψL8, eval_map_algebraMap]; exact h)

/-- Condition (V) for the exponents of `E` (Proposition 4.2). -/
theorem condV_of_form {s : Solution} (R : Aux.Root s) (e : Fin 24 → ℤ) (z : L24ˣ)
    (hform : ((ResidueSymbols.Eu R : L24ˣ) : L24) = (∏ j, B j ^ e j) * (z : L24) ^ 5) :
    Sieve.CondV (fun j => (e j : ZMod 5)) := by
  have key : ∀ i : Fin 24, 1 ≤ i.val → i.val ≤ 7 → (e i : ZMod 5) = (FiveAdic.valE i : ZMod 5) := by
    intro i h1 h7
    have hi : i.val < 12 := by omega
    exact cast_eq_of_cnt _ e z hform (SelmerForm.Pv sUnitFacts i hi) i hi rfl _
      (FiveAdic.count_Edesc_mod_five s R (SelmerForm.Pv sUnitFacts i hi) i h1 h7 rfl)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [FiveAdic.valE] using key 2 (by decide) (by decide)
  · simpa [FiveAdic.valE] using key 4 (by decide) (by decide)
  · simpa [FiveAdic.valE] using key 1 (by decide) (by decide)
  · simpa [FiveAdic.valE] using key 3 (by decide) (by decide)
  · simpa [FiveAdic.valE] using key 5 (by decide) (by decide)
  · simpa [FiveAdic.valE] using key 6 (by decide) (by decide)
  · simpa [FiveAdic.valE] using key 7 (by decide) (by decide)

/-- **Theorem 1.1** (proof of Section 7): a solution with `A_η ≅ L₈` does not exist, given the class-group
hypothesis. -/
theorem false_of_equiv_paper (hclass : ∀ c : ClassGroup (𝓞 L24), c ^ 5 = 1 → c = 1) (s : Solution)
    (he : Nonempty (AdjoinRoot (fpoly s.η) ≃ₐ[ℚ] L8)) : False := by
  obtain ⟨R⟩ := Aux.nonempty_root_of_nonempty_equiv he
  refine compose_paper Bint_coe sUnitFacts hclass (ResidueSymbols.Eu R)
    (fun v hv => count_Edesc_dvd_five s (ResidueSymbols.θ24 R) (ResidueSymbols.θ24_root R) v hv)
    (fun e z hform => ?_)
    (Assembly.Q181.auxAt s R) (Assembly.Q311.auxAt s R) (Assembly.Q131.auxAt s R)
    (Assembly.Q251.auxAt s R) (Assembly.Q101.auxAt s R)
  exact ⟨Norm.condN_of_form R.θ (aeval_ψ_ne_zero R.θ) e z hform, condV_of_form R e z hform⟩

end X2Y5Z7.Main
