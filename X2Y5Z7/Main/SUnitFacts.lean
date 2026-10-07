import X2Y5Z7.SUnits.Theorems
import X2Y5Z7.Reduction.SelmerForm

/-! # The S-unit basis of Table 4 satisfies the hypotheses of the Selmer reduction -/

namespace X2Y5Z7.Main

open NumberField

theorem Bint_coe (j : Fin 24) : ((Bint j : 𝓞 L24) : L24) = B j := rfl

theorem sUnitFacts : SelmerForm.SUnitFacts Bint where
  ne_zero j h := Bint_span_ne_bot j (by rw [h, Ideal.span_singleton_eq_bot])
  isUnit := Bint_isUnit
  isPrime := Bint_span_isPrime
  mem_S i hi v hv := by
    have hmem := Sp_mem i hi
    rw [← hv] at hmem
    simp only [Selmer.L24SIntegers.Sprimes, Set.mem_ofPred_eq]
    fin_cases i <;> simp_all [Sp]
  classify := Sprimes_eq

end X2Y5Z7.Main
