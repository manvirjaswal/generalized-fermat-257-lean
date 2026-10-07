module

public import X2Y5Z7.Sieve.CheckRows

@[expose] public section

/-! # The finite check passes -/

namespace X2Y5Z7.Sieve.Cert

set_option maxRecDepth 100000

theorem rows_cover : rows181.map Prod.fst = I181L := by decide +kernel

theorem rows_ok : rows181.all rowOK = true := by
  simp only [rows181, List.all_append, rows0_ok, rows1_ok, rows2_ok, rows3_ok, rows4_ok, rows5_ok, Bool.and_self]

/-- The whole check passes. -/
theorem allOK_eq_true : allOK = true := by
  simp [allOK, rows_cover, rows_ok]

end X2Y5Z7.Sieve.Cert
