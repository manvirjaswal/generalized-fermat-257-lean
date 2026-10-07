module

public import X2Y5Z7.Sieve.Check

@[expose] public section

/-! # The chunks of the finite check

The check is split into six chunks of rows so that the kernel's memory stays bounded; each chunk is evaluated by
`decide +kernel`. -/

namespace X2Y5Z7.Sieve.Cert

set_option maxRecDepth 100000

theorem rows0_ok : rows181_0.all rowOK = true := by decide +kernel
theorem rows1_ok : rows181_1.all rowOK = true := by decide +kernel
theorem rows2_ok : rows181_2.all rowOK = true := by decide +kernel
theorem rows3_ok : rows181_3.all rowOK = true := by decide +kernel
theorem rows4_ok : rows181_4.all rowOK = true := by decide +kernel
theorem rows5_ok : rows181_5.all rowOK = true := by decide +kernel

end X2Y5Z7.Sieve.Cert
