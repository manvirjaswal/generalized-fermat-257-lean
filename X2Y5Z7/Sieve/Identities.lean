module

public import X2Y5Z7.Sieve.Data
public import X2Y5Z7.Sieve.Certificate
public import X2Y5Z7.Sieve.CheckData
public import X2Y5Z7.Sieve.ListAlg

@[expose] public section

/-! # The properties of the certificate that the proof uses

Every statement here is about explicit matrices over `ZMod 5`, and is checked by evaluation in the kernel
(`decide +kernel`). -/

namespace X2Y5Z7.Sieve.Cert

open Matrix

set_option maxRecDepth 100000

/-- The coordinates fixed by (V), 0-based (the paper's `c₃, c₅, c₂, c₄, c₆, c₇, c₈`), and their values. -/
def vIdx : Fin 7 → Fin 24 := ![2, 4, 1, 3, 5, 6, 7]
def vVal : Fin 7 → ZMod 5 := ![2, 3, 0, 0, 0, 0, 0]

/-! ## The constraint matrix -/

theorem A_rows_N : ∀ i : Fin 10, ∀ j : Fin 24, A (Fin.castAdd 7 i) j = ((NM i j : ℤ) : ZMod 5) := by
  decide +kernel

theorem b_N : ∀ i : Fin 10, b (Fin.castAdd 7 i) = ((TT i : ℤ) : ZMod 5) := by decide +kernel

theorem A_rows_V : ∀ k : Fin 7, A (Fin.natAdd 10 k) = Pi.single (vIdx k) 1 := by decide +kernel

theorem b_V : ∀ k : Fin 7, b (Fin.natAdd 10 k) = vVal k := by decide +kernel

/-! ## The affine space and the change of coordinates -/

theorem R_mul_A : R * A = 1 - Dm * S := by decide +kernel

theorem A_c0 : A *ᵥ c0 = b := by decide +kernel

theorem P_mul_Pinv : P * Pinv = 1 := by decide +kernel

theorem W_eq : W = Dm * P := by decide +kernel

/-! ## The symbol matrices on the affine space -/

theorem a181_eq : M181 *ᵥ c0 = a181 := by decide +kernel
theorem a311_eq : M311 *ᵥ c0 = a311 := by decide +kernel
theorem a131_eq : M131 *ᵥ c0 = a131 := by decide +kernel
theorem a251_eq : M251 *ᵥ c0 = a251 := by decide +kernel
theorem a101_eq : M101 *ᵥ c0 = a101 := by decide +kernel

theorem G1_181_eq : ∀ i j, (M181 * W) i (Fin.castAdd 4 j) = G1_181 i j := fun i j =>
  congrFun (congrFun (by decide +kernel : Matrix.of (fun i j => (M181 * W) i (Fin.castAdd 4 j)) = G1_181) i) j
theorem G2_181_eq : ∀ i j, (M181 * W) i (Fin.natAdd 6 j) = G2_181 i j := fun i j =>
  congrFun (congrFun (by decide +kernel : Matrix.of (fun i j => (M181 * W) i (Fin.natAdd 6 j)) = G2_181) i) j
theorem G1_311_eq : ∀ i j, (M311 * W) i (Fin.castAdd 4 j) = G1_311 i j := fun i j =>
  congrFun (congrFun (by decide +kernel : Matrix.of (fun i j => (M311 * W) i (Fin.castAdd 4 j)) = G1_311) i) j
theorem G2_311_eq : ∀ i j, (M311 * W) i (Fin.natAdd 6 j) = G2_311 i j := fun i j =>
  congrFun (congrFun (by decide +kernel : Matrix.of (fun i j => (M311 * W) i (Fin.natAdd 6 j)) = G2_311) i) j
theorem G1_131_eq : ∀ i j, (M131 * W) i (Fin.castAdd 4 j) = G1_131 i j := fun i j =>
  congrFun (congrFun (by decide +kernel : Matrix.of (fun i j => (M131 * W) i (Fin.castAdd 4 j)) = G1_131) i) j
theorem G2_131_eq : ∀ i j, (M131 * W) i (Fin.natAdd 6 j) = G2_131 i j := fun i j =>
  congrFun (congrFun (by decide +kernel : Matrix.of (fun i j => (M131 * W) i (Fin.natAdd 6 j)) = G2_131) i) j
theorem G1_251_eq : ∀ i j, (M251 * W) i (Fin.castAdd 4 j) = G1_251 i j := fun i j =>
  congrFun (congrFun (by decide +kernel : Matrix.of (fun i j => (M251 * W) i (Fin.castAdd 4 j)) = G1_251) i) j
theorem G2_251_eq : ∀ i j, (M251 * W) i (Fin.natAdd 6 j) = G2_251 i j := fun i j =>
  congrFun (congrFun (by decide +kernel : Matrix.of (fun i j => (M251 * W) i (Fin.natAdd 6 j)) = G2_251) i) j
theorem G1_101_eq : ∀ i j, (M101 * W) i (Fin.castAdd 4 j) = G1_101 i j := fun i j =>
  congrFun (congrFun (by decide +kernel : Matrix.of (fun i j => (M101 * W) i (Fin.castAdd 4 j)) = G1_101) i) j
theorem G2_101_eq : ∀ i j, (M101 * W) i (Fin.natAdd 6 j) = G2_101 i j := fun i j =>
  congrFun (congrFun (by decide +kernel : Matrix.of (fun i j => (M101 * W) i (Fin.natAdd 6 j)) = G2_101) i) j

theorem G2_181_zero : G2_181 = 0 := by decide +kernel

theorem L1_mul : L1 * G1_181 = 1 := by decide +kernel

theorem L2_mul : L2 * G2_311 = 1 := by decide +kernel

/-! ## The list forms used by the check -/

theorem L1L_eq : rowsOf L1 = L1L := by decide +kernel
theorem L2L_eq : rowsOf L2 = L2L := by decide +kernel
theorem a181L_eq : List.ofFn a181 = a181L := by decide +kernel
theorem a311L_eq : List.ofFn a311 = a311L := by decide +kernel
theorem a131L_eq : List.ofFn a131 = a131L := by decide +kernel
theorem a251L_eq : List.ofFn a251 = a251L := by decide +kernel
theorem a101L_eq : List.ofFn a101 = a101L := by decide +kernel
theorem G1_181L_eq : rowsOf G1_181 = G1_181L := by decide +kernel
theorem G1_311L_eq : rowsOf G1_311 = G1_311L := by decide +kernel
theorem G2_311L_eq : rowsOf G2_311 = G2_311L := by decide +kernel
theorem G1_131L_eq : rowsOf G1_131 = G1_131L := by decide +kernel
theorem G2_131L_eq : rowsOf G2_131 = G2_131L := by decide +kernel
theorem G1_251L_eq : rowsOf G1_251 = G1_251L := by decide +kernel
theorem G2_251L_eq : rowsOf G2_251 = G2_251L := by decide +kernel
theorem G1_101L_eq : rowsOf G1_101 = G1_101L := by decide +kernel
theorem G2_101L_eq : rowsOf G2_101 = G2_101L := by decide +kernel
theorem I181L_eq : I181.map List.ofFn = I181L := by decide +kernel
theorem I311L_eq : I311.map List.ofFn = I311L := by decide +kernel
theorem I131L_eq : I131.map List.ofFn = I131L := by decide +kernel
theorem I251L_eq : I251.map List.ofFn = I251L := by decide +kernel
theorem I101L_eq : I101.map List.ofFn = I101L := by decide +kernel

end X2Y5Z7.Sieve.Cert
