import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin

/-! # Vectors and matrices over `ZMod 5` as lists

The finite check in `X2Y5Z7.Sieve.Check` runs in the kernel. Lists are several times faster there than Mathlib's
`Matrix.mulVec`, whose sums go through `Finset`. This file defines the list operations the check uses and proves
that they agree with `Matrix.mulVec`, `+` and `-` on functions `Fin n → ZMod 5`. -/

namespace X2Y5Z7.Sieve

open Matrix

/-- The dot product of two lists (extra entries of the longer list are ignored). -/
def dotL : List (ZMod 5) → List (ZMod 5) → ZMod 5
  | a :: as, b :: bs => a * b + dotL as bs
  | _, _ => 0

/-- A matrix, given as its list of rows, times a vector. -/
def mvL (M : List (List (ZMod 5))) (v : List (ZMod 5)) : List (ZMod 5) :=
  M.map fun r => dotL r v

/-- Entrywise sum. -/
def addL (u v : List (ZMod 5)) : List (ZMod 5) := List.zipWith (· + ·) u v

/-- Entrywise difference. -/
def subL (u v : List (ZMod 5)) : List (ZMod 5) := List.zipWith (· - ·) u v

/-- The rows of a matrix, as lists. -/
def rowsOf {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 5)) : List (List (ZMod 5)) :=
  List.ofFn fun i => List.ofFn (M i)

theorem dotL_ofFn {n : ℕ} (u v : Fin n → ZMod 5) :
    dotL (List.ofFn u) (List.ofFn v) = u ⬝ᵥ v := by
  induction n with
  | zero => simp [dotL, dotProduct]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, dotL, ih]
    simp [dotProduct, Fin.sum_univ_succ]

theorem mvL_rowsOf {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 5)) (v : Fin n → ZMod 5) :
    mvL (rowsOf M) (List.ofFn v) = List.ofFn (M *ᵥ v) := by
  simp only [mvL, rowsOf, List.map_ofFn, Function.comp_def, dotL_ofFn]
  rfl

theorem zipWith_ofFn {n : ℕ} (f : ZMod 5 → ZMod 5 → ZMod 5) (u v : Fin n → ZMod 5) :
    List.zipWith f (List.ofFn u) (List.ofFn v) = List.ofFn fun i => f (u i) (v i) := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.ofFn_succ, List.ofFn_succ, List.zipWith_cons_cons, ih, List.ofFn_succ]

theorem addL_ofFn {n : ℕ} (u v : Fin n → ZMod 5) :
    addL (List.ofFn u) (List.ofFn v) = List.ofFn (u + v) := by
  simp only [addL, zipWith_ofFn]
  rfl

theorem subL_ofFn {n : ℕ} (u v : Fin n → ZMod 5) :
    subL (List.ofFn u) (List.ofFn v) = List.ofFn (u - v) := by
  simp only [subL, zipWith_ofFn]
  rfl

/-- Membership in a list of vectors is membership of the corresponding list of lists. -/
theorem mem_map_ofFn {n : ℕ} (v : Fin n → ZMod 5) (I : List (Fin n → ZMod 5)) :
    List.ofFn v ∈ I.map List.ofFn ↔ v ∈ I := by
  rw [List.mem_map]
  exact ⟨fun ⟨w, hw, h⟩ => List.ofFn_injective h ▸ hw, fun h => ⟨v, h, rfl⟩⟩

end X2Y5Z7.Sieve
