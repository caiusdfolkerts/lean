module

public import Papers.GraphicalZonotopes.FiniteTightCertificates
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.LinearCombination

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace SmallBoolean
open Finset FiniteTight
open scoped BigOperators Matrix

/-- Binary encoding of an actual finite subset; only used to read exact integer certificates. -/
def subsetMask {n : ℕ} (S : Finset (Fin n)) : ℕ := ∑ i∈S,2^i.val

namespace K4

def integerFunction (S : Finset (Fin 4)) : ℤ :=
  (match subsetMask S with
  | 3 => 1
  | 7 => 1
  | 11 => 1
  | 13 => 1
  | 14 => 1
  | 15 => 2
  | _ => 0)

def rows : Fin 16 → Row (Fin 4) :=
  ![.value {0,1},.value ∅,.value {0},.value {1},.value {2},.value {3},.elemental 0 1 {2,3},.elemental 0 2 ∅,.elemental 0 2 {1},.elemental 0 2 {1,3},.elemental 0 3 ∅,.elemental 0 3 {1},.elemental 1 2 ∅,.elemental 1 2 {0,3},.elemental 1 3 ∅,.elemental 2 3 ∅]

def pivot : Finset (Fin 4) := {0,1}

theorem pivot_one : integerFunction pivot=1 := by decide

theorem row_zero : rows 0=.value pivot := by decide

theorem valid_rows : ∀ i : Fin 16,i≠0 → (rows i).valid integerFunction := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 4096 in
theorem row_kernel_zero (f : SetFunction (Fin 4))
    (hf : ∀ i : Fin 16,(rows i).eval f=0) : f=0 := by
  have h0 : f {0,1}=0 := hf 0
  have h1 : f ∅=0 := hf 1
  have h2 : f {0}=0 := hf 2
  have h3 : f {1}=0 := hf 3
  have h4 : f {2}=0 := hf 4
  have h5 : f {3}=0 := hf 5
  have h6 : f {0,1,2,3}-f {0,2,3}-f {1,2,3}+f {2,3}=0 := by
    have h := hf 6
    change f (insert 0 (insert 1 ({2,3} : Finset (Fin 4))))-
      f (insert 0 ({2,3} : Finset (Fin 4)))-f (insert 1 ({2,3} : Finset (Fin 4)))+f {2,3}=0 at h
    have hAB : insert 0 (insert 1 ({2,3} : Finset (Fin 4)))={0,1,2,3} := by decide
    have hA : insert 0 ({2,3} : Finset (Fin 4))={0,2,3} := by decide
    have hB : insert 1 ({2,3} : Finset (Fin 4))={1,2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h7 : f {0,2}-f {0}-f {2}+f ∅=0 := by
    have h := hf 7
    change f (insert 0 (insert 2 (∅ : Finset (Fin 4))))-
      f (insert 0 (∅ : Finset (Fin 4)))-f (insert 2 (∅ : Finset (Fin 4)))+f ∅=0 at h
    have hAB : insert 0 (insert 2 (∅ : Finset (Fin 4)))={0,2} := by decide
    have hA : insert 0 (∅ : Finset (Fin 4))={0} := by decide
    have hB : insert 2 (∅ : Finset (Fin 4))={2} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h8 : f {0,1,2}-f {0,1}-f {1,2}+f {1}=0 := by
    have h := hf 8
    change f (insert 0 (insert 2 ({1} : Finset (Fin 4))))-
      f (insert 0 ({1} : Finset (Fin 4)))-f (insert 2 ({1} : Finset (Fin 4)))+f {1}=0 at h
    have hAB : insert 0 (insert 2 ({1} : Finset (Fin 4)))={0,1,2} := by decide
    have hA : insert 0 ({1} : Finset (Fin 4))={0,1} := by decide
    have hB : insert 2 ({1} : Finset (Fin 4))={1,2} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h9 : f {0,1,2,3}-f {0,1,3}-f {1,2,3}+f {1,3}=0 := by
    have h := hf 9
    change f (insert 0 (insert 2 ({1,3} : Finset (Fin 4))))-
      f (insert 0 ({1,3} : Finset (Fin 4)))-f (insert 2 ({1,3} : Finset (Fin 4)))+f {1,3}=0 at h
    have hAB : insert 0 (insert 2 ({1,3} : Finset (Fin 4)))={0,1,2,3} := by decide
    have hA : insert 0 ({1,3} : Finset (Fin 4))={0,1,3} := by decide
    have hB : insert 2 ({1,3} : Finset (Fin 4))={1,2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h10 : f {0,3}-f {0}-f {3}+f ∅=0 := by
    have h := hf 10
    change f (insert 0 (insert 3 (∅ : Finset (Fin 4))))-
      f (insert 0 (∅ : Finset (Fin 4)))-f (insert 3 (∅ : Finset (Fin 4)))+f ∅=0 at h
    have hAB : insert 0 (insert 3 (∅ : Finset (Fin 4)))={0,3} := by decide
    have hA : insert 0 (∅ : Finset (Fin 4))={0} := by decide
    have hB : insert 3 (∅ : Finset (Fin 4))={3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h11 : f {0,1,3}-f {0,1}-f {1,3}+f {1}=0 := by
    have h := hf 11
    change f (insert 0 (insert 3 ({1} : Finset (Fin 4))))-
      f (insert 0 ({1} : Finset (Fin 4)))-f (insert 3 ({1} : Finset (Fin 4)))+f {1}=0 at h
    have hAB : insert 0 (insert 3 ({1} : Finset (Fin 4)))={0,1,3} := by decide
    have hA : insert 0 ({1} : Finset (Fin 4))={0,1} := by decide
    have hB : insert 3 ({1} : Finset (Fin 4))={1,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h12 : f {1,2}-f {1}-f {2}+f ∅=0 := by
    have h := hf 12
    change f (insert 1 (insert 2 (∅ : Finset (Fin 4))))-
      f (insert 1 (∅ : Finset (Fin 4)))-f (insert 2 (∅ : Finset (Fin 4)))+f ∅=0 at h
    have hAB : insert 1 (insert 2 (∅ : Finset (Fin 4)))={1,2} := by decide
    have hA : insert 1 (∅ : Finset (Fin 4))={1} := by decide
    have hB : insert 2 (∅ : Finset (Fin 4))={2} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h13 : f {0,1,2,3}-f {0,1,3}-f {0,2,3}+f {0,3}=0 := by
    have h := hf 13
    change f (insert 1 (insert 2 ({0,3} : Finset (Fin 4))))-
      f (insert 1 ({0,3} : Finset (Fin 4)))-f (insert 2 ({0,3} : Finset (Fin 4)))+f {0,3}=0 at h
    have hAB : insert 1 (insert 2 ({0,3} : Finset (Fin 4)))={0,1,2,3} := by decide
    have hA : insert 1 ({0,3} : Finset (Fin 4))={0,1,3} := by decide
    have hB : insert 2 ({0,3} : Finset (Fin 4))={0,2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h14 : f {1,3}-f {1}-f {3}+f ∅=0 := by
    have h := hf 14
    change f (insert 1 (insert 3 (∅ : Finset (Fin 4))))-
      f (insert 1 (∅ : Finset (Fin 4)))-f (insert 3 (∅ : Finset (Fin 4)))+f ∅=0 at h
    have hAB : insert 1 (insert 3 (∅ : Finset (Fin 4)))={1,3} := by decide
    have hA : insert 1 (∅ : Finset (Fin 4))={1} := by decide
    have hB : insert 3 (∅ : Finset (Fin 4))={3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h15 : f {2,3}-f {2}-f {3}+f ∅=0 := by
    have h := hf 15
    change f (insert 2 (insert 3 (∅ : Finset (Fin 4))))-
      f (insert 2 (∅ : Finset (Fin 4)))-f (insert 3 (∅ : Finset (Fin 4)))+f ∅=0 at h
    have hAB : insert 2 (insert 3 (∅ : Finset (Fin 4)))={2,3} := by decide
    have hA : insert 2 (∅ : Finset (Fin 4))={2} := by decide
    have hB : insert 3 (∅ : Finset (Fin 4))={3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have v0 : f ∅=0 := by
    linear_combination h1
  have v1 : f {0}=0 := by
    linear_combination h2
  have v2 : f {1}=0 := by
    linear_combination h3
  have v3 : f {0,1}=0 := by
    linear_combination h0
  have v4 : f {2}=0 := by
    linear_combination h4
  have v5 : f {0,2}=0 := by
    linear_combination (-1) * h1 + h2 + h4 + h7
  have v6 : f {1,2}=0 := by
    linear_combination (-1) * h1 + h3 + h4 + h12
  have v7 : f {0,1,2}=0 := by
    linear_combination h0 + (-1) * h1 + h4 + h8 + h12
  have v8 : f {3}=0 := by
    linear_combination h5
  have v9 : f {0,3}=0 := by
    linear_combination (-1) * h1 + h2 + h5 + h10
  have v10 : f {1,3}=0 := by
    linear_combination (-1) * h1 + h3 + h5 + h14
  have v11 : f {0,1,3}=0 := by
    linear_combination h0 + (-1) * h1 + h5 + h11 + h14
  have v12 : f {2,3}=0 := by
    linear_combination (-1) * h1 + h4 + h5 + h15
  have v13 : f {0,2,3}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h3 + h4 + h5 + (-1) * h6 + h9 + h11 + h15
  have v14 : f {1,2,3}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h2 + h4 + h5 + (-1) * h6 + (-1) * h10 + h11 + h13 + h14 + h15
  have v15 : f {0,1,2,3}=0 := by
    linear_combination (2) * h0 + (-1) * h1 + (-1) * h2 + (-1) * h3 + h4 + h5 + (-1) * h6 + h9 + (-1) * h10 + (2) * h11 + h13 + h14 + h15
  funext S
  change f S=0
  have casesS : ∀ S : Finset (Fin 4), S=∅ ∨ S={0} ∨ S={1} ∨ S={0,1} ∨ S={2} ∨ S={0,2} ∨ S={1,2} ∨ S={0,1,2} ∨ S={3} ∨ S={0,3} ∨ S={1,3} ∨ S={0,1,3} ∨ S={2,3} ∨ S={0,2,3} ∨ S={1,2,3} ∨ S={0,1,2,3} := by decide
  rcases casesS S with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem empty_zero : integerFunction ∅=0 := by decide

theorem singleton_zero : ∀ v : Fin 4,integerFunction {v}=0 := by decide

theorem boolean_differences : ∀ u v : Fin 4,u≠v → ∀ S : Finset (Fin 4),
    u∉S → v∉S → integerDelta integerFunction u v S=0 ∨
      integerDelta integerFunction u v S=1 := by decide

theorem extreme : ExtremeSupermodular (realFunction integerFunction) :=
  extreme_of_row_kernel integerFunction rows pivot pivot_one row_zero valid_rows
    row_kernel_zero empty_zero singleton_zero boolean_differences

end K4

namespace K4Complement

def integerFunction (S : Finset (Fin 4)) : ℤ :=
  (match subsetMask S with
  | 5 => 1
  | 6 => 1
  | 7 => 2
  | 9 => 1
  | 10 => 1
  | 11 => 2
  | 12 => 1
  | 13 => 2
  | 14 => 2
  | 15 => 4
  | _ => 0)

def rows : Fin 16 → Row (Fin 4) :=
  ![.value {0,2},.value ∅,.value {0},.value {1},.value {2},.value {3},.elemental 0 1 ∅,.elemental 0 1 {2},.elemental 0 1 {3},.elemental 0 2 {3},.elemental 0 3 {2},.elemental 1 2 {3},.elemental 1 3 {2},.elemental 2 3 {0},.elemental 2 3 {1},.elemental 2 3 {0,1}]

def pivot : Finset (Fin 4) := {0,2}

theorem pivot_one : integerFunction pivot=1 := by decide

theorem row_zero : rows 0=.value pivot := by decide

theorem valid_rows : ∀ i : Fin 16,i≠0 → (rows i).valid integerFunction := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 4096 in
theorem row_kernel_zero (f : SetFunction (Fin 4))
    (hf : ∀ i : Fin 16,(rows i).eval f=0) : f=0 := by
  have h0 : f {0,2}=0 := hf 0
  have h1 : f ∅=0 := hf 1
  have h2 : f {0}=0 := hf 2
  have h3 : f {1}=0 := hf 3
  have h4 : f {2}=0 := hf 4
  have h5 : f {3}=0 := hf 5
  have h6 : f {0,1}-f {0}-f {1}+f ∅=0 := by
    have h := hf 6
    change f (insert 0 (insert 1 (∅ : Finset (Fin 4))))-
      f (insert 0 (∅ : Finset (Fin 4)))-f (insert 1 (∅ : Finset (Fin 4)))+f ∅=0 at h
    have hAB : insert 0 (insert 1 (∅ : Finset (Fin 4)))={0,1} := by decide
    have hA : insert 0 (∅ : Finset (Fin 4))={0} := by decide
    have hB : insert 1 (∅ : Finset (Fin 4))={1} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h7 : f {0,1,2}-f {0,2}-f {1,2}+f {2}=0 := by
    have h := hf 7
    change f (insert 0 (insert 1 ({2} : Finset (Fin 4))))-
      f (insert 0 ({2} : Finset (Fin 4)))-f (insert 1 ({2} : Finset (Fin 4)))+f {2}=0 at h
    have hAB : insert 0 (insert 1 ({2} : Finset (Fin 4)))={0,1,2} := by decide
    have hA : insert 0 ({2} : Finset (Fin 4))={0,2} := by decide
    have hB : insert 1 ({2} : Finset (Fin 4))={1,2} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h8 : f {0,1,3}-f {0,3}-f {1,3}+f {3}=0 := by
    have h := hf 8
    change f (insert 0 (insert 1 ({3} : Finset (Fin 4))))-
      f (insert 0 ({3} : Finset (Fin 4)))-f (insert 1 ({3} : Finset (Fin 4)))+f {3}=0 at h
    have hAB : insert 0 (insert 1 ({3} : Finset (Fin 4)))={0,1,3} := by decide
    have hA : insert 0 ({3} : Finset (Fin 4))={0,3} := by decide
    have hB : insert 1 ({3} : Finset (Fin 4))={1,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h9 : f {0,2,3}-f {0,3}-f {2,3}+f {3}=0 := by
    have h := hf 9
    change f (insert 0 (insert 2 ({3} : Finset (Fin 4))))-
      f (insert 0 ({3} : Finset (Fin 4)))-f (insert 2 ({3} : Finset (Fin 4)))+f {3}=0 at h
    have hAB : insert 0 (insert 2 ({3} : Finset (Fin 4)))={0,2,3} := by decide
    have hA : insert 0 ({3} : Finset (Fin 4))={0,3} := by decide
    have hB : insert 2 ({3} : Finset (Fin 4))={2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h10 : f {0,2,3}-f {0,2}-f {2,3}+f {2}=0 := by
    have h := hf 10
    change f (insert 0 (insert 3 ({2} : Finset (Fin 4))))-
      f (insert 0 ({2} : Finset (Fin 4)))-f (insert 3 ({2} : Finset (Fin 4)))+f {2}=0 at h
    have hAB : insert 0 (insert 3 ({2} : Finset (Fin 4)))={0,2,3} := by decide
    have hA : insert 0 ({2} : Finset (Fin 4))={0,2} := by decide
    have hB : insert 3 ({2} : Finset (Fin 4))={2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h11 : f {1,2,3}-f {1,3}-f {2,3}+f {3}=0 := by
    have h := hf 11
    change f (insert 1 (insert 2 ({3} : Finset (Fin 4))))-
      f (insert 1 ({3} : Finset (Fin 4)))-f (insert 2 ({3} : Finset (Fin 4)))+f {3}=0 at h
    have hAB : insert 1 (insert 2 ({3} : Finset (Fin 4)))={1,2,3} := by decide
    have hA : insert 1 ({3} : Finset (Fin 4))={1,3} := by decide
    have hB : insert 2 ({3} : Finset (Fin 4))={2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h12 : f {1,2,3}-f {1,2}-f {2,3}+f {2}=0 := by
    have h := hf 12
    change f (insert 1 (insert 3 ({2} : Finset (Fin 4))))-
      f (insert 1 ({2} : Finset (Fin 4)))-f (insert 3 ({2} : Finset (Fin 4)))+f {2}=0 at h
    have hAB : insert 1 (insert 3 ({2} : Finset (Fin 4)))={1,2,3} := by decide
    have hA : insert 1 ({2} : Finset (Fin 4))={1,2} := by decide
    have hB : insert 3 ({2} : Finset (Fin 4))={2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h13 : f {0,2,3}-f {0,2}-f {0,3}+f {0}=0 := by
    have h := hf 13
    change f (insert 2 (insert 3 ({0} : Finset (Fin 4))))-
      f (insert 2 ({0} : Finset (Fin 4)))-f (insert 3 ({0} : Finset (Fin 4)))+f {0}=0 at h
    have hAB : insert 2 (insert 3 ({0} : Finset (Fin 4)))={0,2,3} := by decide
    have hA : insert 2 ({0} : Finset (Fin 4))={0,2} := by decide
    have hB : insert 3 ({0} : Finset (Fin 4))={0,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h14 : f {1,2,3}-f {1,2}-f {1,3}+f {1}=0 := by
    have h := hf 14
    change f (insert 2 (insert 3 ({1} : Finset (Fin 4))))-
      f (insert 2 ({1} : Finset (Fin 4)))-f (insert 3 ({1} : Finset (Fin 4)))+f {1}=0 at h
    have hAB : insert 2 (insert 3 ({1} : Finset (Fin 4)))={1,2,3} := by decide
    have hA : insert 2 ({1} : Finset (Fin 4))={1,2} := by decide
    have hB : insert 3 ({1} : Finset (Fin 4))={1,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h15 : f {0,1,2,3}-f {0,1,2}-f {0,1,3}+f {0,1}=0 := by
    have h := hf 15
    change f (insert 2 (insert 3 ({0,1} : Finset (Fin 4))))-
      f (insert 2 ({0,1} : Finset (Fin 4)))-f (insert 3 ({0,1} : Finset (Fin 4)))+f {0,1}=0 at h
    have hAB : insert 2 (insert 3 ({0,1} : Finset (Fin 4)))={0,1,2,3} := by decide
    have hA : insert 2 ({0,1} : Finset (Fin 4))={0,1,2} := by decide
    have hB : insert 3 ({0,1} : Finset (Fin 4))={0,1,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have v0 : f ∅=0 := by
    linear_combination h1
  have v1 : f {0}=0 := by
    linear_combination h2
  have v2 : f {1}=0 := by
    linear_combination h3
  have v3 : f {0,1}=0 := by
    linear_combination (-1) * h1 + h2 + h3 + h6
  have v4 : f {2}=0 := by
    linear_combination h4
  have v5 : f {0,2}=0 := by
    linear_combination h0
  have v6 : f {1,2}=0 := by
    linear_combination h0 + (-1) * h2 + h3 + (-1) * h9 + h11 + h13 + (-1) * h14
  have v7 : f {0,1,2}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + h3 + (-1) * h4 + h7 + (-1) * h9 + h11 + h13 + (-1) * h14
  have v8 : f {3}=0 := by
    linear_combination h5
  have v9 : f {0,3}=0 := by
    linear_combination h0 + (-1) * h4 + h5 + (-1) * h9 + h10
  have v10 : f {1,3}=0 := by
    linear_combination h0 + (-1) * h2 + h3 + (-1) * h4 + h5 + (-1) * h9 + h12 + h13 + (-1) * h14
  have v11 : f {0,1,3}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + h3 + (-2) * h4 + h5 + h8 + (-2) * h9 + h10 + h12 + h13 + (-1) * h14
  have v12 : f {2,3}=0 := by
    linear_combination h0 + (-1) * h2 + h5 + (-1) * h9 + h13
  have v13 : f {0,2,3}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + (-1) * h4 + h5 + (-1) * h9 + h10 + h13
  have v14 : f {1,2,3}=0 := by
    linear_combination (2) * h0 + (-2) * h2 + h3 + (-1) * h4 + h5 + (-2) * h9 + h11 + h12 + (2) * h13 + (-1) * h14
  have v15 : f {0,1,2,3}=0 := by
    linear_combination (4) * h0 + h1 + (-3) * h2 + h3 + (-3) * h4 + h5 + (-1) * h6 + h7 + h8 + (-3) * h9 + h10 + h11 + h12 + (2) * h13 + (-2) * h14 + h15
  funext S
  change f S=0
  have casesS : ∀ S : Finset (Fin 4), S=∅ ∨ S={0} ∨ S={1} ∨ S={0,1} ∨ S={2} ∨ S={0,2} ∨ S={1,2} ∨ S={0,1,2} ∨ S={3} ∨ S={0,3} ∨ S={1,3} ∨ S={0,1,3} ∨ S={2,3} ∨ S={0,2,3} ∨ S={1,2,3} ∨ S={0,1,2,3} := by decide
  rcases casesS S with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem empty_zero : integerFunction ∅=0 := by decide

theorem singleton_zero : ∀ v : Fin 4,integerFunction {v}=0 := by decide

theorem boolean_differences : ∀ u v : Fin 4,u≠v → ∀ S : Finset (Fin 4),
    u∉S → v∉S → integerDelta integerFunction u v S=0 ∨
      integerDelta integerFunction u v S=1 := by decide

theorem extreme : ExtremeSupermodular (realFunction integerFunction) :=
  extreme_of_row_kernel integerFunction rows pivot pivot_one row_zero valid_rows
    row_kernel_zero empty_zero singleton_zero boolean_differences

end K4Complement

namespace K1112

def integerFunction (S : Finset (Fin 5)) : ℤ :=
  (match subsetMask S with
  | 3 => 1
  | 7 => 1
  | 9 => 1
  | 10 => 1
  | 11 => 2
  | 13 => 1
  | 14 => 1
  | 15 => 3
  | 19 => 1
  | 21 => 1
  | 22 => 1
  | 23 => 2
  | 25 => 1
  | 26 => 1
  | 27 => 2
  | 29 => 2
  | 30 => 2
  | 31 => 4
  | _ => 0)

def rows : Fin 32 → Row (Fin 5) :=
  ![.value {0,1},.value ∅,.value {0},.value {1},.value {2},.value {3},.value {4},.elemental 0 1 {3},.elemental 0 1 {2,4},.elemental 0 1 {3,4},.elemental 0 1 {2,3,4},.elemental 0 2 ∅,.elemental 0 2 {1},.elemental 0 2 {3},.elemental 0 2 {1,4},.elemental 0 3 {1},.elemental 0 3 {1,4},.elemental 0 4 ∅,.elemental 0 4 {1},.elemental 0 4 {1,2,3},.elemental 1 2 ∅,.elemental 1 2 {3},.elemental 1 2 {0,4},.elemental 1 3 {0},.elemental 1 3 {0,4},.elemental 1 4 ∅,.elemental 1 4 {0,2,3},.elemental 2 3 ∅,.elemental 2 3 {4},.elemental 2 3 {0,4},.elemental 2 4 ∅,.elemental 3 4 ∅]

def pivot : Finset (Fin 5) := {0,1}

theorem pivot_one : integerFunction pivot=1 := by decide

theorem row_zero : rows 0=.value pivot := by decide

theorem valid_rows : ∀ i : Fin 32,i≠0 → (rows i).valid integerFunction := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 4096 in
theorem row_kernel_zero (f : SetFunction (Fin 5))
    (hf : ∀ i : Fin 32,(rows i).eval f=0) : f=0 := by
  have h0 : f {0,1}=0 := hf 0
  have h1 : f ∅=0 := hf 1
  have h2 : f {0}=0 := hf 2
  have h3 : f {1}=0 := hf 3
  have h4 : f {2}=0 := hf 4
  have h5 : f {3}=0 := hf 5
  have h6 : f {4}=0 := hf 6
  have h7 : f {0,1,3}-f {0,3}-f {1,3}+f {3}=0 := by
    have h := hf 7
    change f (insert 0 (insert 1 ({3} : Finset (Fin 5))))-
      f (insert 0 ({3} : Finset (Fin 5)))-f (insert 1 ({3} : Finset (Fin 5)))+f {3}=0 at h
    have hAB : insert 0 (insert 1 ({3} : Finset (Fin 5)))={0,1,3} := by decide
    have hA : insert 0 ({3} : Finset (Fin 5))={0,3} := by decide
    have hB : insert 1 ({3} : Finset (Fin 5))={1,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h8 : f {0,1,2,4}-f {0,2,4}-f {1,2,4}+f {2,4}=0 := by
    have h := hf 8
    change f (insert 0 (insert 1 ({2,4} : Finset (Fin 5))))-
      f (insert 0 ({2,4} : Finset (Fin 5)))-f (insert 1 ({2,4} : Finset (Fin 5)))+f {2,4}=0 at h
    have hAB : insert 0 (insert 1 ({2,4} : Finset (Fin 5)))={0,1,2,4} := by decide
    have hA : insert 0 ({2,4} : Finset (Fin 5))={0,2,4} := by decide
    have hB : insert 1 ({2,4} : Finset (Fin 5))={1,2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h9 : f {0,1,3,4}-f {0,3,4}-f {1,3,4}+f {3,4}=0 := by
    have h := hf 9
    change f (insert 0 (insert 1 ({3,4} : Finset (Fin 5))))-
      f (insert 0 ({3,4} : Finset (Fin 5)))-f (insert 1 ({3,4} : Finset (Fin 5)))+f {3,4}=0 at h
    have hAB : insert 0 (insert 1 ({3,4} : Finset (Fin 5)))={0,1,3,4} := by decide
    have hA : insert 0 ({3,4} : Finset (Fin 5))={0,3,4} := by decide
    have hB : insert 1 ({3,4} : Finset (Fin 5))={1,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h10 : f {0,1,2,3,4}-f {0,2,3,4}-f {1,2,3,4}+f {2,3,4}=0 := by
    have h := hf 10
    change f (insert 0 (insert 1 ({2,3,4} : Finset (Fin 5))))-
      f (insert 0 ({2,3,4} : Finset (Fin 5)))-f (insert 1 ({2,3,4} : Finset (Fin 5)))+f {2,3,4}=0 at h
    have hAB : insert 0 (insert 1 ({2,3,4} : Finset (Fin 5)))={0,1,2,3,4} := by decide
    have hA : insert 0 ({2,3,4} : Finset (Fin 5))={0,2,3,4} := by decide
    have hB : insert 1 ({2,3,4} : Finset (Fin 5))={1,2,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h11 : f {0,2}-f {0}-f {2}+f ∅=0 := by
    have h := hf 11
    change f (insert 0 (insert 2 (∅ : Finset (Fin 5))))-
      f (insert 0 (∅ : Finset (Fin 5)))-f (insert 2 (∅ : Finset (Fin 5)))+f ∅=0 at h
    have hAB : insert 0 (insert 2 (∅ : Finset (Fin 5)))={0,2} := by decide
    have hA : insert 0 (∅ : Finset (Fin 5))={0} := by decide
    have hB : insert 2 (∅ : Finset (Fin 5))={2} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h12 : f {0,1,2}-f {0,1}-f {1,2}+f {1}=0 := by
    have h := hf 12
    change f (insert 0 (insert 2 ({1} : Finset (Fin 5))))-
      f (insert 0 ({1} : Finset (Fin 5)))-f (insert 2 ({1} : Finset (Fin 5)))+f {1}=0 at h
    have hAB : insert 0 (insert 2 ({1} : Finset (Fin 5)))={0,1,2} := by decide
    have hA : insert 0 ({1} : Finset (Fin 5))={0,1} := by decide
    have hB : insert 2 ({1} : Finset (Fin 5))={1,2} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h13 : f {0,2,3}-f {0,3}-f {2,3}+f {3}=0 := by
    have h := hf 13
    change f (insert 0 (insert 2 ({3} : Finset (Fin 5))))-
      f (insert 0 ({3} : Finset (Fin 5)))-f (insert 2 ({3} : Finset (Fin 5)))+f {3}=0 at h
    have hAB : insert 0 (insert 2 ({3} : Finset (Fin 5)))={0,2,3} := by decide
    have hA : insert 0 ({3} : Finset (Fin 5))={0,3} := by decide
    have hB : insert 2 ({3} : Finset (Fin 5))={2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h14 : f {0,1,2,4}-f {0,1,4}-f {1,2,4}+f {1,4}=0 := by
    have h := hf 14
    change f (insert 0 (insert 2 ({1,4} : Finset (Fin 5))))-
      f (insert 0 ({1,4} : Finset (Fin 5)))-f (insert 2 ({1,4} : Finset (Fin 5)))+f {1,4}=0 at h
    have hAB : insert 0 (insert 2 ({1,4} : Finset (Fin 5)))={0,1,2,4} := by decide
    have hA : insert 0 ({1,4} : Finset (Fin 5))={0,1,4} := by decide
    have hB : insert 2 ({1,4} : Finset (Fin 5))={1,2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h15 : f {0,1,3}-f {0,1}-f {1,3}+f {1}=0 := by
    have h := hf 15
    change f (insert 0 (insert 3 ({1} : Finset (Fin 5))))-
      f (insert 0 ({1} : Finset (Fin 5)))-f (insert 3 ({1} : Finset (Fin 5)))+f {1}=0 at h
    have hAB : insert 0 (insert 3 ({1} : Finset (Fin 5)))={0,1,3} := by decide
    have hA : insert 0 ({1} : Finset (Fin 5))={0,1} := by decide
    have hB : insert 3 ({1} : Finset (Fin 5))={1,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h16 : f {0,1,3,4}-f {0,1,4}-f {1,3,4}+f {1,4}=0 := by
    have h := hf 16
    change f (insert 0 (insert 3 ({1,4} : Finset (Fin 5))))-
      f (insert 0 ({1,4} : Finset (Fin 5)))-f (insert 3 ({1,4} : Finset (Fin 5)))+f {1,4}=0 at h
    have hAB : insert 0 (insert 3 ({1,4} : Finset (Fin 5)))={0,1,3,4} := by decide
    have hA : insert 0 ({1,4} : Finset (Fin 5))={0,1,4} := by decide
    have hB : insert 3 ({1,4} : Finset (Fin 5))={1,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h17 : f {0,4}-f {0}-f {4}+f ∅=0 := by
    have h := hf 17
    change f (insert 0 (insert 4 (∅ : Finset (Fin 5))))-
      f (insert 0 (∅ : Finset (Fin 5)))-f (insert 4 (∅ : Finset (Fin 5)))+f ∅=0 at h
    have hAB : insert 0 (insert 4 (∅ : Finset (Fin 5)))={0,4} := by decide
    have hA : insert 0 (∅ : Finset (Fin 5))={0} := by decide
    have hB : insert 4 (∅ : Finset (Fin 5))={4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h18 : f {0,1,4}-f {0,1}-f {1,4}+f {1}=0 := by
    have h := hf 18
    change f (insert 0 (insert 4 ({1} : Finset (Fin 5))))-
      f (insert 0 ({1} : Finset (Fin 5)))-f (insert 4 ({1} : Finset (Fin 5)))+f {1}=0 at h
    have hAB : insert 0 (insert 4 ({1} : Finset (Fin 5)))={0,1,4} := by decide
    have hA : insert 0 ({1} : Finset (Fin 5))={0,1} := by decide
    have hB : insert 4 ({1} : Finset (Fin 5))={1,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h19 : f {0,1,2,3,4}-f {0,1,2,3}-f {1,2,3,4}+f {1,2,3}=0 := by
    have h := hf 19
    change f (insert 0 (insert 4 ({1,2,3} : Finset (Fin 5))))-
      f (insert 0 ({1,2,3} : Finset (Fin 5)))-f (insert 4 ({1,2,3} : Finset (Fin 5)))+f {1,2,3}=0 at h
    have hAB : insert 0 (insert 4 ({1,2,3} : Finset (Fin 5)))={0,1,2,3,4} := by decide
    have hA : insert 0 ({1,2,3} : Finset (Fin 5))={0,1,2,3} := by decide
    have hB : insert 4 ({1,2,3} : Finset (Fin 5))={1,2,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h20 : f {1,2}-f {1}-f {2}+f ∅=0 := by
    have h := hf 20
    change f (insert 1 (insert 2 (∅ : Finset (Fin 5))))-
      f (insert 1 (∅ : Finset (Fin 5)))-f (insert 2 (∅ : Finset (Fin 5)))+f ∅=0 at h
    have hAB : insert 1 (insert 2 (∅ : Finset (Fin 5)))={1,2} := by decide
    have hA : insert 1 (∅ : Finset (Fin 5))={1} := by decide
    have hB : insert 2 (∅ : Finset (Fin 5))={2} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h21 : f {1,2,3}-f {1,3}-f {2,3}+f {3}=0 := by
    have h := hf 21
    change f (insert 1 (insert 2 ({3} : Finset (Fin 5))))-
      f (insert 1 ({3} : Finset (Fin 5)))-f (insert 2 ({3} : Finset (Fin 5)))+f {3}=0 at h
    have hAB : insert 1 (insert 2 ({3} : Finset (Fin 5)))={1,2,3} := by decide
    have hA : insert 1 ({3} : Finset (Fin 5))={1,3} := by decide
    have hB : insert 2 ({3} : Finset (Fin 5))={2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h22 : f {0,1,2,4}-f {0,1,4}-f {0,2,4}+f {0,4}=0 := by
    have h := hf 22
    change f (insert 1 (insert 2 ({0,4} : Finset (Fin 5))))-
      f (insert 1 ({0,4} : Finset (Fin 5)))-f (insert 2 ({0,4} : Finset (Fin 5)))+f {0,4}=0 at h
    have hAB : insert 1 (insert 2 ({0,4} : Finset (Fin 5)))={0,1,2,4} := by decide
    have hA : insert 1 ({0,4} : Finset (Fin 5))={0,1,4} := by decide
    have hB : insert 2 ({0,4} : Finset (Fin 5))={0,2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h23 : f {0,1,3}-f {0,1}-f {0,3}+f {0}=0 := by
    have h := hf 23
    change f (insert 1 (insert 3 ({0} : Finset (Fin 5))))-
      f (insert 1 ({0} : Finset (Fin 5)))-f (insert 3 ({0} : Finset (Fin 5)))+f {0}=0 at h
    have hAB : insert 1 (insert 3 ({0} : Finset (Fin 5)))={0,1,3} := by decide
    have hA : insert 1 ({0} : Finset (Fin 5))={0,1} := by decide
    have hB : insert 3 ({0} : Finset (Fin 5))={0,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h24 : f {0,1,3,4}-f {0,1,4}-f {0,3,4}+f {0,4}=0 := by
    have h := hf 24
    change f (insert 1 (insert 3 ({0,4} : Finset (Fin 5))))-
      f (insert 1 ({0,4} : Finset (Fin 5)))-f (insert 3 ({0,4} : Finset (Fin 5)))+f {0,4}=0 at h
    have hAB : insert 1 (insert 3 ({0,4} : Finset (Fin 5)))={0,1,3,4} := by decide
    have hA : insert 1 ({0,4} : Finset (Fin 5))={0,1,4} := by decide
    have hB : insert 3 ({0,4} : Finset (Fin 5))={0,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h25 : f {1,4}-f {1}-f {4}+f ∅=0 := by
    have h := hf 25
    change f (insert 1 (insert 4 (∅ : Finset (Fin 5))))-
      f (insert 1 (∅ : Finset (Fin 5)))-f (insert 4 (∅ : Finset (Fin 5)))+f ∅=0 at h
    have hAB : insert 1 (insert 4 (∅ : Finset (Fin 5)))={1,4} := by decide
    have hA : insert 1 (∅ : Finset (Fin 5))={1} := by decide
    have hB : insert 4 (∅ : Finset (Fin 5))={4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h26 : f {0,1,2,3,4}-f {0,1,2,3}-f {0,2,3,4}+f {0,2,3}=0 := by
    have h := hf 26
    change f (insert 1 (insert 4 ({0,2,3} : Finset (Fin 5))))-
      f (insert 1 ({0,2,3} : Finset (Fin 5)))-f (insert 4 ({0,2,3} : Finset (Fin 5)))+f {0,2,3}=0 at h
    have hAB : insert 1 (insert 4 ({0,2,3} : Finset (Fin 5)))={0,1,2,3,4} := by decide
    have hA : insert 1 ({0,2,3} : Finset (Fin 5))={0,1,2,3} := by decide
    have hB : insert 4 ({0,2,3} : Finset (Fin 5))={0,2,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h27 : f {2,3}-f {2}-f {3}+f ∅=0 := by
    have h := hf 27
    change f (insert 2 (insert 3 (∅ : Finset (Fin 5))))-
      f (insert 2 (∅ : Finset (Fin 5)))-f (insert 3 (∅ : Finset (Fin 5)))+f ∅=0 at h
    have hAB : insert 2 (insert 3 (∅ : Finset (Fin 5)))={2,3} := by decide
    have hA : insert 2 (∅ : Finset (Fin 5))={2} := by decide
    have hB : insert 3 (∅ : Finset (Fin 5))={3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h28 : f {2,3,4}-f {2,4}-f {3,4}+f {4}=0 := by
    have h := hf 28
    change f (insert 2 (insert 3 ({4} : Finset (Fin 5))))-
      f (insert 2 ({4} : Finset (Fin 5)))-f (insert 3 ({4} : Finset (Fin 5)))+f {4}=0 at h
    have hAB : insert 2 (insert 3 ({4} : Finset (Fin 5)))={2,3,4} := by decide
    have hA : insert 2 ({4} : Finset (Fin 5))={2,4} := by decide
    have hB : insert 3 ({4} : Finset (Fin 5))={3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h29 : f {0,2,3,4}-f {0,2,4}-f {0,3,4}+f {0,4}=0 := by
    have h := hf 29
    change f (insert 2 (insert 3 ({0,4} : Finset (Fin 5))))-
      f (insert 2 ({0,4} : Finset (Fin 5)))-f (insert 3 ({0,4} : Finset (Fin 5)))+f {0,4}=0 at h
    have hAB : insert 2 (insert 3 ({0,4} : Finset (Fin 5)))={0,2,3,4} := by decide
    have hA : insert 2 ({0,4} : Finset (Fin 5))={0,2,4} := by decide
    have hB : insert 3 ({0,4} : Finset (Fin 5))={0,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h30 : f {2,4}-f {2}-f {4}+f ∅=0 := by
    have h := hf 30
    change f (insert 2 (insert 4 (∅ : Finset (Fin 5))))-
      f (insert 2 (∅ : Finset (Fin 5)))-f (insert 4 (∅ : Finset (Fin 5)))+f ∅=0 at h
    have hAB : insert 2 (insert 4 (∅ : Finset (Fin 5)))={2,4} := by decide
    have hA : insert 2 (∅ : Finset (Fin 5))={2} := by decide
    have hB : insert 4 (∅ : Finset (Fin 5))={4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h31 : f {3,4}-f {3}-f {4}+f ∅=0 := by
    have h := hf 31
    change f (insert 3 (insert 4 (∅ : Finset (Fin 5))))-
      f (insert 3 (∅ : Finset (Fin 5)))-f (insert 4 (∅ : Finset (Fin 5)))+f ∅=0 at h
    have hAB : insert 3 (insert 4 (∅ : Finset (Fin 5)))={3,4} := by decide
    have hA : insert 3 (∅ : Finset (Fin 5))={3} := by decide
    have hB : insert 4 (∅ : Finset (Fin 5))={4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have v0 : f ∅=0 := by
    linear_combination h1
  have v1 : f {0}=0 := by
    linear_combination h2
  have v2 : f {1}=0 := by
    linear_combination h3
  have v3 : f {0,1}=0 := by
    linear_combination h0
  have v4 : f {2}=0 := by
    linear_combination h4
  have v5 : f {0,2}=0 := by
    linear_combination (-1) * h1 + h2 + h4 + h11
  have v6 : f {1,2}=0 := by
    linear_combination (-1) * h1 + h3 + h4 + h20
  have v7 : f {0,1,2}=0 := by
    linear_combination h0 + (-1) * h1 + h4 + h12 + h20
  have v8 : f {3}=0 := by
    linear_combination h5
  have v9 : f {0,3}=0 := by
    linear_combination h0 + (-1) * h3 + h5 + (-1) * h7 + h15
  have v10 : f {1,3}=0 := by
    linear_combination h0 + (-1) * h2 + h5 + (-1) * h7 + h23
  have v11 : f {0,1,3}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + (-1) * h3 + h5 + (-1) * h7 + h15 + h23
  have v12 : f {2,3}=0 := by
    linear_combination (-1) * h1 + h4 + h5 + h27
  have v13 : f {0,2,3}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h3 + h4 + h5 + (-1) * h7 + h13 + h15 + h27
  have v14 : f {1,2,3}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h2 + h4 + h5 + (-1) * h7 + h21 + h23 + h27
  have v15 : f {0,1,2,3}=0 := by
    linear_combination (3) * h0 + (-2) * h2 + (-2) * h3 + h4 + h5 + (-1) * h7 + (-1) * h8 + (-1) * h9 + h10 + h14 + h16 + (-1) * h17 + (2) * h18 + (-1) * h19 + h21 + h23 + h27 + (-1) * h28 + h29
  have v16 : f {4}=0 := by
    linear_combination h6
  have v17 : f {0,4}=0 := by
    linear_combination (-1) * h1 + h2 + h6 + h17
  have v18 : f {1,4}=0 := by
    linear_combination (-1) * h1 + h3 + h6 + h25
  have v19 : f {0,1,4}=0 := by
    linear_combination h0 + (-1) * h1 + h6 + h18 + h25
  have v20 : f {2,4}=0 := by
    linear_combination (-1) * h1 + h4 + h6 + h30
  have v21 : f {0,2,4}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h3 + h4 + h6 + (-1) * h8 + h14 + h18 + h30
  have v22 : f {1,2,4}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h2 + h4 + h6 + (-1) * h8 + (-1) * h17 + h18 + h22 + h25 + h30
  have v23 : f {0,1,2,4}=0 := by
    linear_combination (2) * h0 + (-1) * h1 + (-1) * h2 + (-1) * h3 + h4 + h6 + (-1) * h8 + h14 + (-1) * h17 + (2) * h18 + h22 + h25 + h30
  have v24 : f {3,4}=0 := by
    linear_combination (-1) * h1 + h5 + h6 + h31
  have v25 : f {0,3,4}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h3 + h5 + h6 + (-1) * h9 + h16 + h18 + h31
  have v26 : f {1,3,4}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h2 + h5 + h6 + (-1) * h9 + (-1) * h17 + h18 + h24 + h25 + h31
  have v27 : f {0,1,3,4}=0 := by
    linear_combination (2) * h0 + (-1) * h1 + (-1) * h2 + (-1) * h3 + h5 + h6 + (-1) * h9 + h16 + (-1) * h17 + (2) * h18 + h24 + h25 + h31
  have v28 : f {2,3,4}=0 := by
    linear_combination (-2) * h1 + h4 + h5 + h6 + h28 + h30 + h31
  have v29 : f {0,2,3,4}=0 := by
    linear_combination (2) * h0 + (-1) * h1 + (-1) * h2 + (-2) * h3 + h4 + h5 + h6 + (-1) * h8 + (-1) * h9 + h14 + h16 + (-1) * h17 + (2) * h18 + h29 + h30 + h31
  have v30 : f {1,2,3,4}=0 := by
    linear_combination (2) * h0 + (-1) * h1 + (-2) * h2 + (-1) * h3 + h4 + h5 + h6 + (-1) * h8 + (-1) * h9 + (-1) * h13 + h14 + (-1) * h15 + h16 + (-1) * h17 + (2) * h18 + (-1) * h19 + h21 + h23 + h26 + h29 + h30 + h31
  have v31 : f {0,1,2,3,4}=0 := by
    linear_combination (4) * h0 + (-3) * h2 + (-3) * h3 + h4 + h5 + h6 + (-2) * h8 + (-2) * h9 + h10 + (-1) * h13 + (2) * h14 + (-1) * h15 + (2) * h16 + (-2) * h17 + (4) * h18 + (-1) * h19 + h21 + h23 + h26 + (-1) * h28 + (2) * h29 + h30 + h31
  funext S
  change f S=0
  have casesS : ∀ S : Finset (Fin 5), S=∅ ∨ S={0} ∨ S={1} ∨ S={0,1} ∨ S={2} ∨ S={0,2} ∨ S={1,2} ∨ S={0,1,2} ∨ S={3} ∨ S={0,3} ∨ S={1,3} ∨ S={0,1,3} ∨ S={2,3} ∨ S={0,2,3} ∨ S={1,2,3} ∨ S={0,1,2,3} ∨ S={4} ∨ S={0,4} ∨ S={1,4} ∨ S={0,1,4} ∨ S={2,4} ∨ S={0,2,4} ∨ S={1,2,4} ∨ S={0,1,2,4} ∨ S={3,4} ∨ S={0,3,4} ∨ S={1,3,4} ∨ S={0,1,3,4} ∨ S={2,3,4} ∨ S={0,2,3,4} ∨ S={1,2,3,4} ∨ S={0,1,2,3,4} := by decide
  rcases casesS S with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem empty_zero : integerFunction ∅=0 := by decide

theorem singleton_zero : ∀ v : Fin 5,integerFunction {v}=0 := by decide

theorem boolean_differences : ∀ u v : Fin 5,u≠v → ∀ S : Finset (Fin 5),
    u∉S → v∉S → integerDelta integerFunction u v S=0 ∨
      integerDelta integerFunction u v S=1 := by decide

theorem extreme : ExtremeSupermodular (realFunction integerFunction) :=
  extreme_of_row_kernel integerFunction rows pivot pivot_one row_zero valid_rows
    row_kernel_zero empty_zero singleton_zero boolean_differences

end K1112

namespace K1112Complement

def integerFunction (S : Finset (Fin 5)) : ℤ :=
  (match subsetMask S with
  | 5 => 1
  | 6 => 1
  | 7 => 2
  | 11 => 1
  | 12 => 1
  | 13 => 2
  | 14 => 2
  | 15 => 3
  | 17 => 1
  | 18 => 1
  | 19 => 2
  | 20 => 1
  | 21 => 2
  | 22 => 2
  | 23 => 4
  | 25 => 1
  | 26 => 1
  | 27 => 3
  | 28 => 2
  | 29 => 3
  | 30 => 3
  | 31 => 5
  | _ => 0)

def rows : Fin 32 → Row (Fin 5) :=
  ![.value {0,2},.value ∅,.value {0},.value {1},.value {2},.value {3},.value {4},.elemental 0 1 ∅,.elemental 0 1 {2},.elemental 0 1 {2,3},.elemental 0 1 {4},.elemental 0 2 {1,3},.elemental 0 2 {4},.elemental 0 2 {3,4},.elemental 0 2 {1,3,4},.elemental 0 3 ∅,.elemental 0 3 {2},.elemental 0 3 {4},.elemental 0 3 {1,2,4},.elemental 0 4 {2},.elemental 1 2 {0,3},.elemental 1 2 {4},.elemental 1 2 {3,4},.elemental 1 3 ∅,.elemental 1 3 {2},.elemental 1 3 {4},.elemental 1 4 {2},.elemental 2 3 {0,1},.elemental 2 3 {0,1,4},.elemental 2 4 {0},.elemental 2 4 {0,1},.elemental 3 4 ∅]

def pivot : Finset (Fin 5) := {0,2}

theorem pivot_one : integerFunction pivot=1 := by decide

theorem row_zero : rows 0=.value pivot := by decide

theorem valid_rows : ∀ i : Fin 32,i≠0 → (rows i).valid integerFunction := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 4096 in
theorem row_kernel_zero (f : SetFunction (Fin 5))
    (hf : ∀ i : Fin 32,(rows i).eval f=0) : f=0 := by
  have h0 : f {0,2}=0 := hf 0
  have h1 : f ∅=0 := hf 1
  have h2 : f {0}=0 := hf 2
  have h3 : f {1}=0 := hf 3
  have h4 : f {2}=0 := hf 4
  have h5 : f {3}=0 := hf 5
  have h6 : f {4}=0 := hf 6
  have h7 : f {0,1}-f {0}-f {1}+f ∅=0 := by
    have h := hf 7
    change f (insert 0 (insert 1 (∅ : Finset (Fin 5))))-
      f (insert 0 (∅ : Finset (Fin 5)))-f (insert 1 (∅ : Finset (Fin 5)))+f ∅=0 at h
    have hAB : insert 0 (insert 1 (∅ : Finset (Fin 5)))={0,1} := by decide
    have hA : insert 0 (∅ : Finset (Fin 5))={0} := by decide
    have hB : insert 1 (∅ : Finset (Fin 5))={1} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h8 : f {0,1,2}-f {0,2}-f {1,2}+f {2}=0 := by
    have h := hf 8
    change f (insert 0 (insert 1 ({2} : Finset (Fin 5))))-
      f (insert 0 ({2} : Finset (Fin 5)))-f (insert 1 ({2} : Finset (Fin 5)))+f {2}=0 at h
    have hAB : insert 0 (insert 1 ({2} : Finset (Fin 5)))={0,1,2} := by decide
    have hA : insert 0 ({2} : Finset (Fin 5))={0,2} := by decide
    have hB : insert 1 ({2} : Finset (Fin 5))={1,2} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h9 : f {0,1,2,3}-f {0,2,3}-f {1,2,3}+f {2,3}=0 := by
    have h := hf 9
    change f (insert 0 (insert 1 ({2,3} : Finset (Fin 5))))-
      f (insert 0 ({2,3} : Finset (Fin 5)))-f (insert 1 ({2,3} : Finset (Fin 5)))+f {2,3}=0 at h
    have hAB : insert 0 (insert 1 ({2,3} : Finset (Fin 5)))={0,1,2,3} := by decide
    have hA : insert 0 ({2,3} : Finset (Fin 5))={0,2,3} := by decide
    have hB : insert 1 ({2,3} : Finset (Fin 5))={1,2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h10 : f {0,1,4}-f {0,4}-f {1,4}+f {4}=0 := by
    have h := hf 10
    change f (insert 0 (insert 1 ({4} : Finset (Fin 5))))-
      f (insert 0 ({4} : Finset (Fin 5)))-f (insert 1 ({4} : Finset (Fin 5)))+f {4}=0 at h
    have hAB : insert 0 (insert 1 ({4} : Finset (Fin 5)))={0,1,4} := by decide
    have hA : insert 0 ({4} : Finset (Fin 5))={0,4} := by decide
    have hB : insert 1 ({4} : Finset (Fin 5))={1,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h11 : f {0,1,2,3}-f {0,1,3}-f {1,2,3}+f {1,3}=0 := by
    have h := hf 11
    change f (insert 0 (insert 2 ({1,3} : Finset (Fin 5))))-
      f (insert 0 ({1,3} : Finset (Fin 5)))-f (insert 2 ({1,3} : Finset (Fin 5)))+f {1,3}=0 at h
    have hAB : insert 0 (insert 2 ({1,3} : Finset (Fin 5)))={0,1,2,3} := by decide
    have hA : insert 0 ({1,3} : Finset (Fin 5))={0,1,3} := by decide
    have hB : insert 2 ({1,3} : Finset (Fin 5))={1,2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h12 : f {0,2,4}-f {0,4}-f {2,4}+f {4}=0 := by
    have h := hf 12
    change f (insert 0 (insert 2 ({4} : Finset (Fin 5))))-
      f (insert 0 ({4} : Finset (Fin 5)))-f (insert 2 ({4} : Finset (Fin 5)))+f {4}=0 at h
    have hAB : insert 0 (insert 2 ({4} : Finset (Fin 5)))={0,2,4} := by decide
    have hA : insert 0 ({4} : Finset (Fin 5))={0,4} := by decide
    have hB : insert 2 ({4} : Finset (Fin 5))={2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h13 : f {0,2,3,4}-f {0,3,4}-f {2,3,4}+f {3,4}=0 := by
    have h := hf 13
    change f (insert 0 (insert 2 ({3,4} : Finset (Fin 5))))-
      f (insert 0 ({3,4} : Finset (Fin 5)))-f (insert 2 ({3,4} : Finset (Fin 5)))+f {3,4}=0 at h
    have hAB : insert 0 (insert 2 ({3,4} : Finset (Fin 5)))={0,2,3,4} := by decide
    have hA : insert 0 ({3,4} : Finset (Fin 5))={0,3,4} := by decide
    have hB : insert 2 ({3,4} : Finset (Fin 5))={2,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h14 : f {0,1,2,3,4}-f {0,1,3,4}-f {1,2,3,4}+f {1,3,4}=0 := by
    have h := hf 14
    change f (insert 0 (insert 2 ({1,3,4} : Finset (Fin 5))))-
      f (insert 0 ({1,3,4} : Finset (Fin 5)))-f (insert 2 ({1,3,4} : Finset (Fin 5)))+f {1,3,4}=0 at h
    have hAB : insert 0 (insert 2 ({1,3,4} : Finset (Fin 5)))={0,1,2,3,4} := by decide
    have hA : insert 0 ({1,3,4} : Finset (Fin 5))={0,1,3,4} := by decide
    have hB : insert 2 ({1,3,4} : Finset (Fin 5))={1,2,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h15 : f {0,3}-f {0}-f {3}+f ∅=0 := by
    have h := hf 15
    change f (insert 0 (insert 3 (∅ : Finset (Fin 5))))-
      f (insert 0 (∅ : Finset (Fin 5)))-f (insert 3 (∅ : Finset (Fin 5)))+f ∅=0 at h
    have hAB : insert 0 (insert 3 (∅ : Finset (Fin 5)))={0,3} := by decide
    have hA : insert 0 (∅ : Finset (Fin 5))={0} := by decide
    have hB : insert 3 (∅ : Finset (Fin 5))={3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h16 : f {0,2,3}-f {0,2}-f {2,3}+f {2}=0 := by
    have h := hf 16
    change f (insert 0 (insert 3 ({2} : Finset (Fin 5))))-
      f (insert 0 ({2} : Finset (Fin 5)))-f (insert 3 ({2} : Finset (Fin 5)))+f {2}=0 at h
    have hAB : insert 0 (insert 3 ({2} : Finset (Fin 5)))={0,2,3} := by decide
    have hA : insert 0 ({2} : Finset (Fin 5))={0,2} := by decide
    have hB : insert 3 ({2} : Finset (Fin 5))={2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h17 : f {0,3,4}-f {0,4}-f {3,4}+f {4}=0 := by
    have h := hf 17
    change f (insert 0 (insert 3 ({4} : Finset (Fin 5))))-
      f (insert 0 ({4} : Finset (Fin 5)))-f (insert 3 ({4} : Finset (Fin 5)))+f {4}=0 at h
    have hAB : insert 0 (insert 3 ({4} : Finset (Fin 5)))={0,3,4} := by decide
    have hA : insert 0 ({4} : Finset (Fin 5))={0,4} := by decide
    have hB : insert 3 ({4} : Finset (Fin 5))={3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h18 : f {0,1,2,3,4}-f {0,1,2,4}-f {1,2,3,4}+f {1,2,4}=0 := by
    have h := hf 18
    change f (insert 0 (insert 3 ({1,2,4} : Finset (Fin 5))))-
      f (insert 0 ({1,2,4} : Finset (Fin 5)))-f (insert 3 ({1,2,4} : Finset (Fin 5)))+f {1,2,4}=0 at h
    have hAB : insert 0 (insert 3 ({1,2,4} : Finset (Fin 5)))={0,1,2,3,4} := by decide
    have hA : insert 0 ({1,2,4} : Finset (Fin 5))={0,1,2,4} := by decide
    have hB : insert 3 ({1,2,4} : Finset (Fin 5))={1,2,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h19 : f {0,2,4}-f {0,2}-f {2,4}+f {2}=0 := by
    have h := hf 19
    change f (insert 0 (insert 4 ({2} : Finset (Fin 5))))-
      f (insert 0 ({2} : Finset (Fin 5)))-f (insert 4 ({2} : Finset (Fin 5)))+f {2}=0 at h
    have hAB : insert 0 (insert 4 ({2} : Finset (Fin 5)))={0,2,4} := by decide
    have hA : insert 0 ({2} : Finset (Fin 5))={0,2} := by decide
    have hB : insert 4 ({2} : Finset (Fin 5))={2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h20 : f {0,1,2,3}-f {0,1,3}-f {0,2,3}+f {0,3}=0 := by
    have h := hf 20
    change f (insert 1 (insert 2 ({0,3} : Finset (Fin 5))))-
      f (insert 1 ({0,3} : Finset (Fin 5)))-f (insert 2 ({0,3} : Finset (Fin 5)))+f {0,3}=0 at h
    have hAB : insert 1 (insert 2 ({0,3} : Finset (Fin 5)))={0,1,2,3} := by decide
    have hA : insert 1 ({0,3} : Finset (Fin 5))={0,1,3} := by decide
    have hB : insert 2 ({0,3} : Finset (Fin 5))={0,2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h21 : f {1,2,4}-f {1,4}-f {2,4}+f {4}=0 := by
    have h := hf 21
    change f (insert 1 (insert 2 ({4} : Finset (Fin 5))))-
      f (insert 1 ({4} : Finset (Fin 5)))-f (insert 2 ({4} : Finset (Fin 5)))+f {4}=0 at h
    have hAB : insert 1 (insert 2 ({4} : Finset (Fin 5)))={1,2,4} := by decide
    have hA : insert 1 ({4} : Finset (Fin 5))={1,4} := by decide
    have hB : insert 2 ({4} : Finset (Fin 5))={2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h22 : f {1,2,3,4}-f {1,3,4}-f {2,3,4}+f {3,4}=0 := by
    have h := hf 22
    change f (insert 1 (insert 2 ({3,4} : Finset (Fin 5))))-
      f (insert 1 ({3,4} : Finset (Fin 5)))-f (insert 2 ({3,4} : Finset (Fin 5)))+f {3,4}=0 at h
    have hAB : insert 1 (insert 2 ({3,4} : Finset (Fin 5)))={1,2,3,4} := by decide
    have hA : insert 1 ({3,4} : Finset (Fin 5))={1,3,4} := by decide
    have hB : insert 2 ({3,4} : Finset (Fin 5))={2,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h23 : f {1,3}-f {1}-f {3}+f ∅=0 := by
    have h := hf 23
    change f (insert 1 (insert 3 (∅ : Finset (Fin 5))))-
      f (insert 1 (∅ : Finset (Fin 5)))-f (insert 3 (∅ : Finset (Fin 5)))+f ∅=0 at h
    have hAB : insert 1 (insert 3 (∅ : Finset (Fin 5)))={1,3} := by decide
    have hA : insert 1 (∅ : Finset (Fin 5))={1} := by decide
    have hB : insert 3 (∅ : Finset (Fin 5))={3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h24 : f {1,2,3}-f {1,2}-f {2,3}+f {2}=0 := by
    have h := hf 24
    change f (insert 1 (insert 3 ({2} : Finset (Fin 5))))-
      f (insert 1 ({2} : Finset (Fin 5)))-f (insert 3 ({2} : Finset (Fin 5)))+f {2}=0 at h
    have hAB : insert 1 (insert 3 ({2} : Finset (Fin 5)))={1,2,3} := by decide
    have hA : insert 1 ({2} : Finset (Fin 5))={1,2} := by decide
    have hB : insert 3 ({2} : Finset (Fin 5))={2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h25 : f {1,3,4}-f {1,4}-f {3,4}+f {4}=0 := by
    have h := hf 25
    change f (insert 1 (insert 3 ({4} : Finset (Fin 5))))-
      f (insert 1 ({4} : Finset (Fin 5)))-f (insert 3 ({4} : Finset (Fin 5)))+f {4}=0 at h
    have hAB : insert 1 (insert 3 ({4} : Finset (Fin 5)))={1,3,4} := by decide
    have hA : insert 1 ({4} : Finset (Fin 5))={1,4} := by decide
    have hB : insert 3 ({4} : Finset (Fin 5))={3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h26 : f {1,2,4}-f {1,2}-f {2,4}+f {2}=0 := by
    have h := hf 26
    change f (insert 1 (insert 4 ({2} : Finset (Fin 5))))-
      f (insert 1 ({2} : Finset (Fin 5)))-f (insert 4 ({2} : Finset (Fin 5)))+f {2}=0 at h
    have hAB : insert 1 (insert 4 ({2} : Finset (Fin 5)))={1,2,4} := by decide
    have hA : insert 1 ({2} : Finset (Fin 5))={1,2} := by decide
    have hB : insert 4 ({2} : Finset (Fin 5))={2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h27 : f {0,1,2,3}-f {0,1,2}-f {0,1,3}+f {0,1}=0 := by
    have h := hf 27
    change f (insert 2 (insert 3 ({0,1} : Finset (Fin 5))))-
      f (insert 2 ({0,1} : Finset (Fin 5)))-f (insert 3 ({0,1} : Finset (Fin 5)))+f {0,1}=0 at h
    have hAB : insert 2 (insert 3 ({0,1} : Finset (Fin 5)))={0,1,2,3} := by decide
    have hA : insert 2 ({0,1} : Finset (Fin 5))={0,1,2} := by decide
    have hB : insert 3 ({0,1} : Finset (Fin 5))={0,1,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h28 : f {0,1,2,3,4}-f {0,1,2,4}-f {0,1,3,4}+f {0,1,4}=0 := by
    have h := hf 28
    change f (insert 2 (insert 3 ({0,1,4} : Finset (Fin 5))))-
      f (insert 2 ({0,1,4} : Finset (Fin 5)))-f (insert 3 ({0,1,4} : Finset (Fin 5)))+f {0,1,4}=0 at h
    have hAB : insert 2 (insert 3 ({0,1,4} : Finset (Fin 5)))={0,1,2,3,4} := by decide
    have hA : insert 2 ({0,1,4} : Finset (Fin 5))={0,1,2,4} := by decide
    have hB : insert 3 ({0,1,4} : Finset (Fin 5))={0,1,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h29 : f {0,2,4}-f {0,2}-f {0,4}+f {0}=0 := by
    have h := hf 29
    change f (insert 2 (insert 4 ({0} : Finset (Fin 5))))-
      f (insert 2 ({0} : Finset (Fin 5)))-f (insert 4 ({0} : Finset (Fin 5)))+f {0}=0 at h
    have hAB : insert 2 (insert 4 ({0} : Finset (Fin 5)))={0,2,4} := by decide
    have hA : insert 2 ({0} : Finset (Fin 5))={0,2} := by decide
    have hB : insert 4 ({0} : Finset (Fin 5))={0,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h30 : f {0,1,2,4}-f {0,1,2}-f {0,1,4}+f {0,1}=0 := by
    have h := hf 30
    change f (insert 2 (insert 4 ({0,1} : Finset (Fin 5))))-
      f (insert 2 ({0,1} : Finset (Fin 5)))-f (insert 4 ({0,1} : Finset (Fin 5)))+f {0,1}=0 at h
    have hAB : insert 2 (insert 4 ({0,1} : Finset (Fin 5)))={0,1,2,4} := by decide
    have hA : insert 2 ({0,1} : Finset (Fin 5))={0,1,2} := by decide
    have hB : insert 4 ({0,1} : Finset (Fin 5))={0,1,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h31 : f {3,4}-f {3}-f {4}+f ∅=0 := by
    have h := hf 31
    change f (insert 3 (insert 4 (∅ : Finset (Fin 5))))-
      f (insert 3 (∅ : Finset (Fin 5)))-f (insert 4 (∅ : Finset (Fin 5)))+f ∅=0 at h
    have hAB : insert 3 (insert 4 (∅ : Finset (Fin 5)))={3,4} := by decide
    have hA : insert 3 (∅ : Finset (Fin 5))={3} := by decide
    have hB : insert 4 (∅ : Finset (Fin 5))={4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have v0 : f ∅=0 := by
    linear_combination h1
  have v1 : f {0}=0 := by
    linear_combination h2
  have v2 : f {1}=0 := by
    linear_combination h3
  have v3 : f {0,1}=0 := by
    linear_combination (-1) * h1 + h2 + h3 + h7
  have v4 : f {2}=0 := by
    linear_combination h4
  have v5 : f {0,2}=0 := by
    linear_combination h0
  have v6 : f {1,2}=0 := by
    linear_combination h0 + (-1) * h2 + h3 + (-1) * h11 + (-1) * h15 + h16 + h20 + h23 + (-1) * h24
  have v7 : f {0,1,2}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + h3 + (-1) * h4 + h8 + (-1) * h11 + (-1) * h15 + h16 + h20 + h23 + (-1) * h24
  have v8 : f {3}=0 := by
    linear_combination h5
  have v9 : f {0,3}=0 := by
    linear_combination (-1) * h1 + h2 + h5 + h15
  have v10 : f {1,3}=0 := by
    linear_combination (-1) * h1 + h3 + h5 + h23
  have v11 : f {0,1,3}=0 := by
    linear_combination h0 + (-1) * h1 + h3 + (-1) * h4 + h5 + h9 + (-1) * h11 + h16 + h23
  have v12 : f {2,3}=0 := by
    linear_combination h0 + (-1) * h2 + h5 + (-1) * h7 + h8 + (-1) * h11 + h23 + (-1) * h24 + h27
  have v13 : f {0,2,3}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + (-1) * h4 + h5 + (-1) * h7 + h8 + (-1) * h11 + h16 + h23 + (-1) * h24 + h27
  have v14 : f {1,2,3}=0 := by
    linear_combination (2) * h0 + (-2) * h2 + h3 + (-1) * h4 + h5 + (-1) * h7 + h8 + (-2) * h11 + (-1) * h15 + h16 + h20 + (2) * h23 + (-1) * h24 + h27
  have v15 : f {0,1,2,3}=0 := by
    linear_combination (3) * h0 + (-2) * h2 + h3 + (-2) * h4 + h5 + (-1) * h7 + h8 + h9 + (-2) * h11 + (-1) * h15 + (2) * h16 + h20 + (2) * h23 + (-1) * h24 + h27
  have v16 : f {4}=0 := by
    linear_combination h6
  have v17 : f {0,4}=0 := by
    linear_combination h0 + (-1) * h4 + h6 + (-1) * h12 + h19
  have v18 : f {1,4}=0 := by
    linear_combination h0 + (-1) * h2 + h3 + (-1) * h4 + h6 + (-1) * h11 + (-1) * h15 + h16 + h20 + (-1) * h21 + h23 + (-1) * h24 + h26
  have v19 : f {0,1,4}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + h3 + (-2) * h4 + h6 + h10 + (-1) * h11 + (-1) * h12 + (-1) * h15 + h16 + h19 + h20 + (-1) * h21 + h23 + (-1) * h24 + h26
  have v20 : f {2,4}=0 := by
    linear_combination h0 + (-1) * h2 + h6 + (-1) * h12 + h29
  have v21 : f {0,2,4}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + (-1) * h4 + h6 + (-1) * h12 + h19 + h29
  have v22 : f {1,2,4}=0 := by
    linear_combination (2) * h0 + (-2) * h2 + h3 + (-1) * h4 + h6 + (-1) * h11 + (-1) * h12 + (-1) * h15 + h16 + h20 + h23 + (-1) * h24 + h26 + h29
  have v23 : f {0,1,2,4}=0 := by
    linear_combination (4) * h0 + h1 + (-3) * h2 + h3 + (-3) * h4 + h6 + (-1) * h7 + h8 + h10 + (-2) * h11 + (-1) * h12 + (-2) * h15 + (2) * h16 + h19 + (2) * h20 + (-1) * h21 + (2) * h23 + (-2) * h24 + h26 + h30
  have v24 : f {3,4}=0 := by
    linear_combination (-1) * h1 + h5 + h6 + h31
  have v25 : f {0,3,4}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h4 + h5 + h6 + (-1) * h12 + h17 + h19 + h31
  have v26 : f {1,3,4}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h2 + h3 + (-1) * h4 + h5 + h6 + (-1) * h11 + (-1) * h15 + h16 + h20 + (-1) * h21 + h23 + (-1) * h24 + h25 + h26 + h31
  have v27 : f {0,1,3,4}=0 := by
    linear_combination (3) * h0 + (-2) * h2 + h3 + (-3) * h4 + h5 + h6 + (-1) * h7 + h8 + h10 + (-2) * h11 + (-1) * h14 + (-2) * h15 + (2) * h16 + h18 + h19 + (2) * h20 + (-2) * h21 + (2) * h23 + (-2) * h24 + h25 + h26 + (-1) * h29 + h30 + h31
  have v28 : f {2,3,4}=0 := by
    linear_combination (2) * h0 + (-2) * h2 + (-1) * h4 + h5 + h6 + (-1) * h7 + h8 + (-1) * h11 + (-1) * h14 + (-1) * h15 + h16 + h20 + (-1) * h22 + h23 + (-1) * h24 + h28 + h30 + h31
  have v29 : f {0,2,3,4}=0 := by
    linear_combination (3) * h0 + (-2) * h2 + (-2) * h4 + h5 + h6 + (-1) * h7 + h8 + (-1) * h11 + (-1) * h12 + h13 + (-1) * h14 + (-1) * h15 + h16 + h17 + h19 + h20 + (-1) * h22 + h23 + (-1) * h24 + h28 + h30 + h31
  have v30 : f {1,2,3,4}=0 := by
    linear_combination (3) * h0 + (-3) * h2 + h3 + (-2) * h4 + h5 + h6 + (-1) * h7 + h8 + (-2) * h11 + (-1) * h14 + (-2) * h15 + (2) * h16 + (2) * h20 + (-1) * h21 + (2) * h23 + (-2) * h24 + h25 + h26 + h28 + h30 + h31
  have v31 : f {0,1,2,3,4}=0 := by
    linear_combination (5) * h0 + h1 + (-4) * h2 + h3 + (-4) * h4 + h5 + h6 + (-2) * h7 + (2) * h8 + h10 + (-3) * h11 + (-1) * h14 + (-3) * h15 + (3) * h16 + h18 + h19 + (3) * h20 + (-2) * h21 + (3) * h23 + (-3) * h24 + h25 + h26 + h28 + (-1) * h29 + (2) * h30 + h31
  funext S
  change f S=0
  have casesS : ∀ S : Finset (Fin 5), S=∅ ∨ S={0} ∨ S={1} ∨ S={0,1} ∨ S={2} ∨ S={0,2} ∨ S={1,2} ∨ S={0,1,2} ∨ S={3} ∨ S={0,3} ∨ S={1,3} ∨ S={0,1,3} ∨ S={2,3} ∨ S={0,2,3} ∨ S={1,2,3} ∨ S={0,1,2,3} ∨ S={4} ∨ S={0,4} ∨ S={1,4} ∨ S={0,1,4} ∨ S={2,4} ∨ S={0,2,4} ∨ S={1,2,4} ∨ S={0,1,2,4} ∨ S={3,4} ∨ S={0,3,4} ∨ S={1,3,4} ∨ S={0,1,3,4} ∨ S={2,3,4} ∨ S={0,2,3,4} ∨ S={1,2,3,4} ∨ S={0,1,2,3,4} := by decide
  rcases casesS S with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem empty_zero : integerFunction ∅=0 := by decide

theorem singleton_zero : ∀ v : Fin 5,integerFunction {v}=0 := by decide

theorem boolean_differences : ∀ u v : Fin 5,u≠v → ∀ S : Finset (Fin 5),
    u∉S → v∉S → integerDelta integerFunction u v S=0 ∨
      integerDelta integerFunction u v S=1 := by decide

theorem extreme : ExtremeSupermodular (realFunction integerFunction) :=
  extreme_of_row_kernel integerFunction rows pivot pivot_one row_zero valid_rows
    row_kernel_zero empty_zero singleton_zero boolean_differences

end K1112Complement

namespace K1122

def integerFunction (S : Finset (Fin 6)) : ℤ :=
  (match subsetMask S with
  | 3 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 3
  | 9 => 1
  | 10 => 1
  | 11 => 2
  | 13 => 2
  | 14 => 2
  | 15 => 4
  | 17 => 1
  | 18 => 1
  | 19 => 3
  | 20 => 1
  | 21 => 3
  | 22 => 3
  | 23 => 5
  | 24 => 1
  | 25 => 2
  | 26 => 2
  | 27 => 4
  | 28 => 2
  | 29 => 4
  | 30 => 4
  | 31 => 6
  | 33 => 1
  | 34 => 1
  | 35 => 2
  | 36 => 1
  | 37 => 2
  | 38 => 2
  | 39 => 4
  | 41 => 2
  | 42 => 2
  | 43 => 4
  | 44 => 1
  | 45 => 3
  | 46 => 3
  | 47 => 6
  | 49 => 2
  | 50 => 2
  | 51 => 4
  | 52 => 2
  | 53 => 4
  | 54 => 4
  | 55 => 6
  | 56 => 1
  | 57 => 3
  | 58 => 3
  | 59 => 6
  | 60 => 3
  | 61 => 5
  | 62 => 5
  | 63 => 8
  | _ => 0)

def rows : Fin 64 → Row (Fin 6) :=
  ![.value {0,1},.value ∅,.value {0},.value {1},.value {2},.value {3},.value {4},.value {5},.elemental 0 1 {3},.elemental 0 1 {2,3},.elemental 0 1 {2,4},.elemental 0 1 {2,3,4},.elemental 0 1 {5},.elemental 0 1 {3,5},.elemental 0 1 {4,5},.elemental 0 1 {2,4,5},.elemental 0 2 {1,4},.elemental 0 2 {1,3,4},.elemental 0 2 {5},.elemental 0 2 {3,5},.elemental 0 2 {4,5},.elemental 0 2 {3,4,5},.elemental 0 2 {1,3,4,5},.elemental 0 3 {1},.elemental 0 3 {1,2},.elemental 0 3 {4},.elemental 0 3 {1,4},.elemental 0 3 {4,5},.elemental 0 4 {1,2},.elemental 0 4 {3},.elemental 0 4 {1,2,5},.elemental 0 4 {3,5},.elemental 0 4 {1,2,3,5},.elemental 0 5 {1},.elemental 0 5 {2},.elemental 0 5 {1,2},.elemental 1 2 {0,4},.elemental 1 2 {0,3,4},.elemental 1 2 {5},.elemental 1 2 {3,5},.elemental 1 2 {4,5},.elemental 1 2 {3,4,5},.elemental 1 3 {0},.elemental 1 3 {0,2},.elemental 1 3 {4},.elemental 1 3 {4,5},.elemental 1 4 {0,2},.elemental 1 4 {3},.elemental 1 4 {0,2,5},.elemental 1 4 {3,5},.elemental 1 5 {0},.elemental 2 3 ∅,.elemental 2 3 {0},.elemental 2 3 {4},.elemental 2 3 {5},.elemental 2 3 {0,1,5},.elemental 2 3 {4,5},.elemental 2 4 {0,1},.elemental 2 4 {0,1,5},.elemental 2 5 {0},.elemental 3 4 {0},.elemental 3 4 {0,5},.elemental 3 5 ∅,.elemental 4 5 ∅]

def pivot : Finset (Fin 6) := {0,1}

theorem pivot_one : integerFunction pivot=1 := by decide

theorem row_zero : rows 0=.value pivot := by decide

theorem valid_rows : ∀ i : Fin 64,i≠0 → (rows i).valid integerFunction := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 4096 in
theorem row_kernel_zero (f : SetFunction (Fin 6))
    (hf : ∀ i : Fin 64,(rows i).eval f=0) : f=0 := by
  have h0 : f {0,1}=0 := hf 0
  have h1 : f ∅=0 := hf 1
  have h2 : f {0}=0 := hf 2
  have h3 : f {1}=0 := hf 3
  have h4 : f {2}=0 := hf 4
  have h5 : f {3}=0 := hf 5
  have h6 : f {4}=0 := hf 6
  have h7 : f {5}=0 := hf 7
  have h8 : f {0,1,3}-f {0,3}-f {1,3}+f {3}=0 := by
    have h := hf 8
    change f (insert 0 (insert 1 ({3} : Finset (Fin 6))))-
      f (insert 0 ({3} : Finset (Fin 6)))-f (insert 1 ({3} : Finset (Fin 6)))+f {3}=0 at h
    have hAB : insert 0 (insert 1 ({3} : Finset (Fin 6)))={0,1,3} := by decide
    have hA : insert 0 ({3} : Finset (Fin 6))={0,3} := by decide
    have hB : insert 1 ({3} : Finset (Fin 6))={1,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h9 : f {0,1,2,3}-f {0,2,3}-f {1,2,3}+f {2,3}=0 := by
    have h := hf 9
    change f (insert 0 (insert 1 ({2,3} : Finset (Fin 6))))-
      f (insert 0 ({2,3} : Finset (Fin 6)))-f (insert 1 ({2,3} : Finset (Fin 6)))+f {2,3}=0 at h
    have hAB : insert 0 (insert 1 ({2,3} : Finset (Fin 6)))={0,1,2,3} := by decide
    have hA : insert 0 ({2,3} : Finset (Fin 6))={0,2,3} := by decide
    have hB : insert 1 ({2,3} : Finset (Fin 6))={1,2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h10 : f {0,1,2,4}-f {0,2,4}-f {1,2,4}+f {2,4}=0 := by
    have h := hf 10
    change f (insert 0 (insert 1 ({2,4} : Finset (Fin 6))))-
      f (insert 0 ({2,4} : Finset (Fin 6)))-f (insert 1 ({2,4} : Finset (Fin 6)))+f {2,4}=0 at h
    have hAB : insert 0 (insert 1 ({2,4} : Finset (Fin 6)))={0,1,2,4} := by decide
    have hA : insert 0 ({2,4} : Finset (Fin 6))={0,2,4} := by decide
    have hB : insert 1 ({2,4} : Finset (Fin 6))={1,2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h11 : f {0,1,2,3,4}-f {0,2,3,4}-f {1,2,3,4}+f {2,3,4}=0 := by
    have h := hf 11
    change f (insert 0 (insert 1 ({2,3,4} : Finset (Fin 6))))-
      f (insert 0 ({2,3,4} : Finset (Fin 6)))-f (insert 1 ({2,3,4} : Finset (Fin 6)))+f {2,3,4}=0 at h
    have hAB : insert 0 (insert 1 ({2,3,4} : Finset (Fin 6)))={0,1,2,3,4} := by decide
    have hA : insert 0 ({2,3,4} : Finset (Fin 6))={0,2,3,4} := by decide
    have hB : insert 1 ({2,3,4} : Finset (Fin 6))={1,2,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h12 : f {0,1,5}-f {0,5}-f {1,5}+f {5}=0 := by
    have h := hf 12
    change f (insert 0 (insert 1 ({5} : Finset (Fin 6))))-
      f (insert 0 ({5} : Finset (Fin 6)))-f (insert 1 ({5} : Finset (Fin 6)))+f {5}=0 at h
    have hAB : insert 0 (insert 1 ({5} : Finset (Fin 6)))={0,1,5} := by decide
    have hA : insert 0 ({5} : Finset (Fin 6))={0,5} := by decide
    have hB : insert 1 ({5} : Finset (Fin 6))={1,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h13 : f {0,1,3,5}-f {0,3,5}-f {1,3,5}+f {3,5}=0 := by
    have h := hf 13
    change f (insert 0 (insert 1 ({3,5} : Finset (Fin 6))))-
      f (insert 0 ({3,5} : Finset (Fin 6)))-f (insert 1 ({3,5} : Finset (Fin 6)))+f {3,5}=0 at h
    have hAB : insert 0 (insert 1 ({3,5} : Finset (Fin 6)))={0,1,3,5} := by decide
    have hA : insert 0 ({3,5} : Finset (Fin 6))={0,3,5} := by decide
    have hB : insert 1 ({3,5} : Finset (Fin 6))={1,3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h14 : f {0,1,4,5}-f {0,4,5}-f {1,4,5}+f {4,5}=0 := by
    have h := hf 14
    change f (insert 0 (insert 1 ({4,5} : Finset (Fin 6))))-
      f (insert 0 ({4,5} : Finset (Fin 6)))-f (insert 1 ({4,5} : Finset (Fin 6)))+f {4,5}=0 at h
    have hAB : insert 0 (insert 1 ({4,5} : Finset (Fin 6)))={0,1,4,5} := by decide
    have hA : insert 0 ({4,5} : Finset (Fin 6))={0,4,5} := by decide
    have hB : insert 1 ({4,5} : Finset (Fin 6))={1,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h15 : f {0,1,2,4,5}-f {0,2,4,5}-f {1,2,4,5}+f {2,4,5}=0 := by
    have h := hf 15
    change f (insert 0 (insert 1 ({2,4,5} : Finset (Fin 6))))-
      f (insert 0 ({2,4,5} : Finset (Fin 6)))-f (insert 1 ({2,4,5} : Finset (Fin 6)))+f {2,4,5}=0 at h
    have hAB : insert 0 (insert 1 ({2,4,5} : Finset (Fin 6)))={0,1,2,4,5} := by decide
    have hA : insert 0 ({2,4,5} : Finset (Fin 6))={0,2,4,5} := by decide
    have hB : insert 1 ({2,4,5} : Finset (Fin 6))={1,2,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h16 : f {0,1,2,4}-f {0,1,4}-f {1,2,4}+f {1,4}=0 := by
    have h := hf 16
    change f (insert 0 (insert 2 ({1,4} : Finset (Fin 6))))-
      f (insert 0 ({1,4} : Finset (Fin 6)))-f (insert 2 ({1,4} : Finset (Fin 6)))+f {1,4}=0 at h
    have hAB : insert 0 (insert 2 ({1,4} : Finset (Fin 6)))={0,1,2,4} := by decide
    have hA : insert 0 ({1,4} : Finset (Fin 6))={0,1,4} := by decide
    have hB : insert 2 ({1,4} : Finset (Fin 6))={1,2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h17 : f {0,1,2,3,4}-f {0,1,3,4}-f {1,2,3,4}+f {1,3,4}=0 := by
    have h := hf 17
    change f (insert 0 (insert 2 ({1,3,4} : Finset (Fin 6))))-
      f (insert 0 ({1,3,4} : Finset (Fin 6)))-f (insert 2 ({1,3,4} : Finset (Fin 6)))+f {1,3,4}=0 at h
    have hAB : insert 0 (insert 2 ({1,3,4} : Finset (Fin 6)))={0,1,2,3,4} := by decide
    have hA : insert 0 ({1,3,4} : Finset (Fin 6))={0,1,3,4} := by decide
    have hB : insert 2 ({1,3,4} : Finset (Fin 6))={1,2,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h18 : f {0,2,5}-f {0,5}-f {2,5}+f {5}=0 := by
    have h := hf 18
    change f (insert 0 (insert 2 ({5} : Finset (Fin 6))))-
      f (insert 0 ({5} : Finset (Fin 6)))-f (insert 2 ({5} : Finset (Fin 6)))+f {5}=0 at h
    have hAB : insert 0 (insert 2 ({5} : Finset (Fin 6)))={0,2,5} := by decide
    have hA : insert 0 ({5} : Finset (Fin 6))={0,5} := by decide
    have hB : insert 2 ({5} : Finset (Fin 6))={2,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h19 : f {0,2,3,5}-f {0,3,5}-f {2,3,5}+f {3,5}=0 := by
    have h := hf 19
    change f (insert 0 (insert 2 ({3,5} : Finset (Fin 6))))-
      f (insert 0 ({3,5} : Finset (Fin 6)))-f (insert 2 ({3,5} : Finset (Fin 6)))+f {3,5}=0 at h
    have hAB : insert 0 (insert 2 ({3,5} : Finset (Fin 6)))={0,2,3,5} := by decide
    have hA : insert 0 ({3,5} : Finset (Fin 6))={0,3,5} := by decide
    have hB : insert 2 ({3,5} : Finset (Fin 6))={2,3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h20 : f {0,2,4,5}-f {0,4,5}-f {2,4,5}+f {4,5}=0 := by
    have h := hf 20
    change f (insert 0 (insert 2 ({4,5} : Finset (Fin 6))))-
      f (insert 0 ({4,5} : Finset (Fin 6)))-f (insert 2 ({4,5} : Finset (Fin 6)))+f {4,5}=0 at h
    have hAB : insert 0 (insert 2 ({4,5} : Finset (Fin 6)))={0,2,4,5} := by decide
    have hA : insert 0 ({4,5} : Finset (Fin 6))={0,4,5} := by decide
    have hB : insert 2 ({4,5} : Finset (Fin 6))={2,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h21 : f {0,2,3,4,5}-f {0,3,4,5}-f {2,3,4,5}+f {3,4,5}=0 := by
    have h := hf 21
    change f (insert 0 (insert 2 ({3,4,5} : Finset (Fin 6))))-
      f (insert 0 ({3,4,5} : Finset (Fin 6)))-f (insert 2 ({3,4,5} : Finset (Fin 6)))+f {3,4,5}=0 at h
    have hAB : insert 0 (insert 2 ({3,4,5} : Finset (Fin 6)))={0,2,3,4,5} := by decide
    have hA : insert 0 ({3,4,5} : Finset (Fin 6))={0,3,4,5} := by decide
    have hB : insert 2 ({3,4,5} : Finset (Fin 6))={2,3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h22 : f {0,1,2,3,4,5}-f {0,1,3,4,5}-f {1,2,3,4,5}+f {1,3,4,5}=0 := by
    have h := hf 22
    change f (insert 0 (insert 2 ({1,3,4,5} : Finset (Fin 6))))-
      f (insert 0 ({1,3,4,5} : Finset (Fin 6)))-f (insert 2 ({1,3,4,5} : Finset (Fin 6)))+f {1,3,4,5}=0 at h
    have hAB : insert 0 (insert 2 ({1,3,4,5} : Finset (Fin 6)))={0,1,2,3,4,5} := by decide
    have hA : insert 0 ({1,3,4,5} : Finset (Fin 6))={0,1,3,4,5} := by decide
    have hB : insert 2 ({1,3,4,5} : Finset (Fin 6))={1,2,3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h23 : f {0,1,3}-f {0,1}-f {1,3}+f {1}=0 := by
    have h := hf 23
    change f (insert 0 (insert 3 ({1} : Finset (Fin 6))))-
      f (insert 0 ({1} : Finset (Fin 6)))-f (insert 3 ({1} : Finset (Fin 6)))+f {1}=0 at h
    have hAB : insert 0 (insert 3 ({1} : Finset (Fin 6)))={0,1,3} := by decide
    have hA : insert 0 ({1} : Finset (Fin 6))={0,1} := by decide
    have hB : insert 3 ({1} : Finset (Fin 6))={1,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h24 : f {0,1,2,3}-f {0,1,2}-f {1,2,3}+f {1,2}=0 := by
    have h := hf 24
    change f (insert 0 (insert 3 ({1,2} : Finset (Fin 6))))-
      f (insert 0 ({1,2} : Finset (Fin 6)))-f (insert 3 ({1,2} : Finset (Fin 6)))+f {1,2}=0 at h
    have hAB : insert 0 (insert 3 ({1,2} : Finset (Fin 6)))={0,1,2,3} := by decide
    have hA : insert 0 ({1,2} : Finset (Fin 6))={0,1,2} := by decide
    have hB : insert 3 ({1,2} : Finset (Fin 6))={1,2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h25 : f {0,3,4}-f {0,4}-f {3,4}+f {4}=0 := by
    have h := hf 25
    change f (insert 0 (insert 3 ({4} : Finset (Fin 6))))-
      f (insert 0 ({4} : Finset (Fin 6)))-f (insert 3 ({4} : Finset (Fin 6)))+f {4}=0 at h
    have hAB : insert 0 (insert 3 ({4} : Finset (Fin 6)))={0,3,4} := by decide
    have hA : insert 0 ({4} : Finset (Fin 6))={0,4} := by decide
    have hB : insert 3 ({4} : Finset (Fin 6))={3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h26 : f {0,1,3,4}-f {0,1,4}-f {1,3,4}+f {1,4}=0 := by
    have h := hf 26
    change f (insert 0 (insert 3 ({1,4} : Finset (Fin 6))))-
      f (insert 0 ({1,4} : Finset (Fin 6)))-f (insert 3 ({1,4} : Finset (Fin 6)))+f {1,4}=0 at h
    have hAB : insert 0 (insert 3 ({1,4} : Finset (Fin 6)))={0,1,3,4} := by decide
    have hA : insert 0 ({1,4} : Finset (Fin 6))={0,1,4} := by decide
    have hB : insert 3 ({1,4} : Finset (Fin 6))={1,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h27 : f {0,3,4,5}-f {0,4,5}-f {3,4,5}+f {4,5}=0 := by
    have h := hf 27
    change f (insert 0 (insert 3 ({4,5} : Finset (Fin 6))))-
      f (insert 0 ({4,5} : Finset (Fin 6)))-f (insert 3 ({4,5} : Finset (Fin 6)))+f {4,5}=0 at h
    have hAB : insert 0 (insert 3 ({4,5} : Finset (Fin 6)))={0,3,4,5} := by decide
    have hA : insert 0 ({4,5} : Finset (Fin 6))={0,4,5} := by decide
    have hB : insert 3 ({4,5} : Finset (Fin 6))={3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h28 : f {0,1,2,4}-f {0,1,2}-f {1,2,4}+f {1,2}=0 := by
    have h := hf 28
    change f (insert 0 (insert 4 ({1,2} : Finset (Fin 6))))-
      f (insert 0 ({1,2} : Finset (Fin 6)))-f (insert 4 ({1,2} : Finset (Fin 6)))+f {1,2}=0 at h
    have hAB : insert 0 (insert 4 ({1,2} : Finset (Fin 6)))={0,1,2,4} := by decide
    have hA : insert 0 ({1,2} : Finset (Fin 6))={0,1,2} := by decide
    have hB : insert 4 ({1,2} : Finset (Fin 6))={1,2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h29 : f {0,3,4}-f {0,3}-f {3,4}+f {3}=0 := by
    have h := hf 29
    change f (insert 0 (insert 4 ({3} : Finset (Fin 6))))-
      f (insert 0 ({3} : Finset (Fin 6)))-f (insert 4 ({3} : Finset (Fin 6)))+f {3}=0 at h
    have hAB : insert 0 (insert 4 ({3} : Finset (Fin 6)))={0,3,4} := by decide
    have hA : insert 0 ({3} : Finset (Fin 6))={0,3} := by decide
    have hB : insert 4 ({3} : Finset (Fin 6))={3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h30 : f {0,1,2,4,5}-f {0,1,2,5}-f {1,2,4,5}+f {1,2,5}=0 := by
    have h := hf 30
    change f (insert 0 (insert 4 ({1,2,5} : Finset (Fin 6))))-
      f (insert 0 ({1,2,5} : Finset (Fin 6)))-f (insert 4 ({1,2,5} : Finset (Fin 6)))+f {1,2,5}=0 at h
    have hAB : insert 0 (insert 4 ({1,2,5} : Finset (Fin 6)))={0,1,2,4,5} := by decide
    have hA : insert 0 ({1,2,5} : Finset (Fin 6))={0,1,2,5} := by decide
    have hB : insert 4 ({1,2,5} : Finset (Fin 6))={1,2,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h31 : f {0,3,4,5}-f {0,3,5}-f {3,4,5}+f {3,5}=0 := by
    have h := hf 31
    change f (insert 0 (insert 4 ({3,5} : Finset (Fin 6))))-
      f (insert 0 ({3,5} : Finset (Fin 6)))-f (insert 4 ({3,5} : Finset (Fin 6)))+f {3,5}=0 at h
    have hAB : insert 0 (insert 4 ({3,5} : Finset (Fin 6)))={0,3,4,5} := by decide
    have hA : insert 0 ({3,5} : Finset (Fin 6))={0,3,5} := by decide
    have hB : insert 4 ({3,5} : Finset (Fin 6))={3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h32 : f {0,1,2,3,4,5}-f {0,1,2,3,5}-f {1,2,3,4,5}+f {1,2,3,5}=0 := by
    have h := hf 32
    change f (insert 0 (insert 4 ({1,2,3,5} : Finset (Fin 6))))-
      f (insert 0 ({1,2,3,5} : Finset (Fin 6)))-f (insert 4 ({1,2,3,5} : Finset (Fin 6)))+f {1,2,3,5}=0 at h
    have hAB : insert 0 (insert 4 ({1,2,3,5} : Finset (Fin 6)))={0,1,2,3,4,5} := by decide
    have hA : insert 0 ({1,2,3,5} : Finset (Fin 6))={0,1,2,3,5} := by decide
    have hB : insert 4 ({1,2,3,5} : Finset (Fin 6))={1,2,3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h33 : f {0,1,5}-f {0,1}-f {1,5}+f {1}=0 := by
    have h := hf 33
    change f (insert 0 (insert 5 ({1} : Finset (Fin 6))))-
      f (insert 0 ({1} : Finset (Fin 6)))-f (insert 5 ({1} : Finset (Fin 6)))+f {1}=0 at h
    have hAB : insert 0 (insert 5 ({1} : Finset (Fin 6)))={0,1,5} := by decide
    have hA : insert 0 ({1} : Finset (Fin 6))={0,1} := by decide
    have hB : insert 5 ({1} : Finset (Fin 6))={1,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h34 : f {0,2,5}-f {0,2}-f {2,5}+f {2}=0 := by
    have h := hf 34
    change f (insert 0 (insert 5 ({2} : Finset (Fin 6))))-
      f (insert 0 ({2} : Finset (Fin 6)))-f (insert 5 ({2} : Finset (Fin 6)))+f {2}=0 at h
    have hAB : insert 0 (insert 5 ({2} : Finset (Fin 6)))={0,2,5} := by decide
    have hA : insert 0 ({2} : Finset (Fin 6))={0,2} := by decide
    have hB : insert 5 ({2} : Finset (Fin 6))={2,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h35 : f {0,1,2,5}-f {0,1,2}-f {1,2,5}+f {1,2}=0 := by
    have h := hf 35
    change f (insert 0 (insert 5 ({1,2} : Finset (Fin 6))))-
      f (insert 0 ({1,2} : Finset (Fin 6)))-f (insert 5 ({1,2} : Finset (Fin 6)))+f {1,2}=0 at h
    have hAB : insert 0 (insert 5 ({1,2} : Finset (Fin 6)))={0,1,2,5} := by decide
    have hA : insert 0 ({1,2} : Finset (Fin 6))={0,1,2} := by decide
    have hB : insert 5 ({1,2} : Finset (Fin 6))={1,2,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h36 : f {0,1,2,4}-f {0,1,4}-f {0,2,4}+f {0,4}=0 := by
    have h := hf 36
    change f (insert 1 (insert 2 ({0,4} : Finset (Fin 6))))-
      f (insert 1 ({0,4} : Finset (Fin 6)))-f (insert 2 ({0,4} : Finset (Fin 6)))+f {0,4}=0 at h
    have hAB : insert 1 (insert 2 ({0,4} : Finset (Fin 6)))={0,1,2,4} := by decide
    have hA : insert 1 ({0,4} : Finset (Fin 6))={0,1,4} := by decide
    have hB : insert 2 ({0,4} : Finset (Fin 6))={0,2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h37 : f {0,1,2,3,4}-f {0,1,3,4}-f {0,2,3,4}+f {0,3,4}=0 := by
    have h := hf 37
    change f (insert 1 (insert 2 ({0,3,4} : Finset (Fin 6))))-
      f (insert 1 ({0,3,4} : Finset (Fin 6)))-f (insert 2 ({0,3,4} : Finset (Fin 6)))+f {0,3,4}=0 at h
    have hAB : insert 1 (insert 2 ({0,3,4} : Finset (Fin 6)))={0,1,2,3,4} := by decide
    have hA : insert 1 ({0,3,4} : Finset (Fin 6))={0,1,3,4} := by decide
    have hB : insert 2 ({0,3,4} : Finset (Fin 6))={0,2,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h38 : f {1,2,5}-f {1,5}-f {2,5}+f {5}=0 := by
    have h := hf 38
    change f (insert 1 (insert 2 ({5} : Finset (Fin 6))))-
      f (insert 1 ({5} : Finset (Fin 6)))-f (insert 2 ({5} : Finset (Fin 6)))+f {5}=0 at h
    have hAB : insert 1 (insert 2 ({5} : Finset (Fin 6)))={1,2,5} := by decide
    have hA : insert 1 ({5} : Finset (Fin 6))={1,5} := by decide
    have hB : insert 2 ({5} : Finset (Fin 6))={2,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h39 : f {1,2,3,5}-f {1,3,5}-f {2,3,5}+f {3,5}=0 := by
    have h := hf 39
    change f (insert 1 (insert 2 ({3,5} : Finset (Fin 6))))-
      f (insert 1 ({3,5} : Finset (Fin 6)))-f (insert 2 ({3,5} : Finset (Fin 6)))+f {3,5}=0 at h
    have hAB : insert 1 (insert 2 ({3,5} : Finset (Fin 6)))={1,2,3,5} := by decide
    have hA : insert 1 ({3,5} : Finset (Fin 6))={1,3,5} := by decide
    have hB : insert 2 ({3,5} : Finset (Fin 6))={2,3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h40 : f {1,2,4,5}-f {1,4,5}-f {2,4,5}+f {4,5}=0 := by
    have h := hf 40
    change f (insert 1 (insert 2 ({4,5} : Finset (Fin 6))))-
      f (insert 1 ({4,5} : Finset (Fin 6)))-f (insert 2 ({4,5} : Finset (Fin 6)))+f {4,5}=0 at h
    have hAB : insert 1 (insert 2 ({4,5} : Finset (Fin 6)))={1,2,4,5} := by decide
    have hA : insert 1 ({4,5} : Finset (Fin 6))={1,4,5} := by decide
    have hB : insert 2 ({4,5} : Finset (Fin 6))={2,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h41 : f {1,2,3,4,5}-f {1,3,4,5}-f {2,3,4,5}+f {3,4,5}=0 := by
    have h := hf 41
    change f (insert 1 (insert 2 ({3,4,5} : Finset (Fin 6))))-
      f (insert 1 ({3,4,5} : Finset (Fin 6)))-f (insert 2 ({3,4,5} : Finset (Fin 6)))+f {3,4,5}=0 at h
    have hAB : insert 1 (insert 2 ({3,4,5} : Finset (Fin 6)))={1,2,3,4,5} := by decide
    have hA : insert 1 ({3,4,5} : Finset (Fin 6))={1,3,4,5} := by decide
    have hB : insert 2 ({3,4,5} : Finset (Fin 6))={2,3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h42 : f {0,1,3}-f {0,1}-f {0,3}+f {0}=0 := by
    have h := hf 42
    change f (insert 1 (insert 3 ({0} : Finset (Fin 6))))-
      f (insert 1 ({0} : Finset (Fin 6)))-f (insert 3 ({0} : Finset (Fin 6)))+f {0}=0 at h
    have hAB : insert 1 (insert 3 ({0} : Finset (Fin 6)))={0,1,3} := by decide
    have hA : insert 1 ({0} : Finset (Fin 6))={0,1} := by decide
    have hB : insert 3 ({0} : Finset (Fin 6))={0,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h43 : f {0,1,2,3}-f {0,1,2}-f {0,2,3}+f {0,2}=0 := by
    have h := hf 43
    change f (insert 1 (insert 3 ({0,2} : Finset (Fin 6))))-
      f (insert 1 ({0,2} : Finset (Fin 6)))-f (insert 3 ({0,2} : Finset (Fin 6)))+f {0,2}=0 at h
    have hAB : insert 1 (insert 3 ({0,2} : Finset (Fin 6)))={0,1,2,3} := by decide
    have hA : insert 1 ({0,2} : Finset (Fin 6))={0,1,2} := by decide
    have hB : insert 3 ({0,2} : Finset (Fin 6))={0,2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h44 : f {1,3,4}-f {1,4}-f {3,4}+f {4}=0 := by
    have h := hf 44
    change f (insert 1 (insert 3 ({4} : Finset (Fin 6))))-
      f (insert 1 ({4} : Finset (Fin 6)))-f (insert 3 ({4} : Finset (Fin 6)))+f {4}=0 at h
    have hAB : insert 1 (insert 3 ({4} : Finset (Fin 6)))={1,3,4} := by decide
    have hA : insert 1 ({4} : Finset (Fin 6))={1,4} := by decide
    have hB : insert 3 ({4} : Finset (Fin 6))={3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h45 : f {1,3,4,5}-f {1,4,5}-f {3,4,5}+f {4,5}=0 := by
    have h := hf 45
    change f (insert 1 (insert 3 ({4,5} : Finset (Fin 6))))-
      f (insert 1 ({4,5} : Finset (Fin 6)))-f (insert 3 ({4,5} : Finset (Fin 6)))+f {4,5}=0 at h
    have hAB : insert 1 (insert 3 ({4,5} : Finset (Fin 6)))={1,3,4,5} := by decide
    have hA : insert 1 ({4,5} : Finset (Fin 6))={1,4,5} := by decide
    have hB : insert 3 ({4,5} : Finset (Fin 6))={3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h46 : f {0,1,2,4}-f {0,1,2}-f {0,2,4}+f {0,2}=0 := by
    have h := hf 46
    change f (insert 1 (insert 4 ({0,2} : Finset (Fin 6))))-
      f (insert 1 ({0,2} : Finset (Fin 6)))-f (insert 4 ({0,2} : Finset (Fin 6)))+f {0,2}=0 at h
    have hAB : insert 1 (insert 4 ({0,2} : Finset (Fin 6)))={0,1,2,4} := by decide
    have hA : insert 1 ({0,2} : Finset (Fin 6))={0,1,2} := by decide
    have hB : insert 4 ({0,2} : Finset (Fin 6))={0,2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h47 : f {1,3,4}-f {1,3}-f {3,4}+f {3}=0 := by
    have h := hf 47
    change f (insert 1 (insert 4 ({3} : Finset (Fin 6))))-
      f (insert 1 ({3} : Finset (Fin 6)))-f (insert 4 ({3} : Finset (Fin 6)))+f {3}=0 at h
    have hAB : insert 1 (insert 4 ({3} : Finset (Fin 6)))={1,3,4} := by decide
    have hA : insert 1 ({3} : Finset (Fin 6))={1,3} := by decide
    have hB : insert 4 ({3} : Finset (Fin 6))={3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h48 : f {0,1,2,4,5}-f {0,1,2,5}-f {0,2,4,5}+f {0,2,5}=0 := by
    have h := hf 48
    change f (insert 1 (insert 4 ({0,2,5} : Finset (Fin 6))))-
      f (insert 1 ({0,2,5} : Finset (Fin 6)))-f (insert 4 ({0,2,5} : Finset (Fin 6)))+f {0,2,5}=0 at h
    have hAB : insert 1 (insert 4 ({0,2,5} : Finset (Fin 6)))={0,1,2,4,5} := by decide
    have hA : insert 1 ({0,2,5} : Finset (Fin 6))={0,1,2,5} := by decide
    have hB : insert 4 ({0,2,5} : Finset (Fin 6))={0,2,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h49 : f {1,3,4,5}-f {1,3,5}-f {3,4,5}+f {3,5}=0 := by
    have h := hf 49
    change f (insert 1 (insert 4 ({3,5} : Finset (Fin 6))))-
      f (insert 1 ({3,5} : Finset (Fin 6)))-f (insert 4 ({3,5} : Finset (Fin 6)))+f {3,5}=0 at h
    have hAB : insert 1 (insert 4 ({3,5} : Finset (Fin 6)))={1,3,4,5} := by decide
    have hA : insert 1 ({3,5} : Finset (Fin 6))={1,3,5} := by decide
    have hB : insert 4 ({3,5} : Finset (Fin 6))={3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h50 : f {0,1,5}-f {0,1}-f {0,5}+f {0}=0 := by
    have h := hf 50
    change f (insert 1 (insert 5 ({0} : Finset (Fin 6))))-
      f (insert 1 ({0} : Finset (Fin 6)))-f (insert 5 ({0} : Finset (Fin 6)))+f {0}=0 at h
    have hAB : insert 1 (insert 5 ({0} : Finset (Fin 6)))={0,1,5} := by decide
    have hA : insert 1 ({0} : Finset (Fin 6))={0,1} := by decide
    have hB : insert 5 ({0} : Finset (Fin 6))={0,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h51 : f {2,3}-f {2}-f {3}+f ∅=0 := by
    have h := hf 51
    change f (insert 2 (insert 3 (∅ : Finset (Fin 6))))-
      f (insert 2 (∅ : Finset (Fin 6)))-f (insert 3 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 2 (insert 3 (∅ : Finset (Fin 6)))={2,3} := by decide
    have hA : insert 2 (∅ : Finset (Fin 6))={2} := by decide
    have hB : insert 3 (∅ : Finset (Fin 6))={3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h52 : f {0,2,3}-f {0,2}-f {0,3}+f {0}=0 := by
    have h := hf 52
    change f (insert 2 (insert 3 ({0} : Finset (Fin 6))))-
      f (insert 2 ({0} : Finset (Fin 6)))-f (insert 3 ({0} : Finset (Fin 6)))+f {0}=0 at h
    have hAB : insert 2 (insert 3 ({0} : Finset (Fin 6)))={0,2,3} := by decide
    have hA : insert 2 ({0} : Finset (Fin 6))={0,2} := by decide
    have hB : insert 3 ({0} : Finset (Fin 6))={0,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h53 : f {2,3,4}-f {2,4}-f {3,4}+f {4}=0 := by
    have h := hf 53
    change f (insert 2 (insert 3 ({4} : Finset (Fin 6))))-
      f (insert 2 ({4} : Finset (Fin 6)))-f (insert 3 ({4} : Finset (Fin 6)))+f {4}=0 at h
    have hAB : insert 2 (insert 3 ({4} : Finset (Fin 6)))={2,3,4} := by decide
    have hA : insert 2 ({4} : Finset (Fin 6))={2,4} := by decide
    have hB : insert 3 ({4} : Finset (Fin 6))={3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h54 : f {2,3,5}-f {2,5}-f {3,5}+f {5}=0 := by
    have h := hf 54
    change f (insert 2 (insert 3 ({5} : Finset (Fin 6))))-
      f (insert 2 ({5} : Finset (Fin 6)))-f (insert 3 ({5} : Finset (Fin 6)))+f {5}=0 at h
    have hAB : insert 2 (insert 3 ({5} : Finset (Fin 6)))={2,3,5} := by decide
    have hA : insert 2 ({5} : Finset (Fin 6))={2,5} := by decide
    have hB : insert 3 ({5} : Finset (Fin 6))={3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h55 : f {0,1,2,3,5}-f {0,1,2,5}-f {0,1,3,5}+f {0,1,5}=0 := by
    have h := hf 55
    change f (insert 2 (insert 3 ({0,1,5} : Finset (Fin 6))))-
      f (insert 2 ({0,1,5} : Finset (Fin 6)))-f (insert 3 ({0,1,5} : Finset (Fin 6)))+f {0,1,5}=0 at h
    have hAB : insert 2 (insert 3 ({0,1,5} : Finset (Fin 6)))={0,1,2,3,5} := by decide
    have hA : insert 2 ({0,1,5} : Finset (Fin 6))={0,1,2,5} := by decide
    have hB : insert 3 ({0,1,5} : Finset (Fin 6))={0,1,3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h56 : f {2,3,4,5}-f {2,4,5}-f {3,4,5}+f {4,5}=0 := by
    have h := hf 56
    change f (insert 2 (insert 3 ({4,5} : Finset (Fin 6))))-
      f (insert 2 ({4,5} : Finset (Fin 6)))-f (insert 3 ({4,5} : Finset (Fin 6)))+f {4,5}=0 at h
    have hAB : insert 2 (insert 3 ({4,5} : Finset (Fin 6)))={2,3,4,5} := by decide
    have hA : insert 2 ({4,5} : Finset (Fin 6))={2,4,5} := by decide
    have hB : insert 3 ({4,5} : Finset (Fin 6))={3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h57 : f {0,1,2,4}-f {0,1,2}-f {0,1,4}+f {0,1}=0 := by
    have h := hf 57
    change f (insert 2 (insert 4 ({0,1} : Finset (Fin 6))))-
      f (insert 2 ({0,1} : Finset (Fin 6)))-f (insert 4 ({0,1} : Finset (Fin 6)))+f {0,1}=0 at h
    have hAB : insert 2 (insert 4 ({0,1} : Finset (Fin 6)))={0,1,2,4} := by decide
    have hA : insert 2 ({0,1} : Finset (Fin 6))={0,1,2} := by decide
    have hB : insert 4 ({0,1} : Finset (Fin 6))={0,1,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h58 : f {0,1,2,4,5}-f {0,1,2,5}-f {0,1,4,5}+f {0,1,5}=0 := by
    have h := hf 58
    change f (insert 2 (insert 4 ({0,1,5} : Finset (Fin 6))))-
      f (insert 2 ({0,1,5} : Finset (Fin 6)))-f (insert 4 ({0,1,5} : Finset (Fin 6)))+f {0,1,5}=0 at h
    have hAB : insert 2 (insert 4 ({0,1,5} : Finset (Fin 6)))={0,1,2,4,5} := by decide
    have hA : insert 2 ({0,1,5} : Finset (Fin 6))={0,1,2,5} := by decide
    have hB : insert 4 ({0,1,5} : Finset (Fin 6))={0,1,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h59 : f {0,2,5}-f {0,2}-f {0,5}+f {0}=0 := by
    have h := hf 59
    change f (insert 2 (insert 5 ({0} : Finset (Fin 6))))-
      f (insert 2 ({0} : Finset (Fin 6)))-f (insert 5 ({0} : Finset (Fin 6)))+f {0}=0 at h
    have hAB : insert 2 (insert 5 ({0} : Finset (Fin 6)))={0,2,5} := by decide
    have hA : insert 2 ({0} : Finset (Fin 6))={0,2} := by decide
    have hB : insert 5 ({0} : Finset (Fin 6))={0,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h60 : f {0,3,4}-f {0,3}-f {0,4}+f {0}=0 := by
    have h := hf 60
    change f (insert 3 (insert 4 ({0} : Finset (Fin 6))))-
      f (insert 3 ({0} : Finset (Fin 6)))-f (insert 4 ({0} : Finset (Fin 6)))+f {0}=0 at h
    have hAB : insert 3 (insert 4 ({0} : Finset (Fin 6)))={0,3,4} := by decide
    have hA : insert 3 ({0} : Finset (Fin 6))={0,3} := by decide
    have hB : insert 4 ({0} : Finset (Fin 6))={0,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h61 : f {0,3,4,5}-f {0,3,5}-f {0,4,5}+f {0,5}=0 := by
    have h := hf 61
    change f (insert 3 (insert 4 ({0,5} : Finset (Fin 6))))-
      f (insert 3 ({0,5} : Finset (Fin 6)))-f (insert 4 ({0,5} : Finset (Fin 6)))+f {0,5}=0 at h
    have hAB : insert 3 (insert 4 ({0,5} : Finset (Fin 6)))={0,3,4,5} := by decide
    have hA : insert 3 ({0,5} : Finset (Fin 6))={0,3,5} := by decide
    have hB : insert 4 ({0,5} : Finset (Fin 6))={0,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h62 : f {3,5}-f {3}-f {5}+f ∅=0 := by
    have h := hf 62
    change f (insert 3 (insert 5 (∅ : Finset (Fin 6))))-
      f (insert 3 (∅ : Finset (Fin 6)))-f (insert 5 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 3 (insert 5 (∅ : Finset (Fin 6)))={3,5} := by decide
    have hA : insert 3 (∅ : Finset (Fin 6))={3} := by decide
    have hB : insert 5 (∅ : Finset (Fin 6))={5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h63 : f {4,5}-f {4}-f {5}+f ∅=0 := by
    have h := hf 63
    change f (insert 4 (insert 5 (∅ : Finset (Fin 6))))-
      f (insert 4 (∅ : Finset (Fin 6)))-f (insert 5 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 4 (insert 5 (∅ : Finset (Fin 6)))={4,5} := by decide
    have hA : insert 4 (∅ : Finset (Fin 6))={4} := by decide
    have hB : insert 5 (∅ : Finset (Fin 6))={5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have v0 : f ∅=0 := by
    linear_combination h1
  have v1 : f {0}=0 := by
    linear_combination h2
  have v2 : f {1}=0 := by
    linear_combination h3
  have v3 : f {0,1}=0 := by
    linear_combination h0
  have v4 : f {2}=0 := by
    linear_combination h4
  have v5 : f {0,2}=0 := by
    linear_combination h0 + (-1) * h3 + h4 + (-1) * h12 + h18 + h33 + (-1) * h34
  have v6 : f {1,2}=0 := by
    linear_combination h0 + (-1) * h2 + h4 + (-1) * h12 + (-1) * h16 + h18 + (-1) * h23 + h25 + h28 + (-1) * h29 + h33 + (-1) * h34 + h36 + h42 + (-1) * h44 + (-1) * h46 + h47
  have v7 : f {0,1,2}=0 := by
    linear_combination (3) * h0 + h1 + (-2) * h2 + (-2) * h3 + h4 + (-1) * h8 + h9 + (-2) * h12 + (-1) * h16 + (2) * h18 + (-1) * h24 + h25 + h28 + (-1) * h29 + (2) * h33 + (-2) * h34 + h36 + h42 + (-1) * h44 + (-1) * h46 + h47 + (-1) * h51 + h52
  have v8 : f {3}=0 := by
    linear_combination h5
  have v9 : f {0,3}=0 := by
    linear_combination h0 + (-1) * h3 + h5 + (-1) * h8 + h23
  have v10 : f {1,3}=0 := by
    linear_combination h0 + (-1) * h2 + h5 + (-1) * h8 + h42
  have v11 : f {0,1,3}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + (-1) * h3 + h5 + (-1) * h8 + h23 + h42
  have v12 : f {2,3}=0 := by
    linear_combination (-1) * h1 + h4 + h5 + h51
  have v13 : f {0,2,3}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + (-2) * h3 + h4 + h5 + (-1) * h8 + (-1) * h12 + h18 + h23 + h33 + (-1) * h34 + h52
  have v14 : f {1,2,3}=0 := by
    linear_combination (2) * h0 + (-2) * h2 + (-1) * h3 + h4 + h5 + (-1) * h8 + (-1) * h12 + (-1) * h16 + h18 + (-1) * h24 + h25 + h28 + (-1) * h29 + h33 + (-1) * h34 + h36 + h42 + h43 + (-1) * h44 + (-1) * h46 + h47 + h52
  have v15 : f {0,1,2,3}=0 := by
    linear_combination (4) * h0 + h1 + (-3) * h2 + (-3) * h3 + h4 + h5 + (-2) * h8 + h9 + (-2) * h12 + (-1) * h16 + (2) * h18 + h23 + (-1) * h24 + h25 + h28 + (-1) * h29 + (2) * h33 + (-2) * h34 + h36 + h42 + h43 + (-1) * h44 + (-1) * h46 + h47 + (-1) * h51 + (2) * h52
  have v16 : f {4}=0 := by
    linear_combination h6
  have v17 : f {0,4}=0 := by
    linear_combination h0 + (-1) * h3 + h6 + (-1) * h8 + h23 + (-1) * h25 + h29
  have v18 : f {1,4}=0 := by
    linear_combination h0 + (-1) * h2 + h6 + (-1) * h8 + h42 + (-1) * h44 + h47
  have v19 : f {0,1,4}=0 := by
    linear_combination (3) * h0 + h1 + (-2) * h2 + (-2) * h3 + h6 + (-2) * h8 + h9 + (-1) * h12 + (-1) * h16 + h18 + h23 + (-1) * h24 + h28 + h33 + (-1) * h34 + h42 + (-1) * h44 + h47 + (-1) * h51 + h52
  have v20 : f {2,4}=0 := by
    linear_combination h0 + (-1) * h2 + (-1) * h3 + h4 + h6 + (-1) * h8 + h10 + (-1) * h12 + (-1) * h16 + h18 + h33 + (-1) * h34 + h42 + (-1) * h44 + (-1) * h46 + h47 + h57
  have v21 : f {0,2,4}=0 := by
    linear_combination (3) * h0 + h1 + (-2) * h2 + (-3) * h3 + h4 + h6 + (-2) * h8 + h9 + (-2) * h12 + (-1) * h16 + (2) * h18 + h23 + (-1) * h24 + h28 + (2) * h33 + (-2) * h34 + h42 + (-1) * h44 + (-1) * h46 + h47 + (-1) * h51 + h52 + h57
  have v22 : f {1,2,4}=0 := by
    linear_combination (3) * h0 + h1 + (-3) * h2 + (-2) * h3 + h4 + h6 + (-2) * h8 + h9 + (-2) * h12 + (-2) * h16 + (2) * h18 + (-1) * h24 + h25 + h28 + (-1) * h29 + (2) * h33 + (-2) * h34 + h36 + (2) * h42 + (-2) * h44 + (-1) * h46 + (2) * h47 + (-1) * h51 + h52 + h57
  have v23 : f {0,1,2,4}=0 := by
    linear_combination (5) * h0 + (2) * h1 + (-4) * h2 + (-4) * h3 + h4 + h6 + (-3) * h8 + (2) * h9 + (-3) * h12 + (-2) * h16 + (3) * h18 + h23 + (-2) * h24 + h25 + (2) * h28 + (-1) * h29 + (3) * h33 + (-3) * h34 + h36 + (2) * h42 + (-2) * h44 + (-1) * h46 + (2) * h47 + (-2) * h51 + (2) * h52 + h57
  have v24 : f {3,4}=0 := by
    linear_combination h0 + (-1) * h2 + (-1) * h3 + h5 + h6 + (-1) * h8 + h23 + (-1) * h25 + h60
  have v25 : f {0,3,4}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + (-2) * h3 + h5 + h6 + (-2) * h8 + (2) * h23 + (-1) * h25 + h29 + h60
  have v26 : f {1,3,4}=0 := by
    linear_combination (2) * h0 + (-2) * h2 + (-1) * h3 + h5 + h6 + (-2) * h8 + h23 + (-1) * h25 + h42 + h47 + h60
  have v27 : f {0,1,3,4}=0 := by
    linear_combination (4) * h0 + h1 + (-3) * h2 + (-3) * h3 + h5 + h6 + (-3) * h8 + h9 + (-1) * h12 + (-1) * h16 + h18 + (2) * h23 + (-1) * h24 + (-1) * h25 + h26 + h28 + h33 + (-1) * h34 + h42 + h47 + (-1) * h51 + h52 + h60
  have v28 : f {2,3,4}=0 := by
    linear_combination (2) * h0 + (-2) * h2 + (-2) * h3 + h4 + h5 + h6 + (-2) * h8 + h10 + (-1) * h12 + (-1) * h16 + h18 + h23 + (-1) * h25 + h33 + (-1) * h34 + h42 + (-1) * h44 + (-1) * h46 + h47 + h53 + h57 + h60
  have v29 : f {0,2,3,4}=0 := by
    linear_combination (4) * h0 + h1 + (-3) * h2 + (-4) * h3 + h4 + h5 + h6 + (-3) * h8 + h9 + h10 + (-1) * h11 + (-2) * h12 + (-2) * h16 + h17 + (2) * h18 + (2) * h23 + (-1) * h24 + (-1) * h25 + h26 + h28 + (2) * h33 + (-2) * h34 + h42 + (-1) * h44 + (-1) * h46 + h47 + (-1) * h51 + h52 + h53 + h57 + h60
  have v30 : f {1,2,3,4}=0 := by
    linear_combination (4) * h0 + h1 + (-4) * h2 + (-3) * h3 + h4 + h5 + h6 + (-3) * h8 + h9 + h10 + (-1) * h11 + (-2) * h12 + (-2) * h16 + (2) * h18 + h23 + (-1) * h24 + (-1) * h25 + h26 + h28 + (-1) * h29 + (2) * h33 + (-2) * h34 + h37 + (2) * h42 + (-1) * h44 + (-1) * h46 + (2) * h47 + (-1) * h51 + h52 + h53 + h57 + h60
  have v31 : f {0,1,2,3,4}=0 := by
    linear_combination (6) * h0 + (2) * h1 + (-5) * h2 + (-5) * h3 + h4 + h5 + h6 + (-4) * h8 + (2) * h9 + h10 + (-1) * h11 + (-3) * h12 + (-3) * h16 + h17 + (3) * h18 + (2) * h23 + (-2) * h24 + (-1) * h25 + (2) * h26 + (2) * h28 + (-1) * h29 + (3) * h33 + (-3) * h34 + h37 + (2) * h42 + (-1) * h44 + (-1) * h46 + (2) * h47 + (-2) * h51 + (2) * h52 + h53 + h57 + h60
  have v32 : f {5}=0 := by
    linear_combination h7
  have v33 : f {0,5}=0 := by
    linear_combination h0 + (-1) * h3 + h7 + (-1) * h12 + h33
  have v34 : f {1,5}=0 := by
    linear_combination h0 + (-1) * h2 + h7 + (-1) * h12 + h50
  have v35 : f {0,1,5}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + (-1) * h3 + h7 + (-1) * h12 + h33 + h50
  have v36 : f {2,5}=0 := by
    linear_combination h0 + (-1) * h2 + (-1) * h3 + h4 + h7 + (-1) * h12 + h33 + (-1) * h34 + h59
  have v37 : f {0,2,5}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + (-2) * h3 + h4 + h7 + (-2) * h12 + h18 + (2) * h33 + (-1) * h34 + h59
  have v38 : f {1,2,5}=0 := by
    linear_combination (2) * h0 + (-2) * h2 + (-1) * h3 + h4 + h7 + (-2) * h12 + h33 + (-1) * h34 + h38 + h50 + h59
  have v39 : f {0,1,2,5}=0 := by
    linear_combination (4) * h0 + h1 + (-3) * h2 + (-3) * h3 + h4 + h7 + (-1) * h8 + h9 + (-3) * h12 + h18 + h23 + (-1) * h24 + (2) * h33 + (-2) * h34 + h35 + h38 + h50 + (-1) * h51 + h52 + h59
  have v40 : f {3,5}=0 := by
    linear_combination (-1) * h1 + h5 + h7 + h62
  have v41 : f {0,3,5}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + (-2) * h3 + h5 + h7 + (-1) * h8 + h9 + (-1) * h12 + (-1) * h15 + h18 + (-1) * h20 + h23 + (-1) * h24 + h27 + h30 + (-1) * h31 + h33 + (-1) * h34 + h35 + (-1) * h51 + h52 + h62
  have v42 : f {1,3,5}=0 := by
    linear_combination (2) * h0 + (-2) * h2 + (-1) * h3 + h5 + h7 + (-1) * h8 + h9 + (-1) * h12 + (-1) * h15 + h23 + (-1) * h24 + (-1) * h34 + h35 + h38 + (-1) * h40 + h45 + h48 + (-1) * h49 + h50 + (-1) * h51 + h52 + h62
  have v43 : f {0,1,3,5}=0 := by
    linear_combination (4) * h0 + h1 + (-3) * h2 + (-3) * h3 + h5 + h7 + (-2) * h8 + (2) * h9 + (-2) * h12 + h13 + (-2) * h15 + h18 + (-1) * h20 + (2) * h23 + (-2) * h24 + h27 + h30 + (-1) * h31 + h33 + (-2) * h34 + (2) * h35 + h38 + (-1) * h40 + h45 + h48 + (-1) * h49 + h50 + (-2) * h51 + (2) * h52 + h62
  have v44 : f {2,3,5}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h2 + (-1) * h3 + h4 + h5 + h7 + (-1) * h12 + h33 + (-1) * h34 + h54 + h59 + h62
  have v45 : f {0,2,3,5}=0 := by
    linear_combination (3) * h0 + (-2) * h2 + (-3) * h3 + h4 + h5 + h7 + (-1) * h8 + h9 + (-2) * h12 + (-1) * h15 + h18 + h19 + (-1) * h20 + h23 + (-1) * h24 + h27 + h30 + (-1) * h31 + (2) * h33 + (-2) * h34 + h35 + (-1) * h51 + h52 + h54 + h59 + h62
  have v46 : f {1,2,3,5}=0 := by
    linear_combination (3) * h0 + (-3) * h2 + (-2) * h3 + h4 + h5 + h7 + (-1) * h8 + h9 + (-2) * h12 + (-1) * h15 + h23 + (-1) * h24 + h33 + (-2) * h34 + h35 + h38 + h39 + (-1) * h40 + h45 + h48 + (-1) * h49 + h50 + (-1) * h51 + h52 + h54 + h59 + h62
  have v47 : f {0,1,2,3,5}=0 := by
    linear_combination (6) * h0 + (2) * h1 + (-5) * h2 + (-5) * h3 + h4 + h5 + h7 + (-3) * h8 + (3) * h9 + (-4) * h12 + h13 + (-2) * h15 + (2) * h18 + (-1) * h20 + (3) * h23 + (-3) * h24 + h27 + h30 + (-1) * h31 + (2) * h33 + (-4) * h34 + (3) * h35 + (2) * h38 + (-1) * h40 + h45 + h48 + (-1) * h49 + h50 + (-3) * h51 + (3) * h52 + h55 + h59 + h62
  have v48 : f {4,5}=0 := by
    linear_combination (-1) * h1 + h6 + h7 + h63
  have v49 : f {0,4,5}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + (-2) * h3 + h6 + h7 + (-1) * h8 + h9 + (-1) * h12 + (-1) * h15 + h18 + (-1) * h20 + h23 + (-1) * h24 + h30 + h33 + (-1) * h34 + h35 + (-1) * h51 + h52 + h63
  have v50 : f {1,4,5}=0 := by
    linear_combination (2) * h0 + (-2) * h2 + (-1) * h3 + h6 + h7 + (-1) * h8 + h9 + (-1) * h12 + (-1) * h15 + h23 + (-1) * h24 + (-1) * h34 + h35 + h38 + (-1) * h40 + h48 + h50 + (-1) * h51 + h52 + h63
  have v51 : f {0,1,4,5}=0 := by
    linear_combination (4) * h0 + h1 + (-3) * h2 + (-3) * h3 + h6 + h7 + (-2) * h8 + (2) * h9 + (-2) * h12 + h14 + (-2) * h15 + h18 + (-1) * h20 + (2) * h23 + (-2) * h24 + h30 + h33 + (-2) * h34 + (2) * h35 + h38 + (-1) * h40 + h48 + h50 + (-2) * h51 + (2) * h52 + h63
  have v52 : f {2,4,5}=0 := by
    linear_combination (2) * h0 + (-2) * h2 + (-2) * h3 + h4 + h6 + h7 + (-1) * h8 + h9 + (-2) * h12 + h14 + (-1) * h15 + h18 + (-1) * h20 + h23 + (-1) * h24 + h33 + (-2) * h34 + h35 + h38 + (-1) * h40 + (-1) * h51 + h52 + h58 + h59 + h63
  have v53 : f {0,2,4,5}=0 := by
    linear_combination (4) * h0 + h1 + (-3) * h2 + (-4) * h3 + h4 + h6 + h7 + (-2) * h8 + (2) * h9 + (-3) * h12 + h14 + (-2) * h15 + (2) * h18 + (-1) * h20 + (2) * h23 + (-2) * h24 + h30 + (2) * h33 + (-3) * h34 + (2) * h35 + h38 + (-1) * h40 + (-2) * h51 + (2) * h52 + h58 + h59 + h63
  have v54 : f {1,2,4,5}=0 := by
    linear_combination (4) * h0 + h1 + (-4) * h2 + (-3) * h3 + h4 + h6 + h7 + (-2) * h8 + (2) * h9 + (-3) * h12 + h14 + (-2) * h15 + h18 + (-1) * h20 + (2) * h23 + (-2) * h24 + h33 + (-3) * h34 + (2) * h35 + (2) * h38 + (-1) * h40 + h48 + h50 + (-2) * h51 + (2) * h52 + h58 + h59 + h63
  have v55 : f {0,1,2,4,5}=0 := by
    linear_combination (6) * h0 + (2) * h1 + (-5) * h2 + (-5) * h3 + h4 + h6 + h7 + (-3) * h8 + (3) * h9 + (-4) * h12 + h14 + (-2) * h15 + (2) * h18 + (-1) * h20 + (3) * h23 + (-3) * h24 + h30 + (2) * h33 + (-4) * h34 + (3) * h35 + (2) * h38 + (-1) * h40 + h48 + h50 + (-3) * h51 + (3) * h52 + h58 + h59 + h63
  have v56 : f {3,4,5}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h2 + (-1) * h3 + h5 + h6 + h7 + (-1) * h8 + h9 + (-1) * h15 + h18 + (-1) * h20 + h23 + (-1) * h24 + h30 + (-1) * h31 + (-1) * h34 + h35 + (-1) * h51 + h52 + h61 + h62 + h63
  have v57 : f {0,3,4,5}=0 := by
    linear_combination (3) * h0 + (-2) * h2 + (-3) * h3 + h5 + h6 + h7 + (-2) * h8 + (2) * h9 + (-1) * h12 + (-2) * h15 + (2) * h18 + (-2) * h20 + (2) * h23 + (-2) * h24 + h27 + (2) * h30 + (-1) * h31 + h33 + (-2) * h34 + (2) * h35 + (-2) * h51 + (2) * h52 + h61 + h62 + h63
  have v58 : f {1,3,4,5}=0 := by
    linear_combination (3) * h0 + (-3) * h2 + (-2) * h3 + h5 + h6 + h7 + (-2) * h8 + (2) * h9 + (-1) * h12 + (-2) * h15 + h18 + (-1) * h20 + (2) * h23 + (-2) * h24 + h30 + (-1) * h31 + (-2) * h34 + (2) * h35 + h38 + (-1) * h40 + h45 + h48 + h50 + (-2) * h51 + (2) * h52 + h61 + h62 + h63
  have v59 : f {0,1,3,4,5}=0 := by
    linear_combination (6) * h0 + (2) * h1 + (-5) * h2 + (-5) * h3 + h5 + h6 + h7 + (-4) * h8 + (4) * h9 + (-3) * h12 + h13 + (-3) * h15 + (3) * h18 + (-2) * h20 + (-1) * h22 + (4) * h23 + (-4) * h24 + h27 + (2) * h30 + (-2) * h31 + h32 + h33 + (-4) * h34 + (4) * h35 + (2) * h38 + (-1) * h39 + (-1) * h40 + h45 + h48 + h50 + (-4) * h51 + (4) * h52 + (-1) * h54 + h55 + h61 + h62 + h63
  have v60 : f {2,3,4,5}=0 := by
    linear_combination (3) * h0 + (-3) * h2 + (-3) * h3 + h4 + h5 + h6 + h7 + (-2) * h8 + (2) * h9 + (-2) * h12 + h14 + (-2) * h15 + (2) * h18 + (-2) * h20 + (2) * h23 + (-2) * h24 + h30 + (-1) * h31 + h33 + (-3) * h34 + (2) * h35 + h38 + (-1) * h40 + (-2) * h51 + (2) * h52 + h56 + h58 + h59 + h61 + h62 + h63
  have v61 : f {0,2,3,4,5}=0 := by
    linear_combination (5) * h0 + h1 + (-4) * h2 + (-5) * h3 + h4 + h5 + h6 + h7 + (-3) * h8 + (3) * h9 + (-3) * h12 + h14 + (-3) * h15 + (3) * h18 + (-3) * h20 + h21 + (3) * h23 + (-3) * h24 + h27 + (2) * h30 + (-1) * h31 + (2) * h33 + (-4) * h34 + (3) * h35 + h38 + (-1) * h40 + (-3) * h51 + (3) * h52 + h56 + h58 + h59 + h61 + h62 + h63
  have v62 : f {1,2,3,4,5}=0 := by
    linear_combination (5) * h0 + h1 + (-5) * h2 + (-4) * h3 + h4 + h5 + h6 + h7 + (-3) * h8 + (3) * h9 + (-3) * h12 + h14 + (-3) * h15 + (2) * h18 + (-2) * h20 + (3) * h23 + (-3) * h24 + h30 + (-1) * h31 + h33 + (-4) * h34 + (3) * h35 + (2) * h38 + (-2) * h40 + h41 + h45 + h48 + h50 + (-3) * h51 + (3) * h52 + h56 + h58 + h59 + h61 + h62 + h63
  have v63 : f {0,1,2,3,4,5}=0 := by
    linear_combination (8) * h0 + (3) * h1 + (-7) * h2 + (-7) * h3 + h4 + h5 + h6 + h7 + (-5) * h8 + (5) * h9 + (-5) * h12 + h13 + h14 + (-4) * h15 + (4) * h18 + (-3) * h20 + (5) * h23 + (-5) * h24 + h27 + (2) * h30 + (-2) * h31 + h32 + (2) * h33 + (-6) * h34 + (5) * h35 + (3) * h38 + (-1) * h39 + (-2) * h40 + h41 + h45 + h48 + h50 + (-5) * h51 + (5) * h52 + (-1) * h54 + h55 + h56 + h58 + h59 + h61 + h62 + h63
  funext S
  change f S=0
  have casesS : ∀ S : Finset (Fin 6), S=∅ ∨ S={0} ∨ S={1} ∨ S={0,1} ∨ S={2} ∨ S={0,2} ∨ S={1,2} ∨ S={0,1,2} ∨ S={3} ∨ S={0,3} ∨ S={1,3} ∨ S={0,1,3} ∨ S={2,3} ∨ S={0,2,3} ∨ S={1,2,3} ∨ S={0,1,2,3} ∨ S={4} ∨ S={0,4} ∨ S={1,4} ∨ S={0,1,4} ∨ S={2,4} ∨ S={0,2,4} ∨ S={1,2,4} ∨ S={0,1,2,4} ∨ S={3,4} ∨ S={0,3,4} ∨ S={1,3,4} ∨ S={0,1,3,4} ∨ S={2,3,4} ∨ S={0,2,3,4} ∨ S={1,2,3,4} ∨ S={0,1,2,3,4} ∨ S={5} ∨ S={0,5} ∨ S={1,5} ∨ S={0,1,5} ∨ S={2,5} ∨ S={0,2,5} ∨ S={1,2,5} ∨ S={0,1,2,5} ∨ S={3,5} ∨ S={0,3,5} ∨ S={1,3,5} ∨ S={0,1,3,5} ∨ S={2,3,5} ∨ S={0,2,3,5} ∨ S={1,2,3,5} ∨ S={0,1,2,3,5} ∨ S={4,5} ∨ S={0,4,5} ∨ S={1,4,5} ∨ S={0,1,4,5} ∨ S={2,4,5} ∨ S={0,2,4,5} ∨ S={1,2,4,5} ∨ S={0,1,2,4,5} ∨ S={3,4,5} ∨ S={0,3,4,5} ∨ S={1,3,4,5} ∨ S={0,1,3,4,5} ∨ S={2,3,4,5} ∨ S={0,2,3,4,5} ∨ S={1,2,3,4,5} ∨ S={0,1,2,3,4,5} := by decide
  rcases casesS S with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem empty_zero : integerFunction ∅=0 := by decide

theorem singleton_zero : ∀ v : Fin 6,integerFunction {v}=0 := by decide

theorem boolean_differences : ∀ u v : Fin 6,u≠v → ∀ S : Finset (Fin 6),
    u∉S → v∉S → integerDelta integerFunction u v S=0 ∨
      integerDelta integerFunction u v S=1 := by decide

theorem extreme : ExtremeSupermodular (realFunction integerFunction) :=
  extreme_of_row_kernel integerFunction rows pivot pivot_one row_zero valid_rows
    row_kernel_zero empty_zero singleton_zero boolean_differences

end K1122

namespace K1122Complement

def integerFunction (S : Finset (Fin 6)) : ℤ :=
  (match subsetMask S with
  | 11 => 1
  | 15 => 1
  | 23 => 1
  | 25 => 1
  | 26 => 1
  | 27 => 2
  | 29 => 1
  | 30 => 1
  | 31 => 3
  | 35 => 1
  | 37 => 1
  | 38 => 1
  | 39 => 2
  | 40 => 1
  | 41 => 1
  | 42 => 1
  | 43 => 2
  | 44 => 1
  | 45 => 2
  | 46 => 2
  | 47 => 3
  | 51 => 1
  | 53 => 1
  | 54 => 1
  | 55 => 3
  | 56 => 1
  | 57 => 2
  | 58 => 2
  | 59 => 3
  | 60 => 1
  | 61 => 3
  | 62 => 3
  | 63 => 5
  | _ => 0)

def rows : Fin 64 → Row (Fin 6) :=
  ![.value {0,1,3},.value ∅,.value {0},.value {1},.value {2},.value {3},.value {4},.value {5},.elemental 0 1 ∅,.elemental 0 1 {2},.elemental 0 1 {4},.elemental 0 1 {3,4},.elemental 0 1 {2,5},.elemental 0 1 {2,3,5},.elemental 0 1 {3,4,5},.elemental 0 1 {2,3,4,5},.elemental 0 2 ∅,.elemental 0 2 {3},.elemental 0 2 {1,3},.elemental 0 2 {4},.elemental 0 2 {3,4},.elemental 0 2 {1,5},.elemental 0 2 {1,3,5},.elemental 0 3 ∅,.elemental 0 3 {5},.elemental 0 3 {1,5},.elemental 0 3 {1,4,5},.elemental 0 3 {1,2,4,5},.elemental 0 4 ∅,.elemental 0 4 {1,3},.elemental 0 4 {5},.elemental 0 4 {1,5},.elemental 0 4 {2,5},.elemental 0 5 ∅,.elemental 0 5 {1,3},.elemental 0 5 {1,2,3,4},.elemental 1 2 ∅,.elemental 1 2 {3},.elemental 1 2 {4},.elemental 1 2 {3,4},.elemental 1 2 {0,5},.elemental 1 2 {0,3,5},.elemental 1 3 ∅,.elemental 1 3 {5},.elemental 1 3 {0,4,5},.elemental 1 3 {0,2,4,5},.elemental 1 4 ∅,.elemental 1 4 {0,3},.elemental 1 4 {5},.elemental 1 4 {2,5},.elemental 1 5 ∅,.elemental 2 3 ∅,.elemental 2 3 {4},.elemental 2 3 {0,1,4},.elemental 2 3 {5},.elemental 2 3 {4,5},.elemental 2 3 {0,4,5},.elemental 2 4 ∅,.elemental 2 4 {5},.elemental 2 5 ∅,.elemental 3 4 ∅,.elemental 3 4 {5},.elemental 3 5 {0,1},.elemental 4 5 ∅]

def pivot : Finset (Fin 6) := {0,1,3}

theorem pivot_one : integerFunction pivot=1 := by decide

theorem row_zero : rows 0=.value pivot := by decide

theorem valid_rows : ∀ i : Fin 64,i≠0 → (rows i).valid integerFunction := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 4096 in
theorem row_kernel_zero (f : SetFunction (Fin 6))
    (hf : ∀ i : Fin 64,(rows i).eval f=0) : f=0 := by
  have h0 : f {0,1,3}=0 := hf 0
  have h1 : f ∅=0 := hf 1
  have h2 : f {0}=0 := hf 2
  have h3 : f {1}=0 := hf 3
  have h4 : f {2}=0 := hf 4
  have h5 : f {3}=0 := hf 5
  have h6 : f {4}=0 := hf 6
  have h7 : f {5}=0 := hf 7
  have h8 : f {0,1}-f {0}-f {1}+f ∅=0 := by
    have h := hf 8
    change f (insert 0 (insert 1 (∅ : Finset (Fin 6))))-
      f (insert 0 (∅ : Finset (Fin 6)))-f (insert 1 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 0 (insert 1 (∅ : Finset (Fin 6)))={0,1} := by decide
    have hA : insert 0 (∅ : Finset (Fin 6))={0} := by decide
    have hB : insert 1 (∅ : Finset (Fin 6))={1} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h9 : f {0,1,2}-f {0,2}-f {1,2}+f {2}=0 := by
    have h := hf 9
    change f (insert 0 (insert 1 ({2} : Finset (Fin 6))))-
      f (insert 0 ({2} : Finset (Fin 6)))-f (insert 1 ({2} : Finset (Fin 6)))+f {2}=0 at h
    have hAB : insert 0 (insert 1 ({2} : Finset (Fin 6)))={0,1,2} := by decide
    have hA : insert 0 ({2} : Finset (Fin 6))={0,2} := by decide
    have hB : insert 1 ({2} : Finset (Fin 6))={1,2} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h10 : f {0,1,4}-f {0,4}-f {1,4}+f {4}=0 := by
    have h := hf 10
    change f (insert 0 (insert 1 ({4} : Finset (Fin 6))))-
      f (insert 0 ({4} : Finset (Fin 6)))-f (insert 1 ({4} : Finset (Fin 6)))+f {4}=0 at h
    have hAB : insert 0 (insert 1 ({4} : Finset (Fin 6)))={0,1,4} := by decide
    have hA : insert 0 ({4} : Finset (Fin 6))={0,4} := by decide
    have hB : insert 1 ({4} : Finset (Fin 6))={1,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h11 : f {0,1,3,4}-f {0,3,4}-f {1,3,4}+f {3,4}=0 := by
    have h := hf 11
    change f (insert 0 (insert 1 ({3,4} : Finset (Fin 6))))-
      f (insert 0 ({3,4} : Finset (Fin 6)))-f (insert 1 ({3,4} : Finset (Fin 6)))+f {3,4}=0 at h
    have hAB : insert 0 (insert 1 ({3,4} : Finset (Fin 6)))={0,1,3,4} := by decide
    have hA : insert 0 ({3,4} : Finset (Fin 6))={0,3,4} := by decide
    have hB : insert 1 ({3,4} : Finset (Fin 6))={1,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h12 : f {0,1,2,5}-f {0,2,5}-f {1,2,5}+f {2,5}=0 := by
    have h := hf 12
    change f (insert 0 (insert 1 ({2,5} : Finset (Fin 6))))-
      f (insert 0 ({2,5} : Finset (Fin 6)))-f (insert 1 ({2,5} : Finset (Fin 6)))+f {2,5}=0 at h
    have hAB : insert 0 (insert 1 ({2,5} : Finset (Fin 6)))={0,1,2,5} := by decide
    have hA : insert 0 ({2,5} : Finset (Fin 6))={0,2,5} := by decide
    have hB : insert 1 ({2,5} : Finset (Fin 6))={1,2,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h13 : f {0,1,2,3,5}-f {0,2,3,5}-f {1,2,3,5}+f {2,3,5}=0 := by
    have h := hf 13
    change f (insert 0 (insert 1 ({2,3,5} : Finset (Fin 6))))-
      f (insert 0 ({2,3,5} : Finset (Fin 6)))-f (insert 1 ({2,3,5} : Finset (Fin 6)))+f {2,3,5}=0 at h
    have hAB : insert 0 (insert 1 ({2,3,5} : Finset (Fin 6)))={0,1,2,3,5} := by decide
    have hA : insert 0 ({2,3,5} : Finset (Fin 6))={0,2,3,5} := by decide
    have hB : insert 1 ({2,3,5} : Finset (Fin 6))={1,2,3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h14 : f {0,1,3,4,5}-f {0,3,4,5}-f {1,3,4,5}+f {3,4,5}=0 := by
    have h := hf 14
    change f (insert 0 (insert 1 ({3,4,5} : Finset (Fin 6))))-
      f (insert 0 ({3,4,5} : Finset (Fin 6)))-f (insert 1 ({3,4,5} : Finset (Fin 6)))+f {3,4,5}=0 at h
    have hAB : insert 0 (insert 1 ({3,4,5} : Finset (Fin 6)))={0,1,3,4,5} := by decide
    have hA : insert 0 ({3,4,5} : Finset (Fin 6))={0,3,4,5} := by decide
    have hB : insert 1 ({3,4,5} : Finset (Fin 6))={1,3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h15 : f {0,1,2,3,4,5}-f {0,2,3,4,5}-f {1,2,3,4,5}+f {2,3,4,5}=0 := by
    have h := hf 15
    change f (insert 0 (insert 1 ({2,3,4,5} : Finset (Fin 6))))-
      f (insert 0 ({2,3,4,5} : Finset (Fin 6)))-f (insert 1 ({2,3,4,5} : Finset (Fin 6)))+f {2,3,4,5}=0 at h
    have hAB : insert 0 (insert 1 ({2,3,4,5} : Finset (Fin 6)))={0,1,2,3,4,5} := by decide
    have hA : insert 0 ({2,3,4,5} : Finset (Fin 6))={0,2,3,4,5} := by decide
    have hB : insert 1 ({2,3,4,5} : Finset (Fin 6))={1,2,3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h16 : f {0,2}-f {0}-f {2}+f ∅=0 := by
    have h := hf 16
    change f (insert 0 (insert 2 (∅ : Finset (Fin 6))))-
      f (insert 0 (∅ : Finset (Fin 6)))-f (insert 2 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 0 (insert 2 (∅ : Finset (Fin 6)))={0,2} := by decide
    have hA : insert 0 (∅ : Finset (Fin 6))={0} := by decide
    have hB : insert 2 (∅ : Finset (Fin 6))={2} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h17 : f {0,2,3}-f {0,3}-f {2,3}+f {3}=0 := by
    have h := hf 17
    change f (insert 0 (insert 2 ({3} : Finset (Fin 6))))-
      f (insert 0 ({3} : Finset (Fin 6)))-f (insert 2 ({3} : Finset (Fin 6)))+f {3}=0 at h
    have hAB : insert 0 (insert 2 ({3} : Finset (Fin 6)))={0,2,3} := by decide
    have hA : insert 0 ({3} : Finset (Fin 6))={0,3} := by decide
    have hB : insert 2 ({3} : Finset (Fin 6))={2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h18 : f {0,1,2,3}-f {0,1,3}-f {1,2,3}+f {1,3}=0 := by
    have h := hf 18
    change f (insert 0 (insert 2 ({1,3} : Finset (Fin 6))))-
      f (insert 0 ({1,3} : Finset (Fin 6)))-f (insert 2 ({1,3} : Finset (Fin 6)))+f {1,3}=0 at h
    have hAB : insert 0 (insert 2 ({1,3} : Finset (Fin 6)))={0,1,2,3} := by decide
    have hA : insert 0 ({1,3} : Finset (Fin 6))={0,1,3} := by decide
    have hB : insert 2 ({1,3} : Finset (Fin 6))={1,2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h19 : f {0,2,4}-f {0,4}-f {2,4}+f {4}=0 := by
    have h := hf 19
    change f (insert 0 (insert 2 ({4} : Finset (Fin 6))))-
      f (insert 0 ({4} : Finset (Fin 6)))-f (insert 2 ({4} : Finset (Fin 6)))+f {4}=0 at h
    have hAB : insert 0 (insert 2 ({4} : Finset (Fin 6)))={0,2,4} := by decide
    have hA : insert 0 ({4} : Finset (Fin 6))={0,4} := by decide
    have hB : insert 2 ({4} : Finset (Fin 6))={2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h20 : f {0,2,3,4}-f {0,3,4}-f {2,3,4}+f {3,4}=0 := by
    have h := hf 20
    change f (insert 0 (insert 2 ({3,4} : Finset (Fin 6))))-
      f (insert 0 ({3,4} : Finset (Fin 6)))-f (insert 2 ({3,4} : Finset (Fin 6)))+f {3,4}=0 at h
    have hAB : insert 0 (insert 2 ({3,4} : Finset (Fin 6)))={0,2,3,4} := by decide
    have hA : insert 0 ({3,4} : Finset (Fin 6))={0,3,4} := by decide
    have hB : insert 2 ({3,4} : Finset (Fin 6))={2,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h21 : f {0,1,2,5}-f {0,1,5}-f {1,2,5}+f {1,5}=0 := by
    have h := hf 21
    change f (insert 0 (insert 2 ({1,5} : Finset (Fin 6))))-
      f (insert 0 ({1,5} : Finset (Fin 6)))-f (insert 2 ({1,5} : Finset (Fin 6)))+f {1,5}=0 at h
    have hAB : insert 0 (insert 2 ({1,5} : Finset (Fin 6)))={0,1,2,5} := by decide
    have hA : insert 0 ({1,5} : Finset (Fin 6))={0,1,5} := by decide
    have hB : insert 2 ({1,5} : Finset (Fin 6))={1,2,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h22 : f {0,1,2,3,5}-f {0,1,3,5}-f {1,2,3,5}+f {1,3,5}=0 := by
    have h := hf 22
    change f (insert 0 (insert 2 ({1,3,5} : Finset (Fin 6))))-
      f (insert 0 ({1,3,5} : Finset (Fin 6)))-f (insert 2 ({1,3,5} : Finset (Fin 6)))+f {1,3,5}=0 at h
    have hAB : insert 0 (insert 2 ({1,3,5} : Finset (Fin 6)))={0,1,2,3,5} := by decide
    have hA : insert 0 ({1,3,5} : Finset (Fin 6))={0,1,3,5} := by decide
    have hB : insert 2 ({1,3,5} : Finset (Fin 6))={1,2,3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h23 : f {0,3}-f {0}-f {3}+f ∅=0 := by
    have h := hf 23
    change f (insert 0 (insert 3 (∅ : Finset (Fin 6))))-
      f (insert 0 (∅ : Finset (Fin 6)))-f (insert 3 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 0 (insert 3 (∅ : Finset (Fin 6)))={0,3} := by decide
    have hA : insert 0 (∅ : Finset (Fin 6))={0} := by decide
    have hB : insert 3 (∅ : Finset (Fin 6))={3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h24 : f {0,3,5}-f {0,5}-f {3,5}+f {5}=0 := by
    have h := hf 24
    change f (insert 0 (insert 3 ({5} : Finset (Fin 6))))-
      f (insert 0 ({5} : Finset (Fin 6)))-f (insert 3 ({5} : Finset (Fin 6)))+f {5}=0 at h
    have hAB : insert 0 (insert 3 ({5} : Finset (Fin 6)))={0,3,5} := by decide
    have hA : insert 0 ({5} : Finset (Fin 6))={0,5} := by decide
    have hB : insert 3 ({5} : Finset (Fin 6))={3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h25 : f {0,1,3,5}-f {0,1,5}-f {1,3,5}+f {1,5}=0 := by
    have h := hf 25
    change f (insert 0 (insert 3 ({1,5} : Finset (Fin 6))))-
      f (insert 0 ({1,5} : Finset (Fin 6)))-f (insert 3 ({1,5} : Finset (Fin 6)))+f {1,5}=0 at h
    have hAB : insert 0 (insert 3 ({1,5} : Finset (Fin 6)))={0,1,3,5} := by decide
    have hA : insert 0 ({1,5} : Finset (Fin 6))={0,1,5} := by decide
    have hB : insert 3 ({1,5} : Finset (Fin 6))={1,3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h26 : f {0,1,3,4,5}-f {0,1,4,5}-f {1,3,4,5}+f {1,4,5}=0 := by
    have h := hf 26
    change f (insert 0 (insert 3 ({1,4,5} : Finset (Fin 6))))-
      f (insert 0 ({1,4,5} : Finset (Fin 6)))-f (insert 3 ({1,4,5} : Finset (Fin 6)))+f {1,4,5}=0 at h
    have hAB : insert 0 (insert 3 ({1,4,5} : Finset (Fin 6)))={0,1,3,4,5} := by decide
    have hA : insert 0 ({1,4,5} : Finset (Fin 6))={0,1,4,5} := by decide
    have hB : insert 3 ({1,4,5} : Finset (Fin 6))={1,3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h27 : f {0,1,2,3,4,5}-f {0,1,2,4,5}-f {1,2,3,4,5}+f {1,2,4,5}=0 := by
    have h := hf 27
    change f (insert 0 (insert 3 ({1,2,4,5} : Finset (Fin 6))))-
      f (insert 0 ({1,2,4,5} : Finset (Fin 6)))-f (insert 3 ({1,2,4,5} : Finset (Fin 6)))+f {1,2,4,5}=0 at h
    have hAB : insert 0 (insert 3 ({1,2,4,5} : Finset (Fin 6)))={0,1,2,3,4,5} := by decide
    have hA : insert 0 ({1,2,4,5} : Finset (Fin 6))={0,1,2,4,5} := by decide
    have hB : insert 3 ({1,2,4,5} : Finset (Fin 6))={1,2,3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h28 : f {0,4}-f {0}-f {4}+f ∅=0 := by
    have h := hf 28
    change f (insert 0 (insert 4 (∅ : Finset (Fin 6))))-
      f (insert 0 (∅ : Finset (Fin 6)))-f (insert 4 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 0 (insert 4 (∅ : Finset (Fin 6)))={0,4} := by decide
    have hA : insert 0 (∅ : Finset (Fin 6))={0} := by decide
    have hB : insert 4 (∅ : Finset (Fin 6))={4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h29 : f {0,1,3,4}-f {0,1,3}-f {1,3,4}+f {1,3}=0 := by
    have h := hf 29
    change f (insert 0 (insert 4 ({1,3} : Finset (Fin 6))))-
      f (insert 0 ({1,3} : Finset (Fin 6)))-f (insert 4 ({1,3} : Finset (Fin 6)))+f {1,3}=0 at h
    have hAB : insert 0 (insert 4 ({1,3} : Finset (Fin 6)))={0,1,3,4} := by decide
    have hA : insert 0 ({1,3} : Finset (Fin 6))={0,1,3} := by decide
    have hB : insert 4 ({1,3} : Finset (Fin 6))={1,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h30 : f {0,4,5}-f {0,5}-f {4,5}+f {5}=0 := by
    have h := hf 30
    change f (insert 0 (insert 4 ({5} : Finset (Fin 6))))-
      f (insert 0 ({5} : Finset (Fin 6)))-f (insert 4 ({5} : Finset (Fin 6)))+f {5}=0 at h
    have hAB : insert 0 (insert 4 ({5} : Finset (Fin 6)))={0,4,5} := by decide
    have hA : insert 0 ({5} : Finset (Fin 6))={0,5} := by decide
    have hB : insert 4 ({5} : Finset (Fin 6))={4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h31 : f {0,1,4,5}-f {0,1,5}-f {1,4,5}+f {1,5}=0 := by
    have h := hf 31
    change f (insert 0 (insert 4 ({1,5} : Finset (Fin 6))))-
      f (insert 0 ({1,5} : Finset (Fin 6)))-f (insert 4 ({1,5} : Finset (Fin 6)))+f {1,5}=0 at h
    have hAB : insert 0 (insert 4 ({1,5} : Finset (Fin 6)))={0,1,4,5} := by decide
    have hA : insert 0 ({1,5} : Finset (Fin 6))={0,1,5} := by decide
    have hB : insert 4 ({1,5} : Finset (Fin 6))={1,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h32 : f {0,2,4,5}-f {0,2,5}-f {2,4,5}+f {2,5}=0 := by
    have h := hf 32
    change f (insert 0 (insert 4 ({2,5} : Finset (Fin 6))))-
      f (insert 0 ({2,5} : Finset (Fin 6)))-f (insert 4 ({2,5} : Finset (Fin 6)))+f {2,5}=0 at h
    have hAB : insert 0 (insert 4 ({2,5} : Finset (Fin 6)))={0,2,4,5} := by decide
    have hA : insert 0 ({2,5} : Finset (Fin 6))={0,2,5} := by decide
    have hB : insert 4 ({2,5} : Finset (Fin 6))={2,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h33 : f {0,5}-f {0}-f {5}+f ∅=0 := by
    have h := hf 33
    change f (insert 0 (insert 5 (∅ : Finset (Fin 6))))-
      f (insert 0 (∅ : Finset (Fin 6)))-f (insert 5 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 0 (insert 5 (∅ : Finset (Fin 6)))={0,5} := by decide
    have hA : insert 0 (∅ : Finset (Fin 6))={0} := by decide
    have hB : insert 5 (∅ : Finset (Fin 6))={5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h34 : f {0,1,3,5}-f {0,1,3}-f {1,3,5}+f {1,3}=0 := by
    have h := hf 34
    change f (insert 0 (insert 5 ({1,3} : Finset (Fin 6))))-
      f (insert 0 ({1,3} : Finset (Fin 6)))-f (insert 5 ({1,3} : Finset (Fin 6)))+f {1,3}=0 at h
    have hAB : insert 0 (insert 5 ({1,3} : Finset (Fin 6)))={0,1,3,5} := by decide
    have hA : insert 0 ({1,3} : Finset (Fin 6))={0,1,3} := by decide
    have hB : insert 5 ({1,3} : Finset (Fin 6))={1,3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h35 : f {0,1,2,3,4,5}-f {0,1,2,3,4}-f {1,2,3,4,5}+f {1,2,3,4}=0 := by
    have h := hf 35
    change f (insert 0 (insert 5 ({1,2,3,4} : Finset (Fin 6))))-
      f (insert 0 ({1,2,3,4} : Finset (Fin 6)))-f (insert 5 ({1,2,3,4} : Finset (Fin 6)))+f {1,2,3,4}=0 at h
    have hAB : insert 0 (insert 5 ({1,2,3,4} : Finset (Fin 6)))={0,1,2,3,4,5} := by decide
    have hA : insert 0 ({1,2,3,4} : Finset (Fin 6))={0,1,2,3,4} := by decide
    have hB : insert 5 ({1,2,3,4} : Finset (Fin 6))={1,2,3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h36 : f {1,2}-f {1}-f {2}+f ∅=0 := by
    have h := hf 36
    change f (insert 1 (insert 2 (∅ : Finset (Fin 6))))-
      f (insert 1 (∅ : Finset (Fin 6)))-f (insert 2 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 1 (insert 2 (∅ : Finset (Fin 6)))={1,2} := by decide
    have hA : insert 1 (∅ : Finset (Fin 6))={1} := by decide
    have hB : insert 2 (∅ : Finset (Fin 6))={2} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h37 : f {1,2,3}-f {1,3}-f {2,3}+f {3}=0 := by
    have h := hf 37
    change f (insert 1 (insert 2 ({3} : Finset (Fin 6))))-
      f (insert 1 ({3} : Finset (Fin 6)))-f (insert 2 ({3} : Finset (Fin 6)))+f {3}=0 at h
    have hAB : insert 1 (insert 2 ({3} : Finset (Fin 6)))={1,2,3} := by decide
    have hA : insert 1 ({3} : Finset (Fin 6))={1,3} := by decide
    have hB : insert 2 ({3} : Finset (Fin 6))={2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h38 : f {1,2,4}-f {1,4}-f {2,4}+f {4}=0 := by
    have h := hf 38
    change f (insert 1 (insert 2 ({4} : Finset (Fin 6))))-
      f (insert 1 ({4} : Finset (Fin 6)))-f (insert 2 ({4} : Finset (Fin 6)))+f {4}=0 at h
    have hAB : insert 1 (insert 2 ({4} : Finset (Fin 6)))={1,2,4} := by decide
    have hA : insert 1 ({4} : Finset (Fin 6))={1,4} := by decide
    have hB : insert 2 ({4} : Finset (Fin 6))={2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h39 : f {1,2,3,4}-f {1,3,4}-f {2,3,4}+f {3,4}=0 := by
    have h := hf 39
    change f (insert 1 (insert 2 ({3,4} : Finset (Fin 6))))-
      f (insert 1 ({3,4} : Finset (Fin 6)))-f (insert 2 ({3,4} : Finset (Fin 6)))+f {3,4}=0 at h
    have hAB : insert 1 (insert 2 ({3,4} : Finset (Fin 6)))={1,2,3,4} := by decide
    have hA : insert 1 ({3,4} : Finset (Fin 6))={1,3,4} := by decide
    have hB : insert 2 ({3,4} : Finset (Fin 6))={2,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h40 : f {0,1,2,5}-f {0,1,5}-f {0,2,5}+f {0,5}=0 := by
    have h := hf 40
    change f (insert 1 (insert 2 ({0,5} : Finset (Fin 6))))-
      f (insert 1 ({0,5} : Finset (Fin 6)))-f (insert 2 ({0,5} : Finset (Fin 6)))+f {0,5}=0 at h
    have hAB : insert 1 (insert 2 ({0,5} : Finset (Fin 6)))={0,1,2,5} := by decide
    have hA : insert 1 ({0,5} : Finset (Fin 6))={0,1,5} := by decide
    have hB : insert 2 ({0,5} : Finset (Fin 6))={0,2,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h41 : f {0,1,2,3,5}-f {0,1,3,5}-f {0,2,3,5}+f {0,3,5}=0 := by
    have h := hf 41
    change f (insert 1 (insert 2 ({0,3,5} : Finset (Fin 6))))-
      f (insert 1 ({0,3,5} : Finset (Fin 6)))-f (insert 2 ({0,3,5} : Finset (Fin 6)))+f {0,3,5}=0 at h
    have hAB : insert 1 (insert 2 ({0,3,5} : Finset (Fin 6)))={0,1,2,3,5} := by decide
    have hA : insert 1 ({0,3,5} : Finset (Fin 6))={0,1,3,5} := by decide
    have hB : insert 2 ({0,3,5} : Finset (Fin 6))={0,2,3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h42 : f {1,3}-f {1}-f {3}+f ∅=0 := by
    have h := hf 42
    change f (insert 1 (insert 3 (∅ : Finset (Fin 6))))-
      f (insert 1 (∅ : Finset (Fin 6)))-f (insert 3 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 1 (insert 3 (∅ : Finset (Fin 6)))={1,3} := by decide
    have hA : insert 1 (∅ : Finset (Fin 6))={1} := by decide
    have hB : insert 3 (∅ : Finset (Fin 6))={3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h43 : f {1,3,5}-f {1,5}-f {3,5}+f {5}=0 := by
    have h := hf 43
    change f (insert 1 (insert 3 ({5} : Finset (Fin 6))))-
      f (insert 1 ({5} : Finset (Fin 6)))-f (insert 3 ({5} : Finset (Fin 6)))+f {5}=0 at h
    have hAB : insert 1 (insert 3 ({5} : Finset (Fin 6)))={1,3,5} := by decide
    have hA : insert 1 ({5} : Finset (Fin 6))={1,5} := by decide
    have hB : insert 3 ({5} : Finset (Fin 6))={3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h44 : f {0,1,3,4,5}-f {0,1,4,5}-f {0,3,4,5}+f {0,4,5}=0 := by
    have h := hf 44
    change f (insert 1 (insert 3 ({0,4,5} : Finset (Fin 6))))-
      f (insert 1 ({0,4,5} : Finset (Fin 6)))-f (insert 3 ({0,4,5} : Finset (Fin 6)))+f {0,4,5}=0 at h
    have hAB : insert 1 (insert 3 ({0,4,5} : Finset (Fin 6)))={0,1,3,4,5} := by decide
    have hA : insert 1 ({0,4,5} : Finset (Fin 6))={0,1,4,5} := by decide
    have hB : insert 3 ({0,4,5} : Finset (Fin 6))={0,3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h45 : f {0,1,2,3,4,5}-f {0,1,2,4,5}-f {0,2,3,4,5}+f {0,2,4,5}=0 := by
    have h := hf 45
    change f (insert 1 (insert 3 ({0,2,4,5} : Finset (Fin 6))))-
      f (insert 1 ({0,2,4,5} : Finset (Fin 6)))-f (insert 3 ({0,2,4,5} : Finset (Fin 6)))+f {0,2,4,5}=0 at h
    have hAB : insert 1 (insert 3 ({0,2,4,5} : Finset (Fin 6)))={0,1,2,3,4,5} := by decide
    have hA : insert 1 ({0,2,4,5} : Finset (Fin 6))={0,1,2,4,5} := by decide
    have hB : insert 3 ({0,2,4,5} : Finset (Fin 6))={0,2,3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h46 : f {1,4}-f {1}-f {4}+f ∅=0 := by
    have h := hf 46
    change f (insert 1 (insert 4 (∅ : Finset (Fin 6))))-
      f (insert 1 (∅ : Finset (Fin 6)))-f (insert 4 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 1 (insert 4 (∅ : Finset (Fin 6)))={1,4} := by decide
    have hA : insert 1 (∅ : Finset (Fin 6))={1} := by decide
    have hB : insert 4 (∅ : Finset (Fin 6))={4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h47 : f {0,1,3,4}-f {0,1,3}-f {0,3,4}+f {0,3}=0 := by
    have h := hf 47
    change f (insert 1 (insert 4 ({0,3} : Finset (Fin 6))))-
      f (insert 1 ({0,3} : Finset (Fin 6)))-f (insert 4 ({0,3} : Finset (Fin 6)))+f {0,3}=0 at h
    have hAB : insert 1 (insert 4 ({0,3} : Finset (Fin 6)))={0,1,3,4} := by decide
    have hA : insert 1 ({0,3} : Finset (Fin 6))={0,1,3} := by decide
    have hB : insert 4 ({0,3} : Finset (Fin 6))={0,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h48 : f {1,4,5}-f {1,5}-f {4,5}+f {5}=0 := by
    have h := hf 48
    change f (insert 1 (insert 4 ({5} : Finset (Fin 6))))-
      f (insert 1 ({5} : Finset (Fin 6)))-f (insert 4 ({5} : Finset (Fin 6)))+f {5}=0 at h
    have hAB : insert 1 (insert 4 ({5} : Finset (Fin 6)))={1,4,5} := by decide
    have hA : insert 1 ({5} : Finset (Fin 6))={1,5} := by decide
    have hB : insert 4 ({5} : Finset (Fin 6))={4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h49 : f {1,2,4,5}-f {1,2,5}-f {2,4,5}+f {2,5}=0 := by
    have h := hf 49
    change f (insert 1 (insert 4 ({2,5} : Finset (Fin 6))))-
      f (insert 1 ({2,5} : Finset (Fin 6)))-f (insert 4 ({2,5} : Finset (Fin 6)))+f {2,5}=0 at h
    have hAB : insert 1 (insert 4 ({2,5} : Finset (Fin 6)))={1,2,4,5} := by decide
    have hA : insert 1 ({2,5} : Finset (Fin 6))={1,2,5} := by decide
    have hB : insert 4 ({2,5} : Finset (Fin 6))={2,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h50 : f {1,5}-f {1}-f {5}+f ∅=0 := by
    have h := hf 50
    change f (insert 1 (insert 5 (∅ : Finset (Fin 6))))-
      f (insert 1 (∅ : Finset (Fin 6)))-f (insert 5 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 1 (insert 5 (∅ : Finset (Fin 6)))={1,5} := by decide
    have hA : insert 1 (∅ : Finset (Fin 6))={1} := by decide
    have hB : insert 5 (∅ : Finset (Fin 6))={5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h51 : f {2,3}-f {2}-f {3}+f ∅=0 := by
    have h := hf 51
    change f (insert 2 (insert 3 (∅ : Finset (Fin 6))))-
      f (insert 2 (∅ : Finset (Fin 6)))-f (insert 3 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 2 (insert 3 (∅ : Finset (Fin 6)))={2,3} := by decide
    have hA : insert 2 (∅ : Finset (Fin 6))={2} := by decide
    have hB : insert 3 (∅ : Finset (Fin 6))={3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h52 : f {2,3,4}-f {2,4}-f {3,4}+f {4}=0 := by
    have h := hf 52
    change f (insert 2 (insert 3 ({4} : Finset (Fin 6))))-
      f (insert 2 ({4} : Finset (Fin 6)))-f (insert 3 ({4} : Finset (Fin 6)))+f {4}=0 at h
    have hAB : insert 2 (insert 3 ({4} : Finset (Fin 6)))={2,3,4} := by decide
    have hA : insert 2 ({4} : Finset (Fin 6))={2,4} := by decide
    have hB : insert 3 ({4} : Finset (Fin 6))={3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h53 : f {0,1,2,3,4}-f {0,1,2,4}-f {0,1,3,4}+f {0,1,4}=0 := by
    have h := hf 53
    change f (insert 2 (insert 3 ({0,1,4} : Finset (Fin 6))))-
      f (insert 2 ({0,1,4} : Finset (Fin 6)))-f (insert 3 ({0,1,4} : Finset (Fin 6)))+f {0,1,4}=0 at h
    have hAB : insert 2 (insert 3 ({0,1,4} : Finset (Fin 6)))={0,1,2,3,4} := by decide
    have hA : insert 2 ({0,1,4} : Finset (Fin 6))={0,1,2,4} := by decide
    have hB : insert 3 ({0,1,4} : Finset (Fin 6))={0,1,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h54 : f {2,3,5}-f {2,5}-f {3,5}+f {5}=0 := by
    have h := hf 54
    change f (insert 2 (insert 3 ({5} : Finset (Fin 6))))-
      f (insert 2 ({5} : Finset (Fin 6)))-f (insert 3 ({5} : Finset (Fin 6)))+f {5}=0 at h
    have hAB : insert 2 (insert 3 ({5} : Finset (Fin 6)))={2,3,5} := by decide
    have hA : insert 2 ({5} : Finset (Fin 6))={2,5} := by decide
    have hB : insert 3 ({5} : Finset (Fin 6))={3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h55 : f {2,3,4,5}-f {2,4,5}-f {3,4,5}+f {4,5}=0 := by
    have h := hf 55
    change f (insert 2 (insert 3 ({4,5} : Finset (Fin 6))))-
      f (insert 2 ({4,5} : Finset (Fin 6)))-f (insert 3 ({4,5} : Finset (Fin 6)))+f {4,5}=0 at h
    have hAB : insert 2 (insert 3 ({4,5} : Finset (Fin 6)))={2,3,4,5} := by decide
    have hA : insert 2 ({4,5} : Finset (Fin 6))={2,4,5} := by decide
    have hB : insert 3 ({4,5} : Finset (Fin 6))={3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h56 : f {0,2,3,4,5}-f {0,2,4,5}-f {0,3,4,5}+f {0,4,5}=0 := by
    have h := hf 56
    change f (insert 2 (insert 3 ({0,4,5} : Finset (Fin 6))))-
      f (insert 2 ({0,4,5} : Finset (Fin 6)))-f (insert 3 ({0,4,5} : Finset (Fin 6)))+f {0,4,5}=0 at h
    have hAB : insert 2 (insert 3 ({0,4,5} : Finset (Fin 6)))={0,2,3,4,5} := by decide
    have hA : insert 2 ({0,4,5} : Finset (Fin 6))={0,2,4,5} := by decide
    have hB : insert 3 ({0,4,5} : Finset (Fin 6))={0,3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h57 : f {2,4}-f {2}-f {4}+f ∅=0 := by
    have h := hf 57
    change f (insert 2 (insert 4 (∅ : Finset (Fin 6))))-
      f (insert 2 (∅ : Finset (Fin 6)))-f (insert 4 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 2 (insert 4 (∅ : Finset (Fin 6)))={2,4} := by decide
    have hA : insert 2 (∅ : Finset (Fin 6))={2} := by decide
    have hB : insert 4 (∅ : Finset (Fin 6))={4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h58 : f {2,4,5}-f {2,5}-f {4,5}+f {5}=0 := by
    have h := hf 58
    change f (insert 2 (insert 4 ({5} : Finset (Fin 6))))-
      f (insert 2 ({5} : Finset (Fin 6)))-f (insert 4 ({5} : Finset (Fin 6)))+f {5}=0 at h
    have hAB : insert 2 (insert 4 ({5} : Finset (Fin 6)))={2,4,5} := by decide
    have hA : insert 2 ({5} : Finset (Fin 6))={2,5} := by decide
    have hB : insert 4 ({5} : Finset (Fin 6))={4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h59 : f {2,5}-f {2}-f {5}+f ∅=0 := by
    have h := hf 59
    change f (insert 2 (insert 5 (∅ : Finset (Fin 6))))-
      f (insert 2 (∅ : Finset (Fin 6)))-f (insert 5 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 2 (insert 5 (∅ : Finset (Fin 6)))={2,5} := by decide
    have hA : insert 2 (∅ : Finset (Fin 6))={2} := by decide
    have hB : insert 5 (∅ : Finset (Fin 6))={5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h60 : f {3,4}-f {3}-f {4}+f ∅=0 := by
    have h := hf 60
    change f (insert 3 (insert 4 (∅ : Finset (Fin 6))))-
      f (insert 3 (∅ : Finset (Fin 6)))-f (insert 4 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 3 (insert 4 (∅ : Finset (Fin 6)))={3,4} := by decide
    have hA : insert 3 (∅ : Finset (Fin 6))={3} := by decide
    have hB : insert 4 (∅ : Finset (Fin 6))={4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h61 : f {3,4,5}-f {3,5}-f {4,5}+f {5}=0 := by
    have h := hf 61
    change f (insert 3 (insert 4 ({5} : Finset (Fin 6))))-
      f (insert 3 ({5} : Finset (Fin 6)))-f (insert 4 ({5} : Finset (Fin 6)))+f {5}=0 at h
    have hAB : insert 3 (insert 4 ({5} : Finset (Fin 6)))={3,4,5} := by decide
    have hA : insert 3 ({5} : Finset (Fin 6))={3,5} := by decide
    have hB : insert 4 ({5} : Finset (Fin 6))={4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h62 : f {0,1,3,5}-f {0,1,3}-f {0,1,5}+f {0,1}=0 := by
    have h := hf 62
    change f (insert 3 (insert 5 ({0,1} : Finset (Fin 6))))-
      f (insert 3 ({0,1} : Finset (Fin 6)))-f (insert 5 ({0,1} : Finset (Fin 6)))+f {0,1}=0 at h
    have hAB : insert 3 (insert 5 ({0,1} : Finset (Fin 6)))={0,1,3,5} := by decide
    have hA : insert 3 ({0,1} : Finset (Fin 6))={0,1,3} := by decide
    have hB : insert 5 ({0,1} : Finset (Fin 6))={0,1,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h63 : f {4,5}-f {4}-f {5}+f ∅=0 := by
    have h := hf 63
    change f (insert 4 (insert 5 (∅ : Finset (Fin 6))))-
      f (insert 4 (∅ : Finset (Fin 6)))-f (insert 5 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 4 (insert 5 (∅ : Finset (Fin 6)))={4,5} := by decide
    have hA : insert 4 (∅ : Finset (Fin 6))={4} := by decide
    have hB : insert 5 (∅ : Finset (Fin 6))={5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have v0 : f ∅=0 := by
    linear_combination h1
  have v1 : f {0}=0 := by
    linear_combination h2
  have v2 : f {1}=0 := by
    linear_combination h3
  have v3 : f {0,1}=0 := by
    linear_combination (-1) * h1 + h2 + h3 + h8
  have v4 : f {2}=0 := by
    linear_combination h4
  have v5 : f {0,2}=0 := by
    linear_combination (-1) * h1 + h2 + h4 + h16
  have v6 : f {1,2}=0 := by
    linear_combination (-1) * h1 + h3 + h4 + h36
  have v7 : f {0,1,2}=0 := by
    linear_combination (-2) * h1 + h2 + h3 + h4 + h9 + h16 + h36
  have v8 : f {3}=0 := by
    linear_combination h5
  have v9 : f {0,3}=0 := by
    linear_combination (-1) * h1 + h2 + h5 + h23
  have v10 : f {1,3}=0 := by
    linear_combination (-1) * h1 + h3 + h5 + h42
  have v11 : f {0,1,3}=0 := by
    linear_combination h0
  have v12 : f {2,3}=0 := by
    linear_combination (-1) * h1 + h4 + h5 + h51
  have v13 : f {0,2,3}=0 := by
    linear_combination (-2) * h1 + h2 + h4 + h5 + h17 + h23 + h51
  have v14 : f {1,2,3}=0 := by
    linear_combination (-2) * h1 + h3 + h4 + h5 + h37 + h42 + h51
  have v15 : f {0,1,2,3}=0 := by
    linear_combination h0 + (-1) * h1 + h4 + h18 + h37 + h51
  have v16 : f {4}=0 := by
    linear_combination h6
  have v17 : f {0,4}=0 := by
    linear_combination (-1) * h1 + h2 + h6 + h28
  have v18 : f {1,4}=0 := by
    linear_combination (-1) * h1 + h3 + h6 + h46
  have v19 : f {0,1,4}=0 := by
    linear_combination (-2) * h1 + h2 + h3 + h6 + h10 + h28 + h46
  have v20 : f {2,4}=0 := by
    linear_combination (-1) * h1 + h4 + h6 + h57
  have v21 : f {0,2,4}=0 := by
    linear_combination (-2) * h1 + h2 + h4 + h6 + h19 + h28 + h57
  have v22 : f {1,2,4}=0 := by
    linear_combination (-2) * h1 + h3 + h4 + h6 + h38 + h46 + h57
  have v23 : f {0,1,2,4}=0 := by
    linear_combination h0 + (-1) * h1 + h4 + (-1) * h5 + h6 + h10 + (-1) * h12 + (-1) * h14 + h15 + h21 + (-2) * h25 + h26 + h28 + (-1) * h29 + (-1) * h30 + h31 + h32 + (-1) * h33 + (2) * h34 + (-1) * h35 + h39 + (-1) * h42 + h46 + h52 + (-1) * h53 + (-1) * h55 + h56 + h57
  have v24 : f {3,4}=0 := by
    linear_combination (-1) * h1 + h5 + h6 + h60
  have v25 : f {0,3,4}=0 := by
    linear_combination h0 + (-1) * h3 + h6 + (-1) * h11 + h29 + (-1) * h42 + h60
  have v26 : f {1,3,4}=0 := by
    linear_combination h0 + (-1) * h2 + h6 + (-1) * h11 + (-1) * h23 + h47 + h60
  have v27 : f {0,1,3,4}=0 := by
    linear_combination (2) * h0 + h1 + (-1) * h2 + (-1) * h3 + (-1) * h5 + h6 + (-1) * h11 + (-1) * h23 + h29 + (-1) * h42 + h47 + h60
  have v28 : f {2,3,4}=0 := by
    linear_combination (-2) * h1 + h4 + h5 + h6 + h52 + h57 + h60
  have v29 : f {0,2,3,4}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h3 + h4 + h6 + (-1) * h11 + h20 + h29 + (-1) * h42 + h52 + h57 + h60
  have v30 : f {1,2,3,4}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h2 + h4 + h6 + (-1) * h11 + (-1) * h23 + h39 + h47 + h52 + h57 + h60
  have v31 : f {0,1,2,3,4}=0 := by
    linear_combination (3) * h0 + (2) * h1 + (-2) * h2 + (-2) * h3 + h4 + (-2) * h5 + h6 + (-1) * h11 + (-1) * h12 + (-1) * h14 + h15 + h21 + (-1) * h23 + (-2) * h25 + h26 + (-1) * h30 + h31 + h32 + (-1) * h33 + (2) * h34 + (-1) * h35 + h39 + (-2) * h42 + h47 + h52 + (-1) * h55 + h56 + h57 + h60
  have v32 : f {5}=0 := by
    linear_combination h7
  have v33 : f {0,5}=0 := by
    linear_combination (-1) * h1 + h2 + h7 + h33
  have v34 : f {1,5}=0 := by
    linear_combination (-1) * h1 + h3 + h7 + h50
  have v35 : f {0,1,5}=0 := by
    linear_combination h0 + (-1) * h5 + h7 + (-1) * h25 + h34 + (-1) * h42 + h50
  have v36 : f {2,5}=0 := by
    linear_combination (-1) * h1 + h4 + h7 + h59
  have v37 : f {0,2,5}=0 := by
    linear_combination h0 + (-1) * h3 + h4 + (-1) * h5 + h7 + (-1) * h12 + h21 + (-1) * h25 + h34 + (-1) * h42 + h59
  have v38 : f {1,2,5}=0 := by
    linear_combination h0 + (-1) * h2 + h4 + (-1) * h5 + h7 + (-1) * h12 + (-1) * h25 + (-1) * h33 + h34 + h40 + (-1) * h42 + h50 + h59
  have v39 : f {0,1,2,5}=0 := by
    linear_combination (2) * h0 + h1 + (-1) * h2 + (-1) * h3 + h4 + (-2) * h5 + h7 + (-1) * h12 + h21 + (-2) * h25 + (-1) * h33 + (2) * h34 + h40 + (-2) * h42 + h50 + h59
  have v40 : f {3,5}=0 := by
    linear_combination h0 + h1 + (-1) * h2 + (-1) * h3 + h7 + (-1) * h8 + (-1) * h25 + (-1) * h43 + h62
  have v41 : f {0,3,5}=0 := by
    linear_combination h0 + (-1) * h3 + h7 + (-1) * h8 + h24 + (-1) * h25 + h33 + (-1) * h43 + h62
  have v42 : f {1,3,5}=0 := by
    linear_combination h0 + (-1) * h2 + h7 + (-1) * h8 + (-1) * h25 + h50 + h62
  have v43 : f {0,1,3,5}=0 := by
    linear_combination (2) * h0 + h1 + (-1) * h2 + (-1) * h3 + (-1) * h5 + h7 + (-1) * h8 + (-1) * h25 + h34 + (-1) * h42 + h50 + h62
  have v44 : f {2,3,5}=0 := by
    linear_combination h0 + (-1) * h2 + (-1) * h3 + h4 + h7 + (-1) * h8 + (-1) * h25 + (-1) * h43 + h54 + h59 + h62
  have v45 : f {0,2,3,5}=0 := by
    linear_combination (2) * h0 + h1 + (-1) * h2 + (-2) * h3 + h4 + (-1) * h5 + h7 + (-1) * h8 + (-1) * h13 + h22 + (-1) * h25 + h34 + (-1) * h42 + (-1) * h43 + h54 + h59 + h62
  have v46 : f {1,2,3,5}=0 := by
    linear_combination (2) * h0 + h1 + (-2) * h2 + (-1) * h3 + h4 + (-1) * h5 + h7 + (-1) * h8 + (-1) * h13 + (-1) * h24 + (-1) * h25 + (-1) * h33 + h34 + h41 + (-1) * h42 + h50 + h54 + h59 + h62
  have v47 : f {0,1,2,3,5}=0 := by
    linear_combination (3) * h0 + (2) * h1 + (-2) * h2 + (-2) * h3 + h4 + (-2) * h5 + h7 + (-1) * h8 + (-1) * h13 + h22 + (-1) * h24 + (-1) * h25 + (-1) * h33 + (2) * h34 + h41 + (-2) * h42 + h50 + h54 + h59 + h62
  have v48 : f {4,5}=0 := by
    linear_combination (-1) * h1 + h6 + h7 + h63
  have v49 : f {0,4,5}=0 := by
    linear_combination (-2) * h1 + h2 + h6 + h7 + h30 + h33 + h63
  have v50 : f {1,4,5}=0 := by
    linear_combination (-2) * h1 + h3 + h6 + h7 + h48 + h50 + h63
  have v51 : f {0,1,4,5}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h5 + h6 + h7 + (-1) * h25 + h31 + h34 + (-1) * h42 + h48 + h50 + h63
  have v52 : f {2,4,5}=0 := by
    linear_combination (-2) * h1 + h4 + h6 + h7 + h58 + h59 + h63
  have v53 : f {0,2,4,5}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h3 + h4 + (-1) * h5 + h6 + h7 + (-1) * h12 + h21 + (-1) * h25 + h32 + h34 + (-1) * h42 + h58 + h59 + h63
  have v54 : f {1,2,4,5}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h2 + h4 + (-1) * h5 + h6 + h7 + (-1) * h12 + (-1) * h25 + (-1) * h33 + h34 + h40 + (-1) * h42 + h49 + h50 + h58 + h59 + h63
  have v55 : f {0,1,2,4,5}=0 := by
    linear_combination (3) * h0 + (2) * h1 + (-2) * h2 + (-2) * h3 + h4 + (-3) * h5 + h6 + h7 + (-2) * h12 + (-1) * h14 + h15 + h21 + (-3) * h25 + h26 + (-1) * h27 + (-1) * h30 + h31 + h32 + (-2) * h33 + (3) * h34 + h40 + (-3) * h42 + h49 + h50 + (-1) * h55 + h56 + h58 + h59 + h63
  have v56 : f {3,4,5}=0 := by
    linear_combination h0 + (-1) * h2 + (-1) * h3 + h6 + h7 + (-1) * h8 + (-1) * h25 + (-1) * h43 + h61 + h62 + h63
  have v57 : f {0,3,4,5}=0 := by
    linear_combination (2) * h0 + h1 + (-1) * h2 + (-2) * h3 + (-1) * h5 + h6 + h7 + (-1) * h8 + (-1) * h14 + (-2) * h25 + h26 + h31 + h34 + (-1) * h42 + (-1) * h43 + h61 + h62 + h63
  have v58 : f {1,3,4,5}=0 := by
    linear_combination (2) * h0 + h1 + (-2) * h2 + (-1) * h3 + (-1) * h5 + h6 + h7 + (-1) * h8 + (-1) * h14 + (-2) * h25 + (-1) * h30 + h31 + (-1) * h33 + h34 + (-1) * h42 + (-1) * h43 + h44 + h48 + h50 + h61 + h62 + h63
  have v59 : f {0,1,3,4,5}=0 := by
    linear_combination (3) * h0 + (2) * h1 + (-2) * h2 + (-2) * h3 + (-2) * h5 + h6 + h7 + (-1) * h8 + (-1) * h14 + (-3) * h25 + h26 + (-1) * h30 + (2) * h31 + (-1) * h33 + (2) * h34 + (-2) * h42 + (-1) * h43 + h44 + h48 + h50 + h61 + h62 + h63
  have v60 : f {2,3,4,5}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h2 + (-1) * h3 + h4 + h6 + h7 + (-1) * h8 + (-1) * h25 + (-1) * h43 + h55 + h58 + h59 + h61 + h62 + h63
  have v61 : f {0,2,3,4,5}=0 := by
    linear_combination (3) * h0 + (2) * h1 + (-2) * h2 + (-3) * h3 + h4 + (-2) * h5 + h6 + h7 + (-1) * h8 + (-1) * h12 + (-1) * h14 + h21 + (-3) * h25 + h26 + (-1) * h30 + h31 + h32 + (-1) * h33 + (2) * h34 + (-2) * h42 + (-1) * h43 + h56 + h58 + h59 + h61 + h62 + h63
  have v62 : f {1,2,3,4,5}=0 := by
    linear_combination (3) * h0 + (2) * h1 + (-3) * h2 + (-2) * h3 + h4 + (-2) * h5 + h6 + h7 + (-1) * h8 + (-1) * h12 + (-1) * h14 + (-3) * h25 + h26 + (-1) * h27 + (-1) * h30 + h31 + (-2) * h33 + (2) * h34 + h40 + (-2) * h42 + (-1) * h43 + h45 + h49 + h50 + h56 + h58 + h59 + h61 + h62 + h63
  have v63 : f {0,1,2,3,4,5}=0 := by
    linear_combination (5) * h0 + (5) * h1 + (-4) * h2 + (-4) * h3 + h4 + (-4) * h5 + h6 + h7 + (-1) * h8 + (-2) * h12 + (-2) * h14 + h15 + h21 + (-5) * h25 + (2) * h26 + (-1) * h27 + (-2) * h30 + (2) * h31 + h32 + (-3) * h33 + (4) * h34 + h40 + (-4) * h42 + (-1) * h43 + h45 + h49 + h50 + (-1) * h55 + (2) * h56 + h58 + h59 + h61 + h62 + h63
  funext S
  change f S=0
  have casesS : ∀ S : Finset (Fin 6), S=∅ ∨ S={0} ∨ S={1} ∨ S={0,1} ∨ S={2} ∨ S={0,2} ∨ S={1,2} ∨ S={0,1,2} ∨ S={3} ∨ S={0,3} ∨ S={1,3} ∨ S={0,1,3} ∨ S={2,3} ∨ S={0,2,3} ∨ S={1,2,3} ∨ S={0,1,2,3} ∨ S={4} ∨ S={0,4} ∨ S={1,4} ∨ S={0,1,4} ∨ S={2,4} ∨ S={0,2,4} ∨ S={1,2,4} ∨ S={0,1,2,4} ∨ S={3,4} ∨ S={0,3,4} ∨ S={1,3,4} ∨ S={0,1,3,4} ∨ S={2,3,4} ∨ S={0,2,3,4} ∨ S={1,2,3,4} ∨ S={0,1,2,3,4} ∨ S={5} ∨ S={0,5} ∨ S={1,5} ∨ S={0,1,5} ∨ S={2,5} ∨ S={0,2,5} ∨ S={1,2,5} ∨ S={0,1,2,5} ∨ S={3,5} ∨ S={0,3,5} ∨ S={1,3,5} ∨ S={0,1,3,5} ∨ S={2,3,5} ∨ S={0,2,3,5} ∨ S={1,2,3,5} ∨ S={0,1,2,3,5} ∨ S={4,5} ∨ S={0,4,5} ∨ S={1,4,5} ∨ S={0,1,4,5} ∨ S={2,4,5} ∨ S={0,2,4,5} ∨ S={1,2,4,5} ∨ S={0,1,2,4,5} ∨ S={3,4,5} ∨ S={0,3,4,5} ∨ S={1,3,4,5} ∨ S={0,1,3,4,5} ∨ S={2,3,4,5} ∨ S={0,2,3,4,5} ∨ S={1,2,3,4,5} ∨ S={0,1,2,3,4,5} := by decide
  rcases casesS S with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem empty_zero : integerFunction ∅=0 := by decide

theorem singleton_zero : ∀ v : Fin 6,integerFunction {v}=0 := by decide

theorem boolean_differences : ∀ u v : Fin 6,u≠v → ∀ S : Finset (Fin 6),
    u∉S → v∉S → integerDelta integerFunction u v S=0 ∨
      integerDelta integerFunction u v S=1 := by decide

theorem extreme : ExtremeSupermodular (realFunction integerFunction) :=
  extreme_of_row_kernel integerFunction rows pivot pivot_one row_zero valid_rows
    row_kernel_zero empty_zero singleton_zero boolean_differences

end K1122Complement

end SmallBoolean
end GraphicalZonotopes
