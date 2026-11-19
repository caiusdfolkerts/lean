module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Matrix
open scoped BigOperators

namespace Unimodular.ExplicitR10

/-- The thirteen primitive lattice rays of the eight-dimensional example. -/
def rays : Matrix (Fin 13) (Fin 8) ℤ :=
  ![![-1,0,0,0,0,1,1,1], ![1,0,0,0,0,0,0,0],
    ![0,-1,0,-1,1,0,0,1], ![0,1,0,0,0,0,0,0],
    ![0,0,-1,1,0,-1,0,-1], ![0,0,1,0,0,0,0,0],
    ![0,0,0,0,-1,0,-1,-1], ![0,0,0,-1,1,1,1,1],
    ![0,0,0,1,0,0,0,0], ![0,0,0,0,1,0,0,0],
    ![0,0,0,0,0,1,0,0], ![0,0,0,0,0,0,1,0],
    ![0,0,0,0,0,0,0,1]]

/-- The repeated signed R10 columns in the D5 lattice basis. -/
def columns : Matrix (Fin 13) (Fin 5) ℤ :=
  ![![1,1,0,0,1], ![1,1,0,0,1], ![1,0,1,0,1], ![1,0,1,0,1],
    ![1,0,0,1,1], ![1,0,0,1,1], ![1,0,0,0,1], ![0,-1,-1,0,-1],
    ![0,-1,0,-1,-1], ![0,1,0,0,1], ![0,0,1,1,1],
    ![0,0,1,0,1], ![0,0,0,1,1]]

theorem exact_integer_relation : columns.transpose * rays = 0 := by decide

def positiveWeights : Fin 13 → ℤ := ![1,1,4,4,4,4,6,1,1,1,2,4,4]

theorem positiveWeights_pos : ∀ i, 0 < positiveWeights i := by decide

theorem positive_dependence : ∑ i : Fin 13, positiveWeights i • rays i = 0 := by decide

theorem rays_injective : Function.Injective rays := by
  intro i j h
  have h0 := congrFun h (0 : Fin 8)
  have h1 := congrFun h (1 : Fin 8)
  have h2 := congrFun h (2 : Fin 8)
  have h3 := congrFun h (3 : Fin 8)
  have h4 := congrFun h (4 : Fin 8)
  have h5 := congrFun h (5 : Fin 8)
  have h6 := congrFun h (6 : Fin 8)
  have h7 := congrFun h (7 : Fin 8)
  fin_cases i <;> fin_cases j <;> norm_num [rays] at *

theorem rays_nonzero : ∀ i, rays i ≠ 0 := by
  intro i h
  have h0 := congrFun h (0 : Fin 8)
  have h1 := congrFun h (1 : Fin 8)
  have h2 := congrFun h (2 : Fin 8)
  have h3 := congrFun h (3 : Fin 8)
  have h4 := congrFun h (4 : Fin 8)
  have h5 := congrFun h (5 : Fin 8)
  have h6 := congrFun h (6 : Fin 8)
  have h7 := congrFun h (7 : Fin 8)
  fin_cases i <;> norm_num [rays] at *

theorem thirteen_rays : (Finset.univ.image rays).card = 13 := by
  rw [Finset.card_image_of_injective _ rays_injective]
  rfl

def contractIndex : Fin 3 → Fin 13 := ![1,3,5]
def keep : Fin 10 → Fin 13 := ![0,2,4,6,7,8,9,10,11,12]
def tail : Fin 5 → Fin 8 := ![3,4,5,6,7]

theorem contracted_identity_rays :
    ∀ i : Fin 3, rays (contractIndex i) = Pi.single (Fin.castLE (by decide : 3 ≤ 8) i) 1 := by
  decide

def minorMap : Matrix (Fin 5) (Fin 5) ℤ :=
  ![![1,1,1,-1,0], ![1,0,0,0,1], ![0,0,0,-1,1],
    ![0,1,0,0,0], ![1,1,1,-1,1]]

theorem minorMap_det : minorMap.det = 1 := by decide

def r10Columns : Matrix (Fin 10) (Fin 5) ℤ :=
  ![![1,1,0,0,1], ![1,0,1,0,1], ![1,0,0,1,1], ![1,0,0,0,1],
    ![0,1,1,0,1], ![0,1,0,1,1], ![0,1,0,0,1],
    ![0,0,1,1,1], ![0,0,1,0,1], ![0,0,0,1,1]]

def edgePermutation : Fin 10 → Fin 10 := ![6,7,8,5,9,0,2,3,1,4]
def edgeSigns : Fin 10 → ℤ := ![1,1,-1,-1,1,1,1,1,-1,1]

theorem edgePermutation_bijective : Function.Bijective edgePermutation := by
  decide

theorem edgeSigns_units : ∀ i, edgeSigns i = 1 ∨ edgeSigns i = -1 := by decide

theorem quotient_columns : ∀ i : Fin 10,
    minorMap.mulVec (fun j => rays (keep i) (tail j)) =
      edgeSigns i • r10Columns (edgePermutation i) := by decide

#print axioms quotient_columns
end Unimodular.ExplicitR10
