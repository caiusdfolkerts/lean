module
prelude
public import GraphRouteSelector

@[expose] public section

/-! Exact numerical parameters of the eleven small graph rows and the remaining
six-vertex-facet row. Every graph case refers to one of these fixed records. -/
namespace Papers.RationalityTen.GraphRowSpecifications
open GraphRouteSelector

def rowOfCode : Nat → Row
  | 16 => ⟨16, 13, [0, 3, 8, 2, 0], 10⟩
  | 19 => ⟨19, 13, [0, 2, 7, 4, 0], 11⟩
  | 23 => ⟨23, 11, [0, 4, 10, 0, 0], 10⟩
  | 24 => ⟨24, 12, [0, 4, 8, 2, 0], 10⟩
  | 25 => ⟨25, 11, [0, 3, 9, 2, 0], 11⟩
  | 26 => ⟨26, 12, [0, 3, 7, 4, 0], 11⟩
  | 27 => ⟨27, 12, [0, 2, 6, 6, 0], 12⟩
  | 28 => ⟨28, 10, [0, 5, 10, 0, 0], 10⟩
  | 29 => ⟨29, 11, [0, 5, 8, 2, 0], 10⟩
  | 30 => ⟨30, 11, [0, 4, 7, 4, 0], 11⟩
  | 31 => ⟨31, 10, [0, 6, 8, 2, 0], 10⟩
  | 32 => ⟨32, 12, [0, 4, 5, 4, 1], 12⟩
  | code => ⟨code, 0, [], 0⟩

def isActualCode (code : Nat) : Bool :=
  decide (code = 16 ∨ code = 19 ∨ code = 23 ∨ code = 24 ∨ code = 25 ∨ code = 26 ∨ code = 27 ∨ code = 28 ∨ code = 29 ∨ code = 30 ∨ code = 31 ∨ code = 32)

theorem code_eq (code : Nat) : (rowOfCode code).code = code := by
  unfold rowOfCode
  split <;> rfl

#print axioms code_eq
end Papers.RationalityTen.GraphRowSpecifications
