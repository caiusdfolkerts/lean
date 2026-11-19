module
prelude
public import SixBudgetEnumeration

@[expose] public section

set_option maxRecDepth 100000

set_option maxHeartbeats 0

namespace Papers.RationalityTen.SixBudgetEnumeration

def literalRows5 : List Row := [
  ⟨10, 15, 10, [0,0,0,0,0,0,5]⟩,
  ⟨10, 15, 7, [0,0,0,0,2,0,3]⟩
]

theorem typeLists5_eq : typeLists 5 =
  [[0,0,0,0,0,0,5], [0,0,0,0,2,0,3], [0,0,0,0,4,0,1]] := by decide +kernel

theorem rowsForTypes5_000_eq : rowsForTypes 5 [0,0,0,0,0,0,5] =
[
  ⟨10, 15, 10, [0,0,0,0,0,0,5]⟩
] := by decide +kernel

theorem rowsForTypes5_001_eq : rowsForTypes 5 [0,0,0,0,2,0,3] =
[
  ⟨10, 15, 7, [0,0,0,0,2,0,3]⟩
] := by decide +kernel

theorem rowsForTypes5_002_eq : rowsForTypes 5 [0,0,0,0,4,0,1] =
[

] := by decide +kernel

theorem rowsForTotal5_eq : rowsForTotal 5 = literalRows5 := by
  simp only [rowsForTotal, typeLists5_eq, List.flatMap_cons, List.flatMap_nil, rowsForTypes5_000_eq, rowsForTypes5_001_eq, rowsForTypes5_002_eq]
  rfl

#print axioms rowsForTotal5_eq

end Papers.RationalityTen.SixBudgetEnumeration
