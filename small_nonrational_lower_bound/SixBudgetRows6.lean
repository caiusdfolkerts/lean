module
prelude
public import SixBudgetEnumeration

@[expose] public section

set_option maxRecDepth 100000

set_option maxHeartbeats 0

namespace Papers.RationalityTen.SixBudgetEnumeration

def literalRows6 : List Row := [

]

theorem typeLists6_eq : typeLists 6 =
  [] := by decide +kernel

theorem rowsForTotal6_eq : rowsForTotal 6 = literalRows6 := by
  simp only [rowsForTotal, typeLists6_eq, List.flatMap_cons, List.flatMap_nil]
  rfl

#print axioms rowsForTotal6_eq

end Papers.RationalityTen.SixBudgetEnumeration
