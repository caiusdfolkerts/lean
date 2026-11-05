module
prelude
public import GraphCatalogueCheck
public import PrimitiveBitsetGrowth

@[expose] public section

/-! Primitive bit operations for the already proved graph-catalogue checker. -/

namespace Papers.RationalityTen.FastGraphCatalogueCheck

open GraphCatalogueCore GraphCatalogueCheck GrowthBitsets ConcreteGrowth

variable {n v g after : Nat}

def stateCheck (state : State n) : Bool :=
  decide state.edges.Nodup && decide (state.mask = PrimitiveBitsetGrowth.mask state.edges)

theorem stateCheck_eq (state : State n) :
    stateCheck state = GraphCatalogueCheck.stateCheck state := by
  simp only [stateCheck, GraphCatalogueCheck.stateCheck, PrimitiveBitsetGrowth.mask_eq]

def extensionCheck (incidence : Fin n → Fin v → Bool) (bound : Nat)
    (renamings : Fin g → IncidenceRenaming incidence)
    (source : State n) (next : Fin after → State n) (edge : Fin n) :
    Choice v after g → Bool
  | .selected => source.mask.testBit edge.val
  | .saturated vertex =>
      incidence edge vertex && decide (bound ≤ degree incidence source.edges vertex)
  | .extension model frame =>
      decide ((next model).mask = PrimitiveBitsetGrowth.mask
        ((edge :: source.edges).map (renamings frame).cells.forward))

theorem extensionCheck_eq (incidence : Fin n → Fin v → Bool) (bound : Nat)
    (renamings : Fin g → IncidenceRenaming incidence)
    (source : State n) (next : Fin after → State n) (edge : Fin n)
    (choice : Choice v after g) :
    extensionCheck incidence bound renamings source next edge choice =
      GraphCatalogueCheck.extensionCheck incidence bound renamings source next edge choice := by
  cases choice <;> simp only [extensionCheck, GraphCatalogueCheck.extensionCheck,
    bitAt_eq_testBit, PrimitiveBitsetGrowth.mask_eq]

#print axioms extensionCheck_eq

end Papers.RationalityTen.FastGraphCatalogueCheck
