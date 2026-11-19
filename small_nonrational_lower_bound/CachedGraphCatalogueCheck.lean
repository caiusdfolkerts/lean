module
prelude
public import FastGraphCatalogueCheck

@[expose] public section

/-! Reuse of checked edge images in graph-catalogue replay. -/

namespace Papers.RationalityTen.CachedGraphCatalogueCheck

open GraphCatalogueCore GraphCatalogueCheck GrowthBitsets ConcreteGrowth

variable {n v g after : Nat}

def packedEdgeMap (code : Nat) (edge : Fin 45) : Fin 45 :=
  Fin.ofNat 45 (Nat.land (code >>> (6 * edge.val)) 63)

def extensionCheck (incidence : Fin n → Fin v → Bool) (bound : Nat)
    (edgeMaps : Fin g → Fin n → Fin n)
    (source : State n) (next : Fin after → State n) (edge : Fin n) :
    Choice v after g → Bool
  | .selected => source.mask.testBit edge.val
  | .saturated vertex =>
      incidence edge vertex && decide (bound ≤ degree incidence source.edges vertex)
  | .extension model frame =>
      decide ((next model).mask = PrimitiveBitsetGrowth.mask
        ((edge :: source.edges).map (edgeMaps frame)))

theorem extensionCheck_eq (incidence : Fin n → Fin v → Bool) (bound : Nat)
    (renamings : Fin g → IncidenceRenaming incidence)
    (edgeMaps : Fin g → Fin n → Fin n)
    (hexact : ∀ frame edge, edgeMaps frame edge = (renamings frame).cells.forward edge)
    (source : State n) (next : Fin after → State n) (edge : Fin n)
    (choice : Choice v after g) :
    extensionCheck incidence bound edgeMaps source next edge choice =
      GraphCatalogueCheck.extensionCheck incidence bound renamings source next edge choice := by
  have heq : edgeMaps = fun frame => (renamings frame).cells.forward :=
    funext fun frame => funext (hexact frame)
  rw [heq]
  cases choice <;> simp only [extensionCheck, GraphCatalogueCheck.extensionCheck,
    bitAt_eq_testBit, PrimitiveBitsetGrowth.mask_eq]

#print axioms extensionCheck_eq

end Papers.RationalityTen.CachedGraphCatalogueCheck
