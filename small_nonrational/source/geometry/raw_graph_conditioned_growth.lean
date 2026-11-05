module
prelude
public import GraphConditionedGrowth

@[expose] public section

/-!
# Proof-independent node replay

Concrete node checks use only the forward cell maps.  Their finite replay
therefore needs no geometric imports.  The final theorem supplies the proved
renamings and transfers the identical checks to the semantic checker.
-/

namespace Papers.RationalityTen.RawGraphConditionedGrowth

open GraphConditionedGrowth GraphGrowthConstraints

variable {n r e v k g l t : Nat}

def childCheck (maps : Fin g → Fin n → Fin n)
    (nodes : Fin t → Node n r e v k g l t) (i : Fin t)
    (link : Child n g t) : Bool :=
  decide (link.node.val < i.val) &&
    decide (Nat.land (nodes link.node).mask
      (PrimitiveBitsetGrowth.mask ((link.cell :: (nodes i).cells).map (maps link.frame))) =
        (nodes link.node).mask)

def nodeBody (D : Problem n r e v k) (maps : Fin g → Fin n → Fin n)
    (leaves : Fin l → List (Fin n))
    (nodes : Fin t → Node n r e v k g l t) (i : Fin t) : Bool :=
  match (nodes i).action with
  | .terminal leaf =>
      (decide ((nodes i).mask = PrimitiveBitsetGrowth.mask (leaves leaf)) &&
        decide ((nodes i).mask ≠ 0)) &&
      WitnessGrowthDAG.closedCheck D.ridgeList (nodes i).cells
  | .split rule children =>
      ((availabilityCheck D (nodes i) &&
        ruleCheck D (nodes i).cells (nodes i).mask (nodes i).available rule) &&
        children.all (childCheck maps nodes i)) &&
      decide (Nat.land (Nat.land (candidates D rule) (nodes i).available)
        (PrimitiveBitsetGrowth.mask (children.map Child.cell)) =
          Nat.land (candidates D rule) (nodes i).available)

def nodeCheck (D : Problem n r e v k) (maps : Fin g → Fin n → Fin n)
    (leaves : Fin l → List (Fin n))
    (nodes : Fin t → Node n r e v k g l t) (i : Fin t) : Bool :=
  (decide (nodes i).cells.Nodup &&
    decide ((nodes i).mask = PrimitiveBitsetGrowth.mask (nodes i).cells)) &&
  nodeBody D maps leaves nodes i

theorem nodeCheck_eq (D : Problem n r e v k)
    (maps : Fin g → Fin n → Fin n)
    (renamings : Fin g → GraphGrowthConstraints.Renaming D)
    (hmaps : ∀ frame c, (renamings frame).boundary.cells.forward c = maps frame c)
    (leaves : Fin l → List (Fin n))
    (nodes : Fin t → Node n r e v k g l t) (i : Fin t) :
    nodeCheck D maps leaves nodes i =
      GraphConditionedGrowth.nodeCheck D renamings leaves nodes i := by
  have hm : ∀ frame, (renamings frame).boundary.cells.forward = maps frame :=
    fun frame => funext (hmaps frame)
  have hchildren : childCheck maps nodes i =
      GraphConditionedGrowth.childCheck D renamings nodes i := by
    funext link
    simp only [childCheck, GraphConditionedGrowth.childCheck, hm]
  simp only [nodeCheck, GraphConditionedGrowth.nodeCheck, nodeBody,
    GraphConditionedGrowth.nodeBody, hchildren]
  rfl

#print axioms nodeCheck_eq

end Papers.RationalityTen.RawGraphConditionedGrowth
