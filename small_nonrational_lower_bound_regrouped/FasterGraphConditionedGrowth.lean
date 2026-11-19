module
prelude
public import FastGraphConditionedGrowth
public import FastAvailability

@[expose] public section

/-! The same complete growth checker with single-pass availability checks. -/

namespace Papers.RationalityTen.FasterGraphConditionedGrowth

open GraphConditionedGrowth GraphGrowthConstraints

variable {n r e v k g l t : Nat}

def nodeBody (D : Problem n r e v k) (maps : Fin g → Fin n → Fin n)
    (bounds : Fin t → FastGraphRuleCheck.Bounds n) (bases : Fin t → Nat)
    (leaves : Fin l → List (Fin n))
    (nodes : Fin t → Node n r e v k g l t) (i : Fin t) : Bool :=
  match (nodes i).action with
  | .terminal leaf =>
      (decide ((nodes i).mask = PrimitiveBitsetGrowth.mask (leaves leaf)) &&
        decide ((nodes i).mask ≠ 0)) &&
      WitnessGrowthDAG.closedCheck D.ridgeList (nodes i).cells
  | .split rule children =>
      ((FastAvailability.check D (nodes i) (bases i) &&
        FastGraphRuleCheck.check D (nodes i).cells (nodes i).mask
          (nodes i).available (bounds i) rule) &&
        children.all (RawGraphConditionedGrowth.childCheck maps nodes i)) &&
      decide (Nat.land (Nat.land (candidates D rule) (nodes i).available)
        (PrimitiveBitsetGrowth.mask (children.map Child.cell)) =
          Nat.land (candidates D rule) (nodes i).available)

def nodeCheck (D : Problem n r e v k) (maps : Fin g → Fin n → Fin n)
    (bounds : Fin t → FastGraphRuleCheck.Bounds n) (bases : Fin t → Nat)
    (leaves : Fin l → List (Fin n))
    (nodes : Fin t → Node n r e v k g l t) (i : Fin t) : Bool :=
  (FastGraphConditionedGrowth.ascending (nodes i).cells &&
    decide ((nodes i).mask = PrimitiveBitsetGrowth.mask (nodes i).cells)) &&
  nodeBody D maps bounds bases leaves nodes i

theorem nodeCheck_sound (D : Problem n r e v k) (maps : Fin g → Fin n → Fin n)
    (bounds : Fin t → FastGraphRuleCheck.Bounds n) (bases : Fin t → Nat)
    (leaves : Fin l → List (Fin n))
    (nodes : Fin t → Node n r e v k g l t) (i : Fin t)
    (h : nodeCheck D maps bounds bases leaves nodes i = true) :
    FastGraphConditionedGrowth.nodeCheck D maps bounds leaves nodes i = true := by
  obtain ⟨hstate, hbody⟩ := Bool.and_eq_true_iff.mp h
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hstate, ?_⟩
  cases ha : (nodes i).action with
  | terminal leaf =>
    simpa only [nodeBody, FastGraphConditionedGrowth.nodeBody, ha] using hbody
  | split rule children =>
    obtain ⟨hleft, hcover⟩ := Bool.and_eq_true_iff.mp
      (by simpa only [nodeBody, ha] using hbody)
    obtain ⟨hlocal, hchildren⟩ := Bool.and_eq_true_iff.mp hleft
    obtain ⟨havailable, hrule⟩ := Bool.and_eq_true_iff.mp hlocal
    simp only [FastGraphConditionedGrowth.nodeBody, ha]
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr
        ⟨FastAvailability.check_sound D (nodes i) (bases i) havailable, hrule⟩,
       hchildren⟩, hcover⟩

#print axioms nodeCheck_sound

end Papers.RationalityTen.FasterGraphConditionedGrowth
