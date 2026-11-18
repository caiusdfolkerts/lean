module
prelude
public import FasterGraphConditionedGrowth
public import FastMaskCardinality

@[expose] public section

/-! The ordinary graph checker with two proved representation optimizations:
missing-feature tests visit a checked support list, and45-bit cardinalities
use completely checked byte tables. All original rules are preserved. -/

namespace Papers.RationalityTen.FastGeneralGraphReplay

open GraphConditionedGrowth GraphGrowthConstraints GrowthBitsets

variable {n r v k g l t : Nat}

def SupportsMissing (D : Problem n r 45 v k) (support : List (Fin 45)) : Prop :=
  ∀ q, q ∈ support ∨ D.missingRows q = 0

def possibleCheck (D : Problem n r 45 v k) (support : List (Fin 45))
    (S : List (Fin n)) (available possible : Nat) : Bool :=
  decide (Nat.land (missingUnion D S) possible = missingUnion D S) &&
    support.all fun q => possible.testBit q.val ||
      decide (Nat.land available (D.missingRows q) = 0)

theorem possibleCheck_sound (D : Problem n r 45 v k) (support : List (Fin 45))
    (hs : SupportsMissing D support) (S : List (Fin n)) (available possible : Nat)
    (h : possibleCheck D support S available possible = true) :
    possibleMissingCheck D S available possible = true := by
  obtain ⟨hselected, hrows⟩ := Bool.and_eq_true_iff.mp h
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hselected, List.all_eq_true.mpr ?_⟩
  intro q _
  rcases hs q with hq | hq
  · exact List.all_eq_true.mp hrows q hq
  · simp only [hq, Nat.land_eq, Nat.and_zero, decide_true, Bool.or_true]

def ruleCheck (D : Problem n r 45 v k) (support : List (Fin 45))
    (S : List (Fin n)) (selected available : Nat)
    (bounds : FastGraphRuleCheck.Bounds n) (rule : Rule r 45 v k) : Bool :=
  match rule with
  | .nonedge q possible => possibleCheck D support S available possible &&
      (decide (FastMaskCardinality.card45 possible = D.missingCount) &&
        (possible.testBit q.val && !(missingUnion D S).testBit q.val))
  | .nonedgeCapacity possible => possibleCheck D support S available possible &&
      (decide (D.missingCount < FastMaskCardinality.card45 (missingUnion D S)) ||
        decide (FastMaskCardinality.card45 possible < D.missingCount))
  | _ => FastGraphRuleCheck.check D S selected available bounds rule

theorem ruleCheck_sound (D : Problem n r 45 v k) (support : List (Fin 45))
    (hs : SupportsMissing D support) (S : List (Fin n)) (selected available : Nat)
    (bounds : FastGraphRuleCheck.Bounds n) (rule : Rule r 45 v k)
    (h : ruleCheck D support S selected available bounds rule = true) :
    FastGraphRuleCheck.check D S selected available bounds rule = true := by
  cases rule with
  | nonedge q possible =>
    obtain ⟨hp, hr⟩ := Bool.and_eq_true_iff.mp h
    have hp' := possibleCheck_sound D support hs S available possible hp
    simpa only [FastGraphRuleCheck.check, GraphGrowthConstraints.ruleCheck,
      hp', Bool.true_and, FastMaskCardinality.card45_eq] using hr
  | nonedgeCapacity possible =>
    obtain ⟨hp, hr⟩ := Bool.and_eq_true_iff.mp h
    have hp' := possibleCheck_sound D support hs S available possible hp
    simpa only [FastGraphRuleCheck.check, GraphGrowthConstraints.ruleCheck,
      hp', Bool.true_and, FastMaskCardinality.card45_eq] using hr
  | ridge q owner => exact h
  | edge q => exact h
  | kindCapacity j => exact h
  | vertexCapacity a => exact h

def nodeBody (D : Problem n r 45 v k) (support : List (Fin 45))
    (maps : Fin g → Fin n → Fin n)
    (bounds : Fin t → FastGraphRuleCheck.Bounds n) (bases : Fin t → Nat)
    (leaves : Fin l → List (Fin n))
    (nodes : Fin t → Node n r 45 v k g l t) (i : Fin t) : Bool :=
  match (nodes i).action with
  | .terminal leaf =>
      (decide ((nodes i).mask = PrimitiveBitsetGrowth.mask (leaves leaf)) &&
        decide ((nodes i).mask ≠ 0)) &&
      WitnessGrowthDAG.closedCheck D.ridgeList (nodes i).cells
  | .split rule children =>
      ((FastAvailability.check D (nodes i) (bases i) &&
        ruleCheck D support (nodes i).cells (nodes i).mask
          (nodes i).available (bounds i) rule) &&
        children.all (RawGraphConditionedGrowth.childCheck maps nodes i)) &&
      decide (Nat.land (Nat.land (candidates D rule) (nodes i).available)
        (PrimitiveBitsetGrowth.mask (children.map Child.cell)) =
          Nat.land (candidates D rule) (nodes i).available)

def nodeCheck (D : Problem n r 45 v k) (support : List (Fin 45))
    (maps : Fin g → Fin n → Fin n)
    (bounds : Fin t → FastGraphRuleCheck.Bounds n) (bases : Fin t → Nat)
    (leaves : Fin l → List (Fin n))
    (nodes : Fin t → Node n r 45 v k g l t) (i : Fin t) : Bool :=
  (FastGraphConditionedGrowth.ascending (nodes i).cells &&
    decide ((nodes i).mask = PrimitiveBitsetGrowth.mask (nodes i).cells)) &&
  nodeBody D support maps bounds bases leaves nodes i

theorem nodeCheck_sound (D : Problem n r 45 v k) (support : List (Fin 45))
    (hm : SupportsMissing D support) (maps : Fin g → Fin n → Fin n)
    (bounds : Fin t → FastGraphRuleCheck.Bounds n) (bases : Fin t → Nat)
    (leaves : Fin l → List (Fin n))
    (nodes : Fin t → Node n r 45 v k g l t) (i : Fin t)
    (h : nodeCheck D support maps bounds bases leaves nodes i = true) :
    RawGraphConditionedGrowth.nodeCheck D maps leaves nodes i = true := by
  apply FastGraphConditionedGrowth.nodeCheck_sound D maps bounds leaves nodes i
  apply FasterGraphConditionedGrowth.nodeCheck_sound D maps bounds bases leaves nodes i
  obtain ⟨hstate, hbody⟩ := Bool.and_eq_true_iff.mp h
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hstate, ?_⟩
  cases ha : (nodes i).action with
  | terminal leaf =>
    simpa only [nodeBody, FasterGraphConditionedGrowth.nodeBody, ha] using hbody
  | split rule children =>
    obtain ⟨hleft, hcover⟩ := Bool.and_eq_true_iff.mp
      (by simpa only [nodeBody, ha] using hbody)
    obtain ⟨hlocal, hchildren⟩ := Bool.and_eq_true_iff.mp hleft
    obtain ⟨havailable, hrule⟩ := Bool.and_eq_true_iff.mp hlocal
    simp only [FasterGraphConditionedGrowth.nodeBody, ha]
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr
        ⟨havailable, ruleCheck_sound D support hm _ _ _ _ rule hrule⟩,
       hchildren⟩, hcover⟩

#print axioms nodeCheck_sound

end Papers.RationalityTen.FastGeneralGraphReplay
