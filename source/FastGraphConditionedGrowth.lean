module
prelude
public import RawGraphConditionedGrowth
public import FastGraphRuleCheck

@[expose] public section

/-!
# Efficient replay of graph-conditioned growth

Adjacent comparisons certify distinct selected cells. Short mask-cover lists
certify capacity bounds. Both optimizations imply the original node checker,
so the complete-boundary theorem is unchanged.
-/

namespace Papers.RationalityTen.FastGraphConditionedGrowth

open GraphConditionedGrowth GraphGrowthConstraints

variable {n r e v k g l t : Nat}

def ascendingFrom (lower : Nat) : List (Fin n) → Bool
  | [] => true
  | c :: rest => decide (lower < c.val) && ascendingFrom c.val rest

def ascending : List (Fin n) → Bool
  | [] => true
  | c :: rest => ascendingFrom c.val rest

theorem ascendingFrom_sound (lower : Nat) (xs : List (Fin n))
    (h : ascendingFrom lower xs = true) :
    (∀ c ∈ xs, lower < c.val) ∧ xs.Nodup := by
  induction xs generalizing lower with
  | nil => exact ⟨by simp, List.nodup_nil⟩
  | cons c xs ih =>
    obtain ⟨hlt, htail⟩ := Bool.and_eq_true_iff.mp h
    have hlt := of_decide_eq_true hlt
    obtain ⟨hmem, hnd⟩ := ih c.val htail
    refine ⟨?_, List.nodup_cons.mpr ⟨?_, hnd⟩⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hlt
      · exact Nat.lt_trans hlt (hmem a ha)
    · intro hc
      exact Nat.lt_irrefl c.val (hmem c hc)

theorem ascending_nodup (xs : List (Fin n)) (h : ascending xs = true) : xs.Nodup := by
  cases xs with
  | nil => exact List.nodup_nil
  | cons c xs =>
    obtain ⟨hmem, hnd⟩ := ascendingFrom_sound c.val xs h
    exact List.nodup_cons.mpr ⟨fun hc => Nat.lt_irrefl c.val (hmem c hc), hnd⟩

def nodeBody (D : Problem n r e v k) (maps : Fin g → Fin n → Fin n)
    (bounds : Fin t → FastGraphRuleCheck.Bounds n)
    (leaves : Fin l → List (Fin n))
    (nodes : Fin t → Node n r e v k g l t) (i : Fin t) : Bool :=
  match (nodes i).action with
  | .terminal leaf =>
      (decide ((nodes i).mask = PrimitiveBitsetGrowth.mask (leaves leaf)) &&
        decide ((nodes i).mask ≠ 0)) &&
      WitnessGrowthDAG.closedCheck D.ridgeList (nodes i).cells
  | .split rule children =>
      ((availabilityCheck D (nodes i) &&
        FastGraphRuleCheck.check D (nodes i).cells (nodes i).mask
          (nodes i).available (bounds i) rule) &&
        children.all (RawGraphConditionedGrowth.childCheck maps nodes i)) &&
      decide (Nat.land (Nat.land (candidates D rule) (nodes i).available)
        (PrimitiveBitsetGrowth.mask (children.map Child.cell)) =
          Nat.land (candidates D rule) (nodes i).available)

def nodeCheck (D : Problem n r e v k) (maps : Fin g → Fin n → Fin n)
    (bounds : Fin t → FastGraphRuleCheck.Bounds n)
    (leaves : Fin l → List (Fin n))
    (nodes : Fin t → Node n r e v k g l t) (i : Fin t) : Bool :=
  (ascending (nodes i).cells &&
    decide ((nodes i).mask = PrimitiveBitsetGrowth.mask (nodes i).cells)) &&
  nodeBody D maps bounds leaves nodes i

theorem nodeCheck_sound (D : Problem n r e v k) (maps : Fin g → Fin n → Fin n)
    (bounds : Fin t → FastGraphRuleCheck.Bounds n)
    (leaves : Fin l → List (Fin n))
    (nodes : Fin t → Node n r e v k g l t) (i : Fin t)
    (h : nodeCheck D maps bounds leaves nodes i = true) :
    RawGraphConditionedGrowth.nodeCheck D maps leaves nodes i = true := by
  obtain ⟨hstate, hbody⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hsorted, hmask⟩ := Bool.and_eq_true_iff.mp hstate
  apply Bool.and_eq_true_iff.mpr
  refine ⟨Bool.and_eq_true_iff.mpr
    ⟨decide_eq_true (ascending_nodup _ hsorted), hmask⟩, ?_⟩
  cases ha : (nodes i).action with
  | terminal leaf =>
    simpa only [nodeBody, RawGraphConditionedGrowth.nodeBody, ha] using hbody
  | split rule children =>
    obtain ⟨hleft, hcover⟩ := Bool.and_eq_true_iff.mp
      (by simpa only [nodeBody, ha] using hbody)
    obtain ⟨hlocal, hchildren⟩ := Bool.and_eq_true_iff.mp hleft
    obtain ⟨havailable, hrule⟩ := Bool.and_eq_true_iff.mp hlocal
    simp only [RawGraphConditionedGrowth.nodeBody, ha]
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨havailable,
        FastGraphRuleCheck.check_sound D (nodes i).cells (nodes i).mask
          (nodes i).available (bounds i) rule hrule⟩, hchildren⟩, hcover⟩

#print axioms nodeCheck_sound

end Papers.RationalityTen.FastGraphConditionedGrowth
