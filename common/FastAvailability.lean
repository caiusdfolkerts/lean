module
prelude
public import GraphConditionedGrowth

@[expose] public section

/-!
# Single-pass exclusion propagation

The base exclusion mask is checked once against its definition.  Successful
support propagation returns its final mask, so the final cover check reuses
the same traversal instead of computing the propagation twice.
-/

namespace Papers.RationalityTen.FastAvailability

open BatchedGrowthPruning UnsupportedRidgePruning GraphGrowthConstraints
open GraphConditionedGrowth

variable {n r e v k g l t : Nat}

def propagate {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (selected blocked : Nat) :
    List (Removal n r) → Option Nat
  | [] => some blocked
  | w :: rest =>
      if stepCheck cache selected blocked w then
        propagate cache selected
          (Nat.lor blocked (PrimitiveBitsetGrowth.singleton w.cell.val)) rest
      else none

theorem propagate_sound {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (selected blocked : Nat)
    (removals : List (Removal n r)) (final : Nat)
    (h : propagate cache selected blocked removals = some final) :
    checks cache selected blocked removals = true ∧
      resultingMask blocked removals = final := by
  induction removals generalizing blocked with
  | nil =>
    have heq : blocked = final := Option.some.inj h
    exact ⟨rfl, heq⟩
  | cons w rest ih =>
    by_cases hs : stepCheck cache selected blocked w = true
    · have hh : propagate cache selected
          (Nat.lor blocked (PrimitiveBitsetGrowth.singleton w.cell.val)) rest = some final := by
        simpa only [propagate, hs, ite_true] using h
      obtain ⟨hc, hf⟩ := ih _ hh
      exact ⟨Bool.and_eq_true_iff.mpr ⟨hs, hc⟩, hf⟩
    · have hs' : stepCheck cache selected blocked w = false := Bool.eq_false_of_ne_true hs
      simp [propagate, hs'] at h

def check (D : Problem n r e v k) (node : Node n r e v k g l t)
    (base : Nat) : Bool :=
  ((node.closed.all (PrimitiveBitsetGrowth.closedCheck D.cache node.mask) &&
      decide (base = blockedMask D.cache D.quota node.cells node.mask node.closed)) &&
    match propagate D.cache node.mask base node.removals with
    | none => false
    | some final =>
        decide (Nat.land (FiniteMaskSets.allMask n)
          (Nat.lor final node.available) = FiniteMaskSets.allMask n))

theorem check_sound (D : Problem n r e v k) (node : Node n r e v k g l t)
    (base : Nat) (h : check D node base = true) : availabilityCheck D node = true := by
  obtain ⟨hlocal, hrun⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hclosed, hbase⟩ := Bool.and_eq_true_iff.mp hlocal
  have hbase := of_decide_eq_true hbase
  have hclosed' : node.closed.all (closedWitnessCheck D.cache node.mask) = true := by
    have hf : PrimitiveBitsetGrowth.closedCheck D.cache node.mask =
        closedWitnessCheck D.cache node.mask :=
      funext (PrimitiveBitsetGrowth.closedCheck_eq D.cache node.mask)
    simpa only [hf] using hclosed
  cases hp : propagate D.cache node.mask base node.removals with
  | none => simp only [hp, Bool.false_eq_true] at hrun
  | some final =>
    obtain ⟨hchecks, hfinal⟩ := propagate_sound D.cache node.mask base node.removals final hp
    apply Bool.and_eq_true_iff.mpr
    refine ⟨Bool.and_eq_true_iff.mpr ⟨hclosed', ?_⟩, ?_⟩
    · simpa only [← hbase] using hchecks
    · change decide (Nat.land (FiniteMaskSets.allMask n)
        (Nat.lor (resultingMask
          (blockedMask D.cache D.quota node.cells node.mask node.closed)
          node.removals) node.available) = FiniteMaskSets.allMask n) = true
      rw [← hbase, hfinal]
      simpa only [hp] using hrun

#print axioms check_sound

end Papers.RationalityTen.FastAvailability
