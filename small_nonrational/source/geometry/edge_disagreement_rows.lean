module
prelude
public import IntersectionIncompatibilityRows

@[expose] public section

/-!
# Shared incompatibility rows from disagreeing induced edges

Compatibility requires equality of the two induced edge lists on the common
vertices. A listed edge on one side and a missing pair on the other therefore
give a sound rejection. The rows are exact global transposes; arbitrary finite
subsets of the rejection terms remain sound.
-/

namespace Papers.RationalityTen.EdgeDisagreementRows

open ConcreteGrowth GrowthBitsets FiniteMaskSets

variable {n : Nat}

structure Rows (cells : Fin n → Cell) where
  edges : Nat → Nat
  pairs : Nat → Nat
  edge_exact : ∀ e c, (edges e).testBit c.val = decide (e ∈ (cells c).edges)
  pair_exact : ∀ e c, (pairs e).testBit c.val =
    decide (Nat.land e (cells c).vertices = e)
  edge_within : ∀ c e, e ∈ (cells c).edges → Nat.land e (cells c).vertices = e

theorem within_common (e a b : Nat) (ha : Nat.land e a = e)
    (hb : Nat.land e b = e) : Nat.land e (Nat.land a b) = e := by
  calc
    Nat.land e (Nat.land a b) = Nat.land (Nat.land e a) b :=
      (Nat.and_assoc e a b).symm
    _ = e := by rw [ha, hb]

theorem compatible_edge_iff (a b : Cell) (e : Nat)
    (ha : Nat.land e a.vertices = e) (hb : Nat.land e b.vertices = e)
    (h : compatible a b = true) : e ∈ a.edges ↔ e ∈ b.edges := by
  have heq : (a.edges.filter fun q => decide (Nat.land q (Nat.land a.vertices b.vertices) = q)) =
      (b.edges.filter fun q => decide (Nat.land q (Nat.land a.vertices b.vertices) = q)) :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
  have hc := within_common e a.vertices b.vertices ha hb
  constructor
  · intro he
    have hm : e ∈ a.edges.filter
        (fun q => decide (Nat.land q (Nat.land a.vertices b.vertices) = q)) :=
      List.mem_filter.mpr ⟨he, decide_eq_true hc⟩
    rw [heq] at hm
    exact (List.mem_filter.mp hm).1
  · intro he
    have hm : e ∈ b.edges.filter
        (fun q => decide (Nat.land q (Nat.land a.vertices b.vertices) = q)) :=
      List.mem_filter.mpr ⟨he, decide_eq_true hc⟩
    rw [← heq] at hm
    exact (List.mem_filter.mp hm).1

/-- Cells containing the pair but omitting this edge. -/
def listedTerm {cells : Fin n → Cell} (R : Rows cells) (e : Nat) : Nat :=
  Nat.land (R.pairs e) (Nat.xor (allMask n) (R.edges e))

theorem listedTerm_sound {cells : Fin n → Cell} (R : Rows cells)
    (a b : Fin n) (e : Nat) (ha : e ∈ (cells a).edges)
    (h : (listedTerm R e).testBit b.val = true) :
    compatible (cells a) (cells b) = false := by
  apply Bool.eq_false_of_ne_true
  intro hcompatible
  rw [listedTerm, testBit_land] at h
  obtain ⟨hpair, hmissing⟩ := Bool.and_eq_true_iff.mp h
  rw [R.pair_exact] at hpair
  have hb := of_decide_eq_true hpair
  have hedge := (compatible_edge_iff (cells a) (cells b) e
    (R.edge_within a e ha) hb hcompatible).mp ha
  rw [IntersectionIncompatibilityRows.testBit_xor, allMask_bit b,
    R.edge_exact, decide_eq_true hedge] at hmissing
  exact Bool.noConfusion hmissing

/-- A pair missing from the first cell cannot be an edge of a compatible cell
when both endpoints belong to the first cell. -/
theorem missingTerm_sound {cells : Fin n → Cell} (R : Rows cells)
    (a b : Fin n) (e : Nat) (ha : Nat.land e (cells a).vertices = e)
    (hmissing : e ∉ (cells a).edges)
    (h : (R.edges e).testBit b.val = true) :
    compatible (cells a) (cells b) = false := by
  apply Bool.eq_false_of_ne_true
  intro hcompatible
  rw [R.edge_exact] at h
  have hb := of_decide_eq_true h
  exact hmissing ((compatible_edge_iff (cells a) (cells b) e ha
    (R.edge_within b e hb) hcompatible).mpr hb)

def incompatibleRow {cells : Fin n → Cell} (R : Rows cells)
    (listed missing : List Nat) : Nat :=
  Nat.lor (unionValues (listedTerm R) listed) (unionValues R.edges missing)

/-- A complete cache may combine this row with the proper-face rejection
row. No completeness of either list of terms is needed for soundness. -/
theorem incompatibleRow_sound {cells : Fin n → Cell} (R : Rows cells)
    (a b : Fin n) (listed missing : List Nat)
    (hlisted : ∀ e, e ∈ listed → e ∈ (cells a).edges)
    (hmissing : ∀ e, e ∈ missing →
      Nat.land e (cells a).vertices = e ∧ e ∉ (cells a).edges)
    (h : bitAt (incompatibleRow R listed missing) b.val = true) :
    compatible (cells a) (cells b) = false := by
  rw [incompatibleRow, bitAt_or, Bool.or_eq_true_iff] at h
  rcases h with h | h
  · obtain ⟨e, he, hterm⟩ := (bitAt_unionValues _ _ _).mp h
    exact listedTerm_sound R a b e (hlisted e he)
      ((bitAt_eq_testBit _ _).symm.trans hterm)
  · obtain ⟨e, he, hterm⟩ := (bitAt_unionValues _ _ _).mp h
    exact missingTerm_sound R a b e (hmissing e he).1 (hmissing e he).2
      ((bitAt_eq_testBit _ _).symm.trans hterm)

#print axioms incompatibleRow_sound

end Papers.RationalityTen.EdgeDisagreementRows
