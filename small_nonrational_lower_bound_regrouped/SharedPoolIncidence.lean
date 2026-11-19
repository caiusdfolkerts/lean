module
prelude
public import SharedGraphCellPool
public import GraphCandidateCoverage

@[expose] public section
namespace Papers.RationalityTen.SharedPoolIncidence
open SharedGraphCellPool FiniteChecks GrowthBitsets

structure Rows (N : Nat) where
  vertices : Fin 10 → Nat
  edges : Fin 45 → Nat
  kinds : Fin 5 → Nat

structure RowFacts {N : Nat} (pool : Fin N → Entry) (R : Rows N) : Prop where
  vertices : ∀ a c, (R.vertices a).testBit c.val = (pool c).cell.vertices.testBit a.val
  edges : ∀ q c, (R.edges q).testBit c.val = (pool c).edgeMask.testBit q.val
  kinds : ∀ j c, (R.kinds j).testBit c.val = decide ((pool c).cell.kind = j.val)

def cellTest {N : Nat} [NeZero N] (pool : Fin N → Entry) (R : Rows N) (i : Nat) : Bool :=
  let c := Fin.ofNat N i
  ((List.finRange 10).all fun a =>
    decide ((R.vertices a).testBit c.val = (pool c).cell.vertices.testBit a.val)) &&
  (((List.finRange 45).all fun q =>
    decide ((R.edges q).testBit c.val = (pool c).edgeMask.testBit q.val)) &&
   (List.finRange 5).all fun j =>
    decide ((R.kinds j).testBit c.val = decide ((pool c).cell.kind = j.val)))

theorem rows_of_interval {N : Nat} [NeZero N] (pool : Fin N → Entry) (R : Rows N)
    (h : Interval (cellTest pool R) 0 N) : RowFacts pool R := by
  have hc (c : Fin N) := h c.val (Nat.zero_le _) c.isLt
  simp only [cellTest, Fin.ofNat_val_eq_self, Bool.and_eq_true_iff] at hc
  refine ⟨?_, ?_, ?_⟩
  · intro a c
    exact of_decide_eq_true (List.all_eq_true.mp (hc c).1 a (List.mem_finRange a))
  · intro q c
    exact of_decide_eq_true (List.all_eq_true.mp (hc c).2.1 q (List.mem_finRange q))
  · intro j c
    exact of_decide_eq_true (List.all_eq_true.mp (hc c).2.2 j (List.mem_finRange j))

def graphRows {N : Nat} (pool : Fin N → Entry) (R : Rows N) (h : RowFacts pool R) :
    GraphCandidateCoverage.IncidenceRows N 10 45 where
  first := FastTenGraphEdges.first
  second := FastTenGraphEdges.second
  vertices := fun c => (pool c).cell.vertices
  edges := fun c => (pool c).edgeMask
  vertexRows := R.vertices
  edgeRows := R.edges
  vertexRows_exact := h.vertices
  edgeRows_exact := h.edges

def allowedMask {N : Nat} (R : Rows N) (quota : Nat → Nat) : Nat :=
  unionValues (fun j : Fin 5 => if 0 < quota j.val then R.kinds j else 0) (List.finRange 5)

theorem allowedMask_exact {N : Nat} (pool : Fin N → Entry) (R : Rows N)
    (h : RowFacts pool R) (hkind : ∀ c, (pool c).cell.kind < 5)
    (quota : Nat → Nat) (c : Fin N) :
    (allowedMask R quota).testBit c.val = true ↔ 0 < quota (pool c).cell.kind := by
  unfold allowedMask
  rw [← bitAt_eq_testBit, bitAt_unionValues]
  simp only [List.mem_finRange, true_and, bitAt_eq_testBit]
  constructor
  · rintro ⟨j, hj⟩
    by_cases hq : 0 < quota j.val
    · rw [ite_eq_left hq, h.kinds, decide_eq_true_eq] at hj
      simpa only [hj] using hq
    · rw [ite_eq_right hq, Nat.zero_testBit] at hj
      exact False.elim (Bool.noConfusion hj)
  · intro hq
    let j : Fin 5 := ⟨(pool c).cell.kind, hkind c⟩
    refine ⟨j, ?_⟩
    rw [ite_eq_left hq, h.kinds]
    exact decide_eq_true rfl

#print axioms rows_of_interval
#print axioms allowedMask_exact
end Papers.RationalityTen.SharedPoolIncidence
