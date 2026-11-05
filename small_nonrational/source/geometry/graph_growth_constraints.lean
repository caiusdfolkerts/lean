module
prelude
public import FiniteMaskSets
public import UnsupportedRidgePruning
public import PrimitiveBitsetGrowth

@[expose] public section

/-!
# Necessary conditions for growth inside a fixed graph

The underlying boundary conditions are unchanged.  The additional data record
the exact kind quotas, the graph edges that a complete boundary must cover,
the number of internal nonedges, and the minimum vertex-facet incidence.
All cardinalities below have explicit finite ranges.
-/

namespace Papers.RationalityTen.GraphGrowthConstraints

open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming ConcreteGrowth
open GrowthBitsets BatchedGrowthPruning UnsupportedRidgePruning

variable {n r e v k : Nat}

structure Problem (n r e v k : Nat) where
  ridgeList : Fin n → List (Fin r)
  compatible : Fin n → Fin n → Bool
  kind : Fin n → Nat
  quota : Nat → Nat
  cache : Cache ridgeList compatible kind
  kind_lt : ∀ c, kind c < k
  kind_exact : ∀ j : Fin k, ∀ c,
    (cache.kinds j.val).testBit c.val = decide (kind c = j.val)
  vertexRows : Fin v → Nat
  edges : Fin n → Nat
  missing : Fin n → Nat
  edgeRows : Fin e → Nat
  missingRows : Fin e → Nat
  edgeRows_exact : ∀ q c, (edgeRows q).testBit c.val = (edges c).testBit q.val
  missingRows_exact : ∀ q c,
    (missingRows q).testBit c.val = (missing c).testBit q.val
  requiredEdges : Nat
  missingCount : Nat
  minimumIncidence : Nat

def vertexCount (D : Problem n r e v k) (B : List (Fin n)) (a : Fin v) : Nat :=
  (B.filter fun c => (D.vertexRows a).testBit c.val).length

def edgeUnion (D : Problem n r e v k) (B : List (Fin n)) : Nat :=
  unionValues D.edges B

def missingUnion (D : Problem n r e v k) (B : List (Fin n)) : Nat :=
  unionValues D.missing B

structure Target (D : Problem n r e v k) (B : List (Fin n)) : Prop where
  boundary : GrowthRenaming.Target (fun c => has (D.ridgeList c))
    D.compatible D.kind D.quota B
  nodup : B.Nodup
  exactQuota : ∀ j : Fin k, kindCount D.kind B j.val = D.quota j.val
  incidence : ∀ a, D.minimumIncidence ≤ vertexCount D B a
  edgeCover : ∀ q : Fin e, D.requiredEdges.testBit q.val = true →
    (edgeUnion D B).testBit q.val = true
  missingCard : FiniteMaskSets.card e (missingUnion D B) = D.missingCount

structure Renaming (D : Problem n r e v k) where
  boundary : GrowthRenaming.Renaming (fun c => has (D.ridgeList c))
    D.compatible D.kind
  vertices : Bijection (Fin v)
  features : Bijection (Fin e)
  vertex_incidence : ∀ a c,
    (D.vertexRows (vertices.forward a)).testBit (boundary.cells.forward c).val =
      (D.vertexRows a).testBit c.val
  edge_incidence : ∀ c q,
    (D.edges (boundary.cells.forward c)).testBit (features.forward q).val =
      (D.edges c).testBit q.val
  missing_incidence : ∀ c q,
    (D.missing (boundary.cells.forward c)).testBit (features.forward q).val =
      (D.missing c).testBit q.val
  required_preserved : ∀ q,
    D.requiredEdges.testBit (features.forward q).val = D.requiredEdges.testBit q.val

theorem unionValues_map_bit (features : Fin n → Nat)
    (p : Bijection (Fin n)) (q : Bijection (Fin e))
    (h : ∀ c i, (features (p.forward c)).testBit (q.forward i).val =
      (features c).testBit i.val) (B : List (Fin n)) (i : Fin e) :
    (unionValues features (B.map p.forward)).testBit (q.forward i).val =
      (unionValues features B).testBit i.val := by
  apply Bool.eq_iff_iff.mpr
  simp only [← bitAt_eq_testBit, bitAt_unionValues]
  constructor
  · rintro ⟨c, hc, hi⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    refine ⟨a, ha, ?_⟩
    simpa only [bitAt_eq_testBit, h] using hi
  · rintro ⟨c, hc, hi⟩
    refine ⟨p.forward c, List.mem_map.mpr ⟨c, hc, rfl⟩, ?_⟩
    simpa only [bitAt_eq_testBit, h] using hi

theorem vertexCount_map (D : Problem n r e v k) (p : Renaming D)
    (B : List (Fin n)) (a : Fin v) :
    vertexCount D (B.map p.boundary.cells.forward) (p.vertices.forward a) =
      vertexCount D B a := by
  simp only [vertexCount, List.filter_map, Function.comp_def,
    p.vertex_incidence, List.length_map]

theorem Target.rename {D : Problem n r e v k} {B : List (Fin n)}
    (h : Target D B) (p : Renaming D) :
    Target D (B.map p.boundary.cells.forward) := by
  refine ⟨h.boundary.rename p.boundary,
    List.Pairwise.map p.boundary.cells.forward
      (fun _ _ hne heq => hne (p.boundary.cells.injective heq)) h.nodup, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [kindCount_map]
    exact h.exactQuota j
  · intro a
    rw [← p.vertices.right_inverse a, vertexCount_map]
    exact h.incidence (p.vertices.inverse a)
  · intro q hq
    have hh := unionValues_map_bit D.edges p.boundary.cells p.features
      p.edge_incidence B (p.features.inverse q)
    rw [p.features.right_inverse] at hh
    rw [edgeUnion, hh]
    apply h.edgeCover
    have hp := p.required_preserved (p.features.inverse q)
    rw [p.features.right_inverse] at hp
    exact hp.symm.trans hq
  · rw [missingUnion,
      FiniteMaskSets.card_bijection p.features
        (unionValues_map_bit D.missing p.boundary.cells p.features
          p.missing_incidence B)]
    exact h.missingCard

/-- Every missing target cell must be represented by the available mask.
The mask may overestimate availability; that only weakens the pruning. -/
def Available (S B : List (Fin n)) (available : Nat) : Prop :=
  ∀ c, c ∈ B → c ∉ S → available.testBit c.val = true

def possibleMissingCheck (D : Problem n r e v k)
    (S : List (Fin n)) (available possible : Nat) : Bool :=
  decide (Nat.land (missingUnion D S) possible = missingUnion D S) &&
    (List.finRange e).all fun q => possible.testBit q.val ||
      decide (Nat.land available (D.missingRows q) = 0)

theorem possibleMissingCheck_sound (D : Problem n r e v k)
    (S B : List (Fin n)) (available possible : Nat)
    (havailable : Available S B available)
    (hcheck : possibleMissingCheck D S available possible = true) :
    ∀ q : Fin e, (missingUnion D B).testBit q.val = true →
      possible.testBit q.val = true := by
  obtain ⟨hselected, hfeatures⟩ := Bool.and_eq_true_iff.mp hcheck
  intro q hq
  obtain ⟨c, hc, hcq⟩ := (bitAt_unionValues D.missing B q.val).mp
    (by simpa only [missingUnion, bitAt_eq_testBit] using hq)
  by_cases hcS : c ∈ S
  · have hs : (missingUnion D S).testBit q.val = true := by
      exact (bitAt_eq_testBit _ _).symm.trans
        ((bitAt_unionValues D.missing S q.val).mpr ⟨c, hcS, hcq⟩)
    have hh := congrArg (fun bits => bits.testBit q.val) (of_decide_eq_true hselected)
    simpa only [FiniteMaskSets.testBit_land, hs, Bool.true_and] using hh
  · have hrow := List.all_eq_true.mp hfeatures q (List.mem_finRange q)
    rcases Bool.or_eq_true_iff.mp hrow with hp | hz
    · exact hp
    · have hzero := congrArg (fun bits => bits.testBit c.val) (of_decide_eq_true hz)
      have ha := havailable c hc hcS
      have hcq' : (D.missing c).testBit q.val = true :=
        (bitAt_eq_testBit _ _).symm.trans hcq
      simp only [FiniteMaskSets.testBit_land, D.missingRows_exact, ha, hcq', Bool.true_and,
        Nat.zero_testBit] at hzero
      exact False.elim (Bool.noConfusion hzero)

def vertexUpper (D : Problem n r e v k) (S : List (Fin n))
    (available : Nat) (a : Fin v) : Nat :=
  vertexCount D S a + ((List.finRange k).map fun j =>
    min (D.quota j.val - kindCount D.kind S j.val)
      (FiniteMaskSets.card n
        (Nat.land available (Nat.land (D.cache.kinds j.val) (D.vertexRows a))))).sum

inductive Rule (r e v k : Nat) where
  | ridge (face : Fin r) (owner : Nat)
  | edge (feature : Fin e)
  | nonedge (feature : Fin e) (possible : Nat)
  | kindCapacity (kind : Fin k)
  | vertexCapacity (vertex : Fin v)
  | nonedgeCapacity (possible : Nat)

def candidates (D : Problem n r e v k) : Rule r e v k → Nat
  | .ridge q _ => D.cache.candidates q
  | .edge q => D.edgeRows q
  | .nonedge q _ => D.missingRows q
  | .kindCapacity _ | .vertexCapacity _ | .nonedgeCapacity _ => 0

def ruleCheck (D : Problem n r e v k) (S : List (Fin n))
    (selected available : Nat) : Rule r e v k → Bool
  | .ridge q owner => decide (owner < n) &&
      decide (Nat.land selected (D.cache.candidates q) = Nat.shiftLeft 1 owner)
  | .edge q => D.requiredEdges.testBit q.val && !(edgeUnion D S).testBit q.val
  | .nonedge q possible => possibleMissingCheck D S available possible &&
      (decide (FiniteMaskSets.card e possible = D.missingCount) &&
        (possible.testBit q.val && !(missingUnion D S).testBit q.val))
  | .kindCapacity j => decide (kindCount D.kind S j.val +
      FiniteMaskSets.card n (Nat.land available (D.cache.kinds j.val)) < D.quota j.val)
  | .vertexCapacity a => decide (vertexUpper D S available a < D.minimumIncidence)
  | .nonedgeCapacity possible => possibleMissingCheck D S available possible &&
      (decide (D.missingCount < FiniteMaskSets.card e (missingUnion D S)) ||
        decide (FiniteMaskSets.card e possible < D.missingCount))

#print axioms Target.rename
#print axioms possibleMissingCheck_sound

end Papers.RationalityTen.GraphGrowthConstraints
