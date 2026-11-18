module
prelude
public import SharedSmallGraphCellsChecked
public import SharedSmallGraphRidgesChecked
public import SharedSmallGraphWithinChecked

@[expose] public section
namespace Papers.RationalityTen.SharedSmallGraph
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming GrowthBitsets
open BatchedGrowthPruning GraphGrowthConstraints FiniteChecks

theorem kind_lt (c : Fin cellCount) : (cells c).kind < 5 := by
  have h := cells_checked c
  simp only [cellCheck, Bool.and_eq_true_iff] at h
  exact of_decide_eq_true h.1

theorem ridge_coverage (c : Fin cellCount) :
    (ridgeList cells c).all (fun q => (candidateRows q).testBit c.val) = true := by
  have h := cells_checked c
  simp only [cellCheck, Bool.and_eq_true_iff] at h
  exact h.2.1

theorem edge_mask_eq (c : Fin cellCount) :
    edgeMask c = PrimitiveBitsetGrowth.mask (edgeIndices c) := by
  have h := cells_checked c
  simp only [cellCheck, Bool.and_eq_true_iff] at h
  exact of_decide_eq_true h.2.2.1

theorem edge_indices_map (c : Fin cellCount) :
    (edgeIndices c).map fastEdgeMask = (cells c).edges := by
  have h := cells_checked c
  simp only [cellCheck, Bool.and_eq_true_iff] at h
  exact of_decide_eq_true h.2.2.2.1

theorem vertex_rows_exact (v : Fin 10) (c : Fin cellCount) :
    (vertexRows v).testBit c.val = (cells c).vertices.testBit v.val := by
  have h := cells_checked c
  simp only [cellCheck, Bool.and_eq_true_iff] at h
  exact of_decide_eq_true
    (List.all_eq_true.mp h.2.2.2.2.1 v (List.mem_finRange v))

theorem kind_rows_exact (j : Fin 5) (c : Fin cellCount) :
    (kindRows j.val).testBit c.val = decide ((cells c).kind = j.val) := by
  have h := cells_checked c
  simp only [cellCheck, Bool.and_eq_true_iff] at h
  exact of_decide_eq_true
    (List.all_eq_true.mp h.2.2.2.2.2.1 j (List.mem_finRange j))

theorem edge_rows_exact (q : Fin 45) (c : Fin cellCount) :
    (edgeRows q).testBit c.val = (edgeMask c).testBit q.val := by
  have h := cells_checked c
  simp only [cellCheck, Bool.and_eq_true_iff] at h
  exact of_decide_eq_true
    (List.all_eq_true.mp h.2.2.2.2.2.2.1 q (List.mem_finRange q))

theorem missing_rows_exact (q : Fin 45) (c : Fin cellCount) :
    (missingRows q).testBit c.val = (missingMask c).testBit q.val := by
  have h := cells_checked c
  simp only [cellCheck, Bool.and_eq_true_iff] at h
  exact of_decide_eq_true
    (List.all_eq_true.mp h.2.2.2.2.2.2.2.1 q (List.mem_finRange q))

theorem missing_mask_eq (c : Fin cellCount) :
    missingMask c = Nat.land (withinMask (cells c).vertices)
      (Nat.xor (FiniteMaskSets.allMask 45) (edgeMask c)) := by
  have h := cells_checked c
  simp only [cellCheck, Bool.and_eq_true_iff] at h
  exact of_decide_eq_true h.2.2.2.2.2.2.2.2.1

theorem edge_within (c : Fin cellCount) :
    Nat.land (edgeMask c) (withinMask (cells c).vertices) = edgeMask c := by
  have h := cells_checked c
  simp only [cellCheck, Bool.and_eq_true_iff] at h
  exact of_decide_eq_true h.2.2.2.2.2.2.2.2.2.1

theorem vertices_lt (c : Fin cellCount) : (cells c).vertices < 1024 := by
  have h := cells_checked c
  simp only [cellCheck, Bool.and_eq_true_iff] at h
  exact of_decide_eq_true h.2.2.2.2.2.2.2.2.2.2

theorem candidate_rows_exact (q : Fin 1024) (c : Fin cellCount) :
    bitAt (candidateRows q) c.val = has (ridgeList cells c) q :=
  candidate_exact_of_bits (ridgeList cells) candidateSupports candidateRows
    (fun q => of_decide_eq_true (Bool.and_eq_true_iff.mp (ridges_checked q)).1)
    ridge_coverage
    (fun q => (Bool.and_eq_true_iff.mp (ridges_checked q)).2) q c

theorem within_mask_exact (v : Fin 1024) (q : Fin 45) :
    (withinMask v.val).testBit q.val =
      (v.val.testBit (FastTenGraphEdges.first q).val &&
       v.val.testBit (FastTenGraphEdges.second q).val) :=
  of_decide_eq_true
    (List.all_eq_true.mp (within_checked v) q (List.mem_finRange q))

/-- Shared cache: every row is checked once against the full literal universe.
No incompatibility exclusions are required by the empty-root certificates. -/
noncomputable def cache :
    Cache (ridgeList cells) (fun a b => compatible (cells a) (cells b))
      (fun c => (cells c).kind) where
  candidates := candidateRows
  incompatible := fun _ => 0
  kinds := kindRows
  keys := List.range 5
  candidates_exact := candidate_rows_exact
  incompatible_sound := by
    intro a c h
    simp only [bitAt_zero] at h
    exact False.elim (Bool.noConfusion h)
  kind_sound := by
    intro j hj c h
    have hjlt : j < 5 := List.mem_range.mp hj
    have hrow := kind_rows_exact ⟨j,hjlt⟩ c
    apply of_decide_eq_true
    rw [← hrow]
    simpa only [bitAt_eq_testBit] using h

/-- Only the exact numerical budgets vary with a residual row and its graph. -/
noncomputable def problem (quota : Nat → Nat) (required missingCount : Nat) :
    Problem cellCount 1024 45 10 5 where
  ridgeList := ridgeList cells
  compatible := fun a b => compatible (cells a) (cells b)
  kind := fun c => (cells c).kind
  quota := quota
  cache := cache
  kind_lt := kind_lt
  kind_exact := kind_rows_exact
  vertexRows := vertexRows
  edges := edgeMask
  missing := missingMask
  edgeRows := edgeRows
  missingRows := missingRows
  edgeRows_exact := edge_rows_exact
  missingRows_exact := missing_rows_exact
  requiredEdges := required
  missingCount := missingCount
  minimumIncidence := 5

noncomputable def graphRows :
    GraphCandidateCoverage.IncidenceRows cellCount 10 45 where
  first := FastTenGraphEdges.first
  second := FastTenGraphEdges.second
  vertices := fun c => (cells c).vertices
  edges := edgeMask
  vertexRows := vertexRows
  edgeRows := edgeRows
  vertexRows_exact := vertex_rows_exact
  edgeRows_exact := edge_rows_exact

def requiredMask (complement : Nat) : Nat :=
  Nat.xor (FiniteMaskSets.allMask 45) complement

noncomputable def allowedMask (quota : Nat → Nat) : Nat :=
  unionValues
    (fun j : Fin 5 => if 0 < quota j.val then kindRows j.val else 0)
    (List.finRange 5)

#print axioms problem
#print axioms graphRows
end Papers.RationalityTen.SharedSmallGraph
