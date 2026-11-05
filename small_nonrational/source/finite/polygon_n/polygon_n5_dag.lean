module
prelude
public import PolygonN5DAGData

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.PolygonGrowth.N5
open Papers.RationalityTen GrowthDAG SparseGrowthDAG GrowthPruning FiniteChecks

noncomputable def candidateTest (i : Nat) : Bool :=
  let a := Fin.ofNat 16 i
  (ridgeList a).all fun q => has (candidates q) a

noncomputable def nodeTest (i : Nat) : Bool :=
  WitnessGrowthDAG.nodeCheck ridgeList candidates compatible kind quota terminals nodes (Fin.ofNat 20 i)

theorem candidates_checked_00000 : FiniteChecks.Interval candidateTest 0 8 :=
  FiniteChecks.interval_of_check candidateTest 0 8 (by decide +kernel)

theorem candidates_checked_00008 : FiniteChecks.Interval candidateTest 8 16 :=
  FiniteChecks.interval_of_check candidateTest 8 8 (by decide +kernel)

theorem candidates_checked_join_00000_00016 : FiniteChecks.Interval candidateTest 0 16 :=
  FiniteChecks.interval_append candidateTest 0 8 16 candidates_checked_00000 candidates_checked_00008

theorem nodes_checked_00000 : FiniteChecks.Interval nodeTest 0 8 :=
  FiniteChecks.interval_of_check nodeTest 0 8 (by decide +kernel)

theorem nodes_checked_00008 : FiniteChecks.Interval nodeTest 8 16 :=
  FiniteChecks.interval_of_check nodeTest 8 8 (by decide +kernel)

theorem nodes_checked_00016 : FiniteChecks.Interval nodeTest 16 20 :=
  FiniteChecks.interval_of_check nodeTest 16 4 (by decide +kernel)

theorem nodes_checked_join_00008_00020 : FiniteChecks.Interval nodeTest 8 20 :=
  FiniteChecks.interval_append nodeTest 8 16 20 nodes_checked_00008 nodes_checked_00016

theorem nodes_checked_join_00000_00020 : FiniteChecks.Interval nodeTest 0 20 :=
  FiniteChecks.interval_append nodeTest 0 8 20 nodes_checked_00000 nodes_checked_join_00008_00020

theorem candidate_coverage (a : Fin 16) :
    (ridgeList a).all (fun q => has (candidates q) a) = true :=
  FiniteChecks.fin_of_interval
    (fun a : Fin 16 => (ridgeList a).all fun q => has (candidates q) a) candidates_checked_join_00000_00016 a

theorem all_nodes_checked : ∀ i,
    WitnessGrowthDAG.nodeCheck ridgeList candidates compatible kind quota terminals nodes i = true :=
  FiniteChecks.fin_of_interval
    (fun i : Fin 20 => WitnessGrowthDAG.nodeCheck ridgeList candidates compatible kind quota
      terminals nodes i) nodes_checked_join_00000_00020

theorem root_cells : ∀ i, (nodes (roots i)).cells = [0, neighbors i] := by decide +kernel

theorem boundary_classification (B : List (Fin 16))
    (hquota : ∀ j, kindCount kind B j ≤ quota j)
    (hcompatible : ∀ a b, a ∈ B → b ∈ B → a ≠ b → compatible a b = true)
    (hmates : HasMate (fun a => has (ridgeList a)) (family B))
    (hthree : NoThree (fun a => has (ridgeList a)) (family B))
    (hconn : Connected (fun a => has (ridgeList a)) (family B))
    (seed : Fin 2) (hroot : (0 : Fin 16) ∈ B) (hneighbor : neighbors seed ∈ B) :
    ∃ j, Same (family (terminals j)) (family B) := by
  apply WitnessGrowthDAG.complete_of_checks ridgeList candidates compatible kind quota
    terminals nodes candidate_coverage all_nodes_checked
    B hquota hcompatible hmates hthree hconn (roots seed)
  · intro a ha
    have hmem := (has_true _ a).mp ha
    rw [root_cells] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · exact (has_true B _).mpr hroot
    · exact (has_true B _).mpr hneighbor
  · refine ⟨0, ?_⟩
    apply (has_true _ _).mpr
    rw [root_cells]
    exact List.mem_cons_self

#print axioms all_nodes_checked
#print axioms boundary_classification
end Papers.RationalityTen.PolygonGrowth.N5
