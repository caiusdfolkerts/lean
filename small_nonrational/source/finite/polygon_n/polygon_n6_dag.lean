module
prelude
public import PolygonN6DAGData

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.PolygonGrowth.N6
open Papers.RationalityTen GrowthDAG SparseGrowthDAG GrowthPruning FiniteChecks

noncomputable def candidateTest (i : Nat) : Bool :=
  let a := Fin.ofNat 65 i
  (ridgeList a).all fun q => has (candidates q) a

noncomputable def nodeTest (i : Nat) : Bool :=
  WitnessGrowthDAG.nodeCheck ridgeList candidates compatible kind quota terminals nodes (Fin.ofNat 289 i)

theorem candidates_checked_00000 : FiniteChecks.Interval candidateTest 0 8 :=
  FiniteChecks.interval_of_check candidateTest 0 8 (by decide +kernel)

theorem candidates_checked_00008 : FiniteChecks.Interval candidateTest 8 16 :=
  FiniteChecks.interval_of_check candidateTest 8 8 (by decide +kernel)

theorem candidates_checked_00016 : FiniteChecks.Interval candidateTest 16 24 :=
  FiniteChecks.interval_of_check candidateTest 16 8 (by decide +kernel)

theorem candidates_checked_00024 : FiniteChecks.Interval candidateTest 24 32 :=
  FiniteChecks.interval_of_check candidateTest 24 8 (by decide +kernel)

theorem candidates_checked_00032 : FiniteChecks.Interval candidateTest 32 40 :=
  FiniteChecks.interval_of_check candidateTest 32 8 (by decide +kernel)

theorem candidates_checked_00040 : FiniteChecks.Interval candidateTest 40 48 :=
  FiniteChecks.interval_of_check candidateTest 40 8 (by decide +kernel)

theorem candidates_checked_00048 : FiniteChecks.Interval candidateTest 48 56 :=
  FiniteChecks.interval_of_check candidateTest 48 8 (by decide +kernel)

theorem candidates_checked_00056 : FiniteChecks.Interval candidateTest 56 64 :=
  FiniteChecks.interval_of_check candidateTest 56 8 (by decide +kernel)

theorem candidates_checked_00064 : FiniteChecks.Interval candidateTest 64 65 :=
  FiniteChecks.interval_of_check candidateTest 64 1 (by decide +kernel)

theorem candidates_checked_join_00000_00016 : FiniteChecks.Interval candidateTest 0 16 :=
  FiniteChecks.interval_append candidateTest 0 8 16 candidates_checked_00000 candidates_checked_00008

theorem candidates_checked_join_00016_00032 : FiniteChecks.Interval candidateTest 16 32 :=
  FiniteChecks.interval_append candidateTest 16 24 32 candidates_checked_00016 candidates_checked_00024

theorem candidates_checked_join_00000_00032 : FiniteChecks.Interval candidateTest 0 32 :=
  FiniteChecks.interval_append candidateTest 0 16 32 candidates_checked_join_00000_00016 candidates_checked_join_00016_00032

theorem candidates_checked_join_00032_00048 : FiniteChecks.Interval candidateTest 32 48 :=
  FiniteChecks.interval_append candidateTest 32 40 48 candidates_checked_00032 candidates_checked_00040

theorem candidates_checked_join_00056_00065 : FiniteChecks.Interval candidateTest 56 65 :=
  FiniteChecks.interval_append candidateTest 56 64 65 candidates_checked_00056 candidates_checked_00064

theorem candidates_checked_join_00048_00065 : FiniteChecks.Interval candidateTest 48 65 :=
  FiniteChecks.interval_append candidateTest 48 56 65 candidates_checked_00048 candidates_checked_join_00056_00065

theorem candidates_checked_join_00032_00065 : FiniteChecks.Interval candidateTest 32 65 :=
  FiniteChecks.interval_append candidateTest 32 48 65 candidates_checked_join_00032_00048 candidates_checked_join_00048_00065

theorem candidates_checked_join_00000_00065 : FiniteChecks.Interval candidateTest 0 65 :=
  FiniteChecks.interval_append candidateTest 0 32 65 candidates_checked_join_00000_00032 candidates_checked_join_00032_00065

theorem nodes_checked_00000 : FiniteChecks.Interval nodeTest 0 8 :=
  FiniteChecks.interval_of_check nodeTest 0 8 (by decide +kernel)

theorem nodes_checked_00008 : FiniteChecks.Interval nodeTest 8 16 :=
  FiniteChecks.interval_of_check nodeTest 8 8 (by decide +kernel)

theorem nodes_checked_00016 : FiniteChecks.Interval nodeTest 16 24 :=
  FiniteChecks.interval_of_check nodeTest 16 8 (by decide +kernel)

theorem nodes_checked_00024 : FiniteChecks.Interval nodeTest 24 32 :=
  FiniteChecks.interval_of_check nodeTest 24 8 (by decide +kernel)

theorem nodes_checked_00032 : FiniteChecks.Interval nodeTest 32 40 :=
  FiniteChecks.interval_of_check nodeTest 32 8 (by decide +kernel)

theorem nodes_checked_00040 : FiniteChecks.Interval nodeTest 40 48 :=
  FiniteChecks.interval_of_check nodeTest 40 8 (by decide +kernel)

theorem nodes_checked_00048 : FiniteChecks.Interval nodeTest 48 56 :=
  FiniteChecks.interval_of_check nodeTest 48 8 (by decide +kernel)

theorem nodes_checked_00056 : FiniteChecks.Interval nodeTest 56 64 :=
  FiniteChecks.interval_of_check nodeTest 56 8 (by decide +kernel)

theorem nodes_checked_00064 : FiniteChecks.Interval nodeTest 64 72 :=
  FiniteChecks.interval_of_check nodeTest 64 8 (by decide +kernel)

theorem nodes_checked_00072 : FiniteChecks.Interval nodeTest 72 80 :=
  FiniteChecks.interval_of_check nodeTest 72 8 (by decide +kernel)

theorem nodes_checked_00080 : FiniteChecks.Interval nodeTest 80 88 :=
  FiniteChecks.interval_of_check nodeTest 80 8 (by decide +kernel)

theorem nodes_checked_00088 : FiniteChecks.Interval nodeTest 88 96 :=
  FiniteChecks.interval_of_check nodeTest 88 8 (by decide +kernel)

theorem nodes_checked_00096 : FiniteChecks.Interval nodeTest 96 104 :=
  FiniteChecks.interval_of_check nodeTest 96 8 (by decide +kernel)

theorem nodes_checked_00104 : FiniteChecks.Interval nodeTest 104 112 :=
  FiniteChecks.interval_of_check nodeTest 104 8 (by decide +kernel)

theorem nodes_checked_00112 : FiniteChecks.Interval nodeTest 112 120 :=
  FiniteChecks.interval_of_check nodeTest 112 8 (by decide +kernel)

theorem nodes_checked_00120 : FiniteChecks.Interval nodeTest 120 128 :=
  FiniteChecks.interval_of_check nodeTest 120 8 (by decide +kernel)

theorem nodes_checked_00128 : FiniteChecks.Interval nodeTest 128 136 :=
  FiniteChecks.interval_of_check nodeTest 128 8 (by decide +kernel)

theorem nodes_checked_00136 : FiniteChecks.Interval nodeTest 136 144 :=
  FiniteChecks.interval_of_check nodeTest 136 8 (by decide +kernel)

theorem nodes_checked_00144 : FiniteChecks.Interval nodeTest 144 152 :=
  FiniteChecks.interval_of_check nodeTest 144 8 (by decide +kernel)

theorem nodes_checked_00152 : FiniteChecks.Interval nodeTest 152 160 :=
  FiniteChecks.interval_of_check nodeTest 152 8 (by decide +kernel)

theorem nodes_checked_00160 : FiniteChecks.Interval nodeTest 160 168 :=
  FiniteChecks.interval_of_check nodeTest 160 8 (by decide +kernel)

theorem nodes_checked_00168 : FiniteChecks.Interval nodeTest 168 176 :=
  FiniteChecks.interval_of_check nodeTest 168 8 (by decide +kernel)

theorem nodes_checked_00176 : FiniteChecks.Interval nodeTest 176 184 :=
  FiniteChecks.interval_of_check nodeTest 176 8 (by decide +kernel)

theorem nodes_checked_00184 : FiniteChecks.Interval nodeTest 184 192 :=
  FiniteChecks.interval_of_check nodeTest 184 8 (by decide +kernel)

theorem nodes_checked_00192 : FiniteChecks.Interval nodeTest 192 200 :=
  FiniteChecks.interval_of_check nodeTest 192 8 (by decide +kernel)

theorem nodes_checked_00200 : FiniteChecks.Interval nodeTest 200 208 :=
  FiniteChecks.interval_of_check nodeTest 200 8 (by decide +kernel)

theorem nodes_checked_00208 : FiniteChecks.Interval nodeTest 208 216 :=
  FiniteChecks.interval_of_check nodeTest 208 8 (by decide +kernel)

theorem nodes_checked_00216 : FiniteChecks.Interval nodeTest 216 224 :=
  FiniteChecks.interval_of_check nodeTest 216 8 (by decide +kernel)

theorem nodes_checked_00224 : FiniteChecks.Interval nodeTest 224 232 :=
  FiniteChecks.interval_of_check nodeTest 224 8 (by decide +kernel)

theorem nodes_checked_00232 : FiniteChecks.Interval nodeTest 232 240 :=
  FiniteChecks.interval_of_check nodeTest 232 8 (by decide +kernel)

theorem nodes_checked_00240 : FiniteChecks.Interval nodeTest 240 248 :=
  FiniteChecks.interval_of_check nodeTest 240 8 (by decide +kernel)

theorem nodes_checked_00248 : FiniteChecks.Interval nodeTest 248 256 :=
  FiniteChecks.interval_of_check nodeTest 248 8 (by decide +kernel)

theorem nodes_checked_00256 : FiniteChecks.Interval nodeTest 256 264 :=
  FiniteChecks.interval_of_check nodeTest 256 8 (by decide +kernel)

theorem nodes_checked_00264 : FiniteChecks.Interval nodeTest 264 272 :=
  FiniteChecks.interval_of_check nodeTest 264 8 (by decide +kernel)

theorem nodes_checked_00272 : FiniteChecks.Interval nodeTest 272 280 :=
  FiniteChecks.interval_of_check nodeTest 272 8 (by decide +kernel)

theorem nodes_checked_00280 : FiniteChecks.Interval nodeTest 280 288 :=
  FiniteChecks.interval_of_check nodeTest 280 8 (by decide +kernel)

theorem nodes_checked_00288 : FiniteChecks.Interval nodeTest 288 289 :=
  FiniteChecks.interval_of_check nodeTest 288 1 (by decide +kernel)

theorem nodes_checked_join_00000_00016 : FiniteChecks.Interval nodeTest 0 16 :=
  FiniteChecks.interval_append nodeTest 0 8 16 nodes_checked_00000 nodes_checked_00008

theorem nodes_checked_join_00016_00032 : FiniteChecks.Interval nodeTest 16 32 :=
  FiniteChecks.interval_append nodeTest 16 24 32 nodes_checked_00016 nodes_checked_00024

theorem nodes_checked_join_00000_00032 : FiniteChecks.Interval nodeTest 0 32 :=
  FiniteChecks.interval_append nodeTest 0 16 32 nodes_checked_join_00000_00016 nodes_checked_join_00016_00032

theorem nodes_checked_join_00032_00048 : FiniteChecks.Interval nodeTest 32 48 :=
  FiniteChecks.interval_append nodeTest 32 40 48 nodes_checked_00032 nodes_checked_00040

theorem nodes_checked_join_00056_00072 : FiniteChecks.Interval nodeTest 56 72 :=
  FiniteChecks.interval_append nodeTest 56 64 72 nodes_checked_00056 nodes_checked_00064

theorem nodes_checked_join_00048_00072 : FiniteChecks.Interval nodeTest 48 72 :=
  FiniteChecks.interval_append nodeTest 48 56 72 nodes_checked_00048 nodes_checked_join_00056_00072

theorem nodes_checked_join_00032_00072 : FiniteChecks.Interval nodeTest 32 72 :=
  FiniteChecks.interval_append nodeTest 32 48 72 nodes_checked_join_00032_00048 nodes_checked_join_00048_00072

theorem nodes_checked_join_00000_00072 : FiniteChecks.Interval nodeTest 0 72 :=
  FiniteChecks.interval_append nodeTest 0 32 72 nodes_checked_join_00000_00032 nodes_checked_join_00032_00072

theorem nodes_checked_join_00072_00088 : FiniteChecks.Interval nodeTest 72 88 :=
  FiniteChecks.interval_append nodeTest 72 80 88 nodes_checked_00072 nodes_checked_00080

theorem nodes_checked_join_00088_00104 : FiniteChecks.Interval nodeTest 88 104 :=
  FiniteChecks.interval_append nodeTest 88 96 104 nodes_checked_00088 nodes_checked_00096

theorem nodes_checked_join_00072_00104 : FiniteChecks.Interval nodeTest 72 104 :=
  FiniteChecks.interval_append nodeTest 72 88 104 nodes_checked_join_00072_00088 nodes_checked_join_00088_00104

theorem nodes_checked_join_00104_00120 : FiniteChecks.Interval nodeTest 104 120 :=
  FiniteChecks.interval_append nodeTest 104 112 120 nodes_checked_00104 nodes_checked_00112

theorem nodes_checked_join_00128_00144 : FiniteChecks.Interval nodeTest 128 144 :=
  FiniteChecks.interval_append nodeTest 128 136 144 nodes_checked_00128 nodes_checked_00136

theorem nodes_checked_join_00120_00144 : FiniteChecks.Interval nodeTest 120 144 :=
  FiniteChecks.interval_append nodeTest 120 128 144 nodes_checked_00120 nodes_checked_join_00128_00144

theorem nodes_checked_join_00104_00144 : FiniteChecks.Interval nodeTest 104 144 :=
  FiniteChecks.interval_append nodeTest 104 120 144 nodes_checked_join_00104_00120 nodes_checked_join_00120_00144

theorem nodes_checked_join_00072_00144 : FiniteChecks.Interval nodeTest 72 144 :=
  FiniteChecks.interval_append nodeTest 72 104 144 nodes_checked_join_00072_00104 nodes_checked_join_00104_00144

theorem nodes_checked_join_00000_00144 : FiniteChecks.Interval nodeTest 0 144 :=
  FiniteChecks.interval_append nodeTest 0 72 144 nodes_checked_join_00000_00072 nodes_checked_join_00072_00144

theorem nodes_checked_join_00144_00160 : FiniteChecks.Interval nodeTest 144 160 :=
  FiniteChecks.interval_append nodeTest 144 152 160 nodes_checked_00144 nodes_checked_00152

theorem nodes_checked_join_00160_00176 : FiniteChecks.Interval nodeTest 160 176 :=
  FiniteChecks.interval_append nodeTest 160 168 176 nodes_checked_00160 nodes_checked_00168

theorem nodes_checked_join_00144_00176 : FiniteChecks.Interval nodeTest 144 176 :=
  FiniteChecks.interval_append nodeTest 144 160 176 nodes_checked_join_00144_00160 nodes_checked_join_00160_00176

theorem nodes_checked_join_00176_00192 : FiniteChecks.Interval nodeTest 176 192 :=
  FiniteChecks.interval_append nodeTest 176 184 192 nodes_checked_00176 nodes_checked_00184

theorem nodes_checked_join_00200_00216 : FiniteChecks.Interval nodeTest 200 216 :=
  FiniteChecks.interval_append nodeTest 200 208 216 nodes_checked_00200 nodes_checked_00208

theorem nodes_checked_join_00192_00216 : FiniteChecks.Interval nodeTest 192 216 :=
  FiniteChecks.interval_append nodeTest 192 200 216 nodes_checked_00192 nodes_checked_join_00200_00216

theorem nodes_checked_join_00176_00216 : FiniteChecks.Interval nodeTest 176 216 :=
  FiniteChecks.interval_append nodeTest 176 192 216 nodes_checked_join_00176_00192 nodes_checked_join_00192_00216

theorem nodes_checked_join_00144_00216 : FiniteChecks.Interval nodeTest 144 216 :=
  FiniteChecks.interval_append nodeTest 144 176 216 nodes_checked_join_00144_00176 nodes_checked_join_00176_00216

theorem nodes_checked_join_00216_00232 : FiniteChecks.Interval nodeTest 216 232 :=
  FiniteChecks.interval_append nodeTest 216 224 232 nodes_checked_00216 nodes_checked_00224

theorem nodes_checked_join_00240_00256 : FiniteChecks.Interval nodeTest 240 256 :=
  FiniteChecks.interval_append nodeTest 240 248 256 nodes_checked_00240 nodes_checked_00248

theorem nodes_checked_join_00232_00256 : FiniteChecks.Interval nodeTest 232 256 :=
  FiniteChecks.interval_append nodeTest 232 240 256 nodes_checked_00232 nodes_checked_join_00240_00256

theorem nodes_checked_join_00216_00256 : FiniteChecks.Interval nodeTest 216 256 :=
  FiniteChecks.interval_append nodeTest 216 232 256 nodes_checked_join_00216_00232 nodes_checked_join_00232_00256

theorem nodes_checked_join_00256_00272 : FiniteChecks.Interval nodeTest 256 272 :=
  FiniteChecks.interval_append nodeTest 256 264 272 nodes_checked_00256 nodes_checked_00264

theorem nodes_checked_join_00280_00289 : FiniteChecks.Interval nodeTest 280 289 :=
  FiniteChecks.interval_append nodeTest 280 288 289 nodes_checked_00280 nodes_checked_00288

theorem nodes_checked_join_00272_00289 : FiniteChecks.Interval nodeTest 272 289 :=
  FiniteChecks.interval_append nodeTest 272 280 289 nodes_checked_00272 nodes_checked_join_00280_00289

theorem nodes_checked_join_00256_00289 : FiniteChecks.Interval nodeTest 256 289 :=
  FiniteChecks.interval_append nodeTest 256 272 289 nodes_checked_join_00256_00272 nodes_checked_join_00272_00289

theorem nodes_checked_join_00216_00289 : FiniteChecks.Interval nodeTest 216 289 :=
  FiniteChecks.interval_append nodeTest 216 256 289 nodes_checked_join_00216_00256 nodes_checked_join_00256_00289

theorem nodes_checked_join_00144_00289 : FiniteChecks.Interval nodeTest 144 289 :=
  FiniteChecks.interval_append nodeTest 144 216 289 nodes_checked_join_00144_00216 nodes_checked_join_00216_00289

theorem nodes_checked_join_00000_00289 : FiniteChecks.Interval nodeTest 0 289 :=
  FiniteChecks.interval_append nodeTest 0 144 289 nodes_checked_join_00000_00144 nodes_checked_join_00144_00289

theorem candidate_coverage (a : Fin 65) :
    (ridgeList a).all (fun q => has (candidates q) a) = true :=
  FiniteChecks.fin_of_interval
    (fun a : Fin 65 => (ridgeList a).all fun q => has (candidates q) a) candidates_checked_join_00000_00065 a

theorem all_nodes_checked : ∀ i,
    WitnessGrowthDAG.nodeCheck ridgeList candidates compatible kind quota terminals nodes i = true :=
  FiniteChecks.fin_of_interval
    (fun i : Fin 289 => WitnessGrowthDAG.nodeCheck ridgeList candidates compatible kind quota
      terminals nodes i) nodes_checked_join_00000_00289

theorem root_cells : ∀ i, (nodes (roots i)).cells = [0, neighbors i] := by decide +kernel

theorem boundary_classification (B : List (Fin 65))
    (hquota : ∀ j, kindCount kind B j ≤ quota j)
    (hcompatible : ∀ a b, a ∈ B → b ∈ B → a ≠ b → compatible a b = true)
    (hmates : HasMate (fun a => has (ridgeList a)) (family B))
    (hthree : NoThree (fun a => has (ridgeList a)) (family B))
    (hconn : Connected (fun a => has (ridgeList a)) (family B))
    (seed : Fin 3) (hroot : (0 : Fin 65) ∈ B) (hneighbor : neighbors seed ∈ B) :
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
end Papers.RationalityTen.PolygonGrowth.N6
