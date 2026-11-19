module
prelude
public meta import LowerSchemas.FinitePolygonN
public import PolygonN7DAGCandidates
public import PolygonN7DAGPart000
public import PolygonN7DAGPart001
public import PolygonN7DAGPart002
public import PolygonN7DAGPart003
public import PolygonN7DAGPart004
public import PolygonN7DAGPart005
public import PolygonN7DAGPart006
public import PolygonN7DAGPart007
public import PolygonN7DAGPart008
public import PolygonN7DAGPart009
public import PolygonN7DAGPart010
public import PolygonN7DAGPart011
public import PolygonN7DAGPart012
public import PolygonN7DAGPart013
public import PolygonN7DAGPart014
public import PolygonN7DAGPart015
public import PolygonN7DAGPart016
public import PolygonN7DAGPart017
public import PolygonN7DAGPart018
public import PolygonN7DAGPart019
public import PolygonN7DAGPart020
public import PolygonN7DAGPart021
public import PolygonN7DAGPart022
public import PolygonN7DAGPart023
public import PolygonN7DAGPart024
public import PolygonN7DAGPart025
public import PolygonN7DAGPart026
public import PolygonN7DAGPart027
public import PolygonN7DAGPart028
public import PolygonN7DAGPart029
public import PolygonN7DAGPart030
public import PolygonN7DAGPart031
public import PolygonN7DAGPart032
public import PolygonN7DAGPart033
public import PolygonN7DAGPart034
public import PolygonN7DAGPart035
public import PolygonN7DAGPart036
public import PolygonN7DAGPart037
public import PolygonN7DAGPart038
public import PolygonN7DAGPart039
public import PolygonN7DAGPart040
public import PolygonN7DAGPart041
public import PolygonN7DAGPart042
public import PolygonN7DAGPart043
public import PolygonN7DAGPart044

@[expose] public section

namespace Papers.RationalityTen.PolygonGrowth.N7
open Papers.RationalityTen GrowthDAG SparseGrowthDAG GrowthPruning FiniteChecks

cert_nodes_checked_join_3 00000 00512 0 512 256 000 00256 001
cert_nodes_checked_join_3 00768 01280 768 1280 1024 003 01024 004
cert_nodes_checked_join_2 00512 01280 512 1280 768 002 00768
cert_nodes_checked_join_4 00000 01280 0 1280 512 00512
cert_nodes_checked_join_3 01536 02048 1536 2048 1792 006 01792 007
cert_nodes_checked_join_2 01280 02048 1280 2048 1536 005 01536
cert_nodes_checked_join_3 02304 02816 2304 2816 2560 009 02560 010
cert_nodes_checked_join_2 02048 02816 2048 2816 2304 008 02304
cert_nodes_checked_join_4 01280 02816 1280 2816 2048 02048
cert_nodes_checked_join_4 00000 02816 0 2816 1280 01280
cert_nodes_checked_join_3 02816 03328 2816 3328 3072 011 03072 012
cert_nodes_checked_join_3 03584 04096 3584 4096 3840 014 03840 015
cert_nodes_checked_join_2 03328 04096 3328 4096 3584 013 03584
cert_nodes_checked_join_4 02816 04096 2816 4096 3328 03328
cert_nodes_checked_join_3 04352 04864 4352 4864 4608 017 04608 018
cert_nodes_checked_join_2 04096 04864 4096 4864 4352 016 04352
cert_nodes_checked_join_3 05120 05632 5120 5632 5376 020 05376 021
cert_nodes_checked_join_2 04864 05632 4864 5632 5120 019 05120
cert_nodes_checked_join_4 04096 05632 4096 5632 4864 04864
cert_nodes_checked_join_4 02816 05632 2816 5632 4096 04096
cert_nodes_checked_join_4 00000 05632 0 5632 2816 02816
cert_nodes_checked_join_3 05632 06144 5632 6144 5888 022 05888 023
cert_nodes_checked_join_3 06400 06912 6400 6912 6656 025 06656 026
cert_nodes_checked_join_2 06144 06912 6144 6912 6400 024 06400
cert_nodes_checked_join_4 05632 06912 5632 6912 6144 06144
cert_nodes_checked_join_3 07168 07680 7168 7680 7424 028 07424 029
cert_nodes_checked_join_2 06912 07680 6912 7680 7168 027 07168
cert_nodes_checked_join_3 07936 08448 7936 8448 8192 031 08192 032
cert_nodes_checked_join_2 07680 08448 7680 8448 7936 030 07936
cert_nodes_checked_join_4 06912 08448 6912 8448 7680 07680
cert_nodes_checked_join_4 05632 08448 5632 8448 6912 06912
cert_nodes_checked_join_3 08704 09216 8704 9216 8960 034 08960 035
cert_nodes_checked_join_2 08448 09216 8448 9216 8704 033 08704
cert_nodes_checked_join_3 09472 09984 9472 9984 9728 037 09728 038
cert_nodes_checked_join_2 09216 09984 9216 9984 9472 036 09472
cert_nodes_checked_join_4 08448 09984 8448 9984 9216 09216
cert_nodes_checked_join_3 10240 10752 10240 10752 10496 040 10496 041
cert_nodes_checked_join_2 09984 10752 9984 10752 10240 039 10240
cert_nodes_checked_join_3 11008 11426 11008 11426 11264 043 11264 044
cert_nodes_checked_join_2 10752 11426 10752 11426 11008 042 11008
cert_nodes_checked_join_4 09984 11426 9984 11426 10752 10752
cert_nodes_checked_join_4 08448 11426 8448 11426 9984 09984
cert_nodes_checked_join_4 05632 11426 5632 11426 8448 08448
cert_nodes_checked_join_4 00000 11426 0 11426 5632 05632
theorem candidate_coverage (a : Fin 290) :
    (ridgeList a).all (fun q => has (candidates q) a) = true :=
  FiniteChecks.fin_of_interval
    (fun a : Fin 290 => (ridgeList a).all fun q => has (candidates q) a) candidates_checked_join_00000_00290 a

theorem all_nodes_checked : ∀ i,
    WitnessGrowthDAG.nodeCheck ridgeList candidates compatible kind quota terminals nodes i = true :=
  FiniteChecks.fin_of_interval
    (fun i : Fin 11426 => WitnessGrowthDAG.nodeCheck ridgeList candidates compatible kind quota
      terminals nodes i) nodes_checked_join_00000_11426

theorem root_cells : ∀ i, (nodes (roots i)).cells = [0, neighbors i] := by decide +kernel

theorem boundary_classification (B : List (Fin 290))
    (hquota : ∀ j, kindCount kind B j ≤ quota j)
    (hcompatible : ∀ a b, a ∈ B → b ∈ B → a ≠ b → compatible a b = true)
    (hmates : HasMate (fun a => has (ridgeList a)) (family B))
    (hthree : NoThree (fun a => has (ridgeList a)) (family B))
    (hconn : Connected (fun a => has (ridgeList a)) (family B))
    (seed : Fin 4) (hroot : (0 : Fin 290) ∈ B) (hneighbor : neighbors seed ∈ B) :
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
end Papers.RationalityTen.PolygonGrowth.N7
