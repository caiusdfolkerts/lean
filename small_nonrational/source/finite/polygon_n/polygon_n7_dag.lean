module
prelude
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

theorem nodes_checked_join_00000_00512 : FiniteChecks.Interval nodeTest 0 512 :=
  FiniteChecks.interval_append nodeTest 0 256 512 nodes_part000_join_00000_00256 nodes_part001_join_00256_00512

theorem nodes_checked_join_00768_01280 : FiniteChecks.Interval nodeTest 768 1280 :=
  FiniteChecks.interval_append nodeTest 768 1024 1280 nodes_part003_join_00768_01024 nodes_part004_join_01024_01280

theorem nodes_checked_join_00512_01280 : FiniteChecks.Interval nodeTest 512 1280 :=
  FiniteChecks.interval_append nodeTest 512 768 1280 nodes_part002_join_00512_00768 nodes_checked_join_00768_01280

theorem nodes_checked_join_00000_01280 : FiniteChecks.Interval nodeTest 0 1280 :=
  FiniteChecks.interval_append nodeTest 0 512 1280 nodes_checked_join_00000_00512 nodes_checked_join_00512_01280

theorem nodes_checked_join_01536_02048 : FiniteChecks.Interval nodeTest 1536 2048 :=
  FiniteChecks.interval_append nodeTest 1536 1792 2048 nodes_part006_join_01536_01792 nodes_part007_join_01792_02048

theorem nodes_checked_join_01280_02048 : FiniteChecks.Interval nodeTest 1280 2048 :=
  FiniteChecks.interval_append nodeTest 1280 1536 2048 nodes_part005_join_01280_01536 nodes_checked_join_01536_02048

theorem nodes_checked_join_02304_02816 : FiniteChecks.Interval nodeTest 2304 2816 :=
  FiniteChecks.interval_append nodeTest 2304 2560 2816 nodes_part009_join_02304_02560 nodes_part010_join_02560_02816

theorem nodes_checked_join_02048_02816 : FiniteChecks.Interval nodeTest 2048 2816 :=
  FiniteChecks.interval_append nodeTest 2048 2304 2816 nodes_part008_join_02048_02304 nodes_checked_join_02304_02816

theorem nodes_checked_join_01280_02816 : FiniteChecks.Interval nodeTest 1280 2816 :=
  FiniteChecks.interval_append nodeTest 1280 2048 2816 nodes_checked_join_01280_02048 nodes_checked_join_02048_02816

theorem nodes_checked_join_00000_02816 : FiniteChecks.Interval nodeTest 0 2816 :=
  FiniteChecks.interval_append nodeTest 0 1280 2816 nodes_checked_join_00000_01280 nodes_checked_join_01280_02816

theorem nodes_checked_join_02816_03328 : FiniteChecks.Interval nodeTest 2816 3328 :=
  FiniteChecks.interval_append nodeTest 2816 3072 3328 nodes_part011_join_02816_03072 nodes_part012_join_03072_03328

theorem nodes_checked_join_03584_04096 : FiniteChecks.Interval nodeTest 3584 4096 :=
  FiniteChecks.interval_append nodeTest 3584 3840 4096 nodes_part014_join_03584_03840 nodes_part015_join_03840_04096

theorem nodes_checked_join_03328_04096 : FiniteChecks.Interval nodeTest 3328 4096 :=
  FiniteChecks.interval_append nodeTest 3328 3584 4096 nodes_part013_join_03328_03584 nodes_checked_join_03584_04096

theorem nodes_checked_join_02816_04096 : FiniteChecks.Interval nodeTest 2816 4096 :=
  FiniteChecks.interval_append nodeTest 2816 3328 4096 nodes_checked_join_02816_03328 nodes_checked_join_03328_04096

theorem nodes_checked_join_04352_04864 : FiniteChecks.Interval nodeTest 4352 4864 :=
  FiniteChecks.interval_append nodeTest 4352 4608 4864 nodes_part017_join_04352_04608 nodes_part018_join_04608_04864

theorem nodes_checked_join_04096_04864 : FiniteChecks.Interval nodeTest 4096 4864 :=
  FiniteChecks.interval_append nodeTest 4096 4352 4864 nodes_part016_join_04096_04352 nodes_checked_join_04352_04864

theorem nodes_checked_join_05120_05632 : FiniteChecks.Interval nodeTest 5120 5632 :=
  FiniteChecks.interval_append nodeTest 5120 5376 5632 nodes_part020_join_05120_05376 nodes_part021_join_05376_05632

theorem nodes_checked_join_04864_05632 : FiniteChecks.Interval nodeTest 4864 5632 :=
  FiniteChecks.interval_append nodeTest 4864 5120 5632 nodes_part019_join_04864_05120 nodes_checked_join_05120_05632

theorem nodes_checked_join_04096_05632 : FiniteChecks.Interval nodeTest 4096 5632 :=
  FiniteChecks.interval_append nodeTest 4096 4864 5632 nodes_checked_join_04096_04864 nodes_checked_join_04864_05632

theorem nodes_checked_join_02816_05632 : FiniteChecks.Interval nodeTest 2816 5632 :=
  FiniteChecks.interval_append nodeTest 2816 4096 5632 nodes_checked_join_02816_04096 nodes_checked_join_04096_05632

theorem nodes_checked_join_00000_05632 : FiniteChecks.Interval nodeTest 0 5632 :=
  FiniteChecks.interval_append nodeTest 0 2816 5632 nodes_checked_join_00000_02816 nodes_checked_join_02816_05632

theorem nodes_checked_join_05632_06144 : FiniteChecks.Interval nodeTest 5632 6144 :=
  FiniteChecks.interval_append nodeTest 5632 5888 6144 nodes_part022_join_05632_05888 nodes_part023_join_05888_06144

theorem nodes_checked_join_06400_06912 : FiniteChecks.Interval nodeTest 6400 6912 :=
  FiniteChecks.interval_append nodeTest 6400 6656 6912 nodes_part025_join_06400_06656 nodes_part026_join_06656_06912

theorem nodes_checked_join_06144_06912 : FiniteChecks.Interval nodeTest 6144 6912 :=
  FiniteChecks.interval_append nodeTest 6144 6400 6912 nodes_part024_join_06144_06400 nodes_checked_join_06400_06912

theorem nodes_checked_join_05632_06912 : FiniteChecks.Interval nodeTest 5632 6912 :=
  FiniteChecks.interval_append nodeTest 5632 6144 6912 nodes_checked_join_05632_06144 nodes_checked_join_06144_06912

theorem nodes_checked_join_07168_07680 : FiniteChecks.Interval nodeTest 7168 7680 :=
  FiniteChecks.interval_append nodeTest 7168 7424 7680 nodes_part028_join_07168_07424 nodes_part029_join_07424_07680

theorem nodes_checked_join_06912_07680 : FiniteChecks.Interval nodeTest 6912 7680 :=
  FiniteChecks.interval_append nodeTest 6912 7168 7680 nodes_part027_join_06912_07168 nodes_checked_join_07168_07680

theorem nodes_checked_join_07936_08448 : FiniteChecks.Interval nodeTest 7936 8448 :=
  FiniteChecks.interval_append nodeTest 7936 8192 8448 nodes_part031_join_07936_08192 nodes_part032_join_08192_08448

theorem nodes_checked_join_07680_08448 : FiniteChecks.Interval nodeTest 7680 8448 :=
  FiniteChecks.interval_append nodeTest 7680 7936 8448 nodes_part030_join_07680_07936 nodes_checked_join_07936_08448

theorem nodes_checked_join_06912_08448 : FiniteChecks.Interval nodeTest 6912 8448 :=
  FiniteChecks.interval_append nodeTest 6912 7680 8448 nodes_checked_join_06912_07680 nodes_checked_join_07680_08448

theorem nodes_checked_join_05632_08448 : FiniteChecks.Interval nodeTest 5632 8448 :=
  FiniteChecks.interval_append nodeTest 5632 6912 8448 nodes_checked_join_05632_06912 nodes_checked_join_06912_08448

theorem nodes_checked_join_08704_09216 : FiniteChecks.Interval nodeTest 8704 9216 :=
  FiniteChecks.interval_append nodeTest 8704 8960 9216 nodes_part034_join_08704_08960 nodes_part035_join_08960_09216

theorem nodes_checked_join_08448_09216 : FiniteChecks.Interval nodeTest 8448 9216 :=
  FiniteChecks.interval_append nodeTest 8448 8704 9216 nodes_part033_join_08448_08704 nodes_checked_join_08704_09216

theorem nodes_checked_join_09472_09984 : FiniteChecks.Interval nodeTest 9472 9984 :=
  FiniteChecks.interval_append nodeTest 9472 9728 9984 nodes_part037_join_09472_09728 nodes_part038_join_09728_09984

theorem nodes_checked_join_09216_09984 : FiniteChecks.Interval nodeTest 9216 9984 :=
  FiniteChecks.interval_append nodeTest 9216 9472 9984 nodes_part036_join_09216_09472 nodes_checked_join_09472_09984

theorem nodes_checked_join_08448_09984 : FiniteChecks.Interval nodeTest 8448 9984 :=
  FiniteChecks.interval_append nodeTest 8448 9216 9984 nodes_checked_join_08448_09216 nodes_checked_join_09216_09984

theorem nodes_checked_join_10240_10752 : FiniteChecks.Interval nodeTest 10240 10752 :=
  FiniteChecks.interval_append nodeTest 10240 10496 10752 nodes_part040_join_10240_10496 nodes_part041_join_10496_10752

theorem nodes_checked_join_09984_10752 : FiniteChecks.Interval nodeTest 9984 10752 :=
  FiniteChecks.interval_append nodeTest 9984 10240 10752 nodes_part039_join_09984_10240 nodes_checked_join_10240_10752

theorem nodes_checked_join_11008_11426 : FiniteChecks.Interval nodeTest 11008 11426 :=
  FiniteChecks.interval_append nodeTest 11008 11264 11426 nodes_part043_join_11008_11264 nodes_part044_join_11264_11426

theorem nodes_checked_join_10752_11426 : FiniteChecks.Interval nodeTest 10752 11426 :=
  FiniteChecks.interval_append nodeTest 10752 11008 11426 nodes_part042_join_10752_11008 nodes_checked_join_11008_11426

theorem nodes_checked_join_09984_11426 : FiniteChecks.Interval nodeTest 9984 11426 :=
  FiniteChecks.interval_append nodeTest 9984 10752 11426 nodes_checked_join_09984_10752 nodes_checked_join_10752_11426

theorem nodes_checked_join_08448_11426 : FiniteChecks.Interval nodeTest 8448 11426 :=
  FiniteChecks.interval_append nodeTest 8448 9984 11426 nodes_checked_join_08448_09984 nodes_checked_join_09984_11426

theorem nodes_checked_join_05632_11426 : FiniteChecks.Interval nodeTest 5632 11426 :=
  FiniteChecks.interval_append nodeTest 5632 8448 11426 nodes_checked_join_05632_08448 nodes_checked_join_08448_11426

theorem nodes_checked_join_00000_11426 : FiniteChecks.Interval nodeTest 0 11426 :=
  FiniteChecks.interval_append nodeTest 0 5632 11426 nodes_checked_join_00000_05632 nodes_checked_join_05632_11426

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
