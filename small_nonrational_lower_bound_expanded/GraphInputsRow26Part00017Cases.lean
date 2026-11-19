module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00017Checked
public import GraphInputsRow26Part00017Metadata
public import GraphInputsRow26Part00017Frames
public import GraphInputsRow26Part00017Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch070
public import GraphCoverageBatch071
public import GraphCoverageBatch126
public import GraphInputsRow26Part00017Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 11410862080000 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07095 14

certified_graph_case record001 26 11410996281344 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07097 14

certified_graph_case record002 26 11411000410240 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07098 14

certified_graph_case record003 26 11411066470528 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07099 14

certified_graph_case record004 26 11413142716416 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07100 14

certified_graph_case record005 26 11413146845312 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07101 14

certified_graph_case record006 26 11417303465984 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07105 14

certified_graph_case record007 26 11417307594880 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12660 14

certified_graph_case record008 26 11422572544000 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07107 14

certified_graph_case record009 26 11422576705536 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07108 14

certified_graph_case record010 26 11431158251648 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07111 14

certified_graph_case record011 26 11431162445824 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07112 14

certified_graph_case record012 26 11431261536256 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07113 14

certified_graph_case record013 26 11431358513280 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12661 14

certified_graph_case record014 26 11435521376256 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07115 14

certified_graph_case record015 26 11444097679616 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07116 14

certified_graph_case record016 26 11444097744896 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07117 14

certified_graph_case record017 26 11444101873792 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12662 14

certified_graph_case record018 26 11444231946240 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07119 14

certified_graph_case record019 26 11444236075136 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12663 14

certified_graph_case record020 26 11444349307136 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07120 14

theorem record021_parameters : Parameters record021 (rowOfCode 26) 11444353501312 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record021_coverage : Coverage record021 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11444353501312 :=
  GraphCoverageDescriptions.coverage_of_checked record021 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12664 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11444353501312
    (by rfl) record021_cells_exact
    (GraphCoverageDescriptions.small_allowed record021 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch126.candidate12664_checked

theorem record021_result : Result (26, 11444353501312) :=
  of_direct_small 26 11444353501312 (by decide) ⟨record021, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record021.direct_core, record021_parameters, record021_coverage⟩

certified_graph_case record022 26 11444500316288 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07121 14

certified_graph_case record023 26 11444500348928 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07122 14

certified_graph_case record024 26 11446376300544 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07126 14

certified_graph_case record025 26 11446378381312 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07127 14

certified_graph_case record026 26 11446379421696 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07128 14

certified_graph_case record027 26 11446382510208 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12665 14

certified_graph_case record028 26 11446429681920 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07129 14

certified_graph_case record029 26 11446433876096 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12666 14

certified_graph_case record030 26 11446499936384 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12667 14

certified_graph_case record031 26 11446646784000 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07132 14

certified_graph_case record032 26 11448650563585 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07133 14

certified_graph_case record033 26 11450939621504 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07135 14

certified_graph_case record034 26 11450939654144 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07136 14

theorem record035_parameters : Parameters record035 (rowOfCode 26) 11452943433729 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record035_coverage : Coverage record035 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11452943433729 :=
  GraphCoverageDescriptions.coverage_of_checked record035 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12668 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11452943433729
    (by rfl) record035_cells_exact
    (GraphCoverageDescriptions.small_allowed record035 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch126.candidate12668_checked

theorem record035_result : Result (26, 11452943433729) :=
  of_direct_small 26 11452943433729 (by decide) ⟨record035, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record035.direct_core, record035_parameters, record035_coverage⟩

certified_graph_case record036 26 11455089868801 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12669 14

certified_graph_case record037 26 11459180365952 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07137 14

theorem record038_parameters : Parameters record038 (rowOfCode 26) 11471924904064 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record038_coverage : Coverage record038 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11471924904064 :=
  GraphCoverageDescriptions.coverage_of_checked record038 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07138 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11471924904064
    (by rfl) record038_cells_exact
    (GraphCoverageDescriptions.small_allowed record038 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch071.candidate07138_checked

theorem record038_result : Result (26, 11471924904064) :=
  of_direct_small 26 11471924904064 (by decide) ⟨record038, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record038.direct_core, record038_parameters, record038_coverage⟩

certified_graph_case record039 26 11471927017472 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07139 14

certified_graph_case record040 26 11471931048960 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07140 14

certified_graph_case record041 26 11472058974848 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07141 14

certified_graph_case record042 26 11472129229824 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07142 14

certified_graph_case record043 26 11478594764928 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12670 14

certified_graph_case record044 26 11478859006080 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07143 14

certified_graph_case record045 26 11548508651536 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12671 14

certified_graph_case record046 26 11548670132352 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12672 14

certified_graph_case record047 26 11554881896464 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12673 14

certified_graph_case record048 26 11563467636752 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12674 14

certified_graph_case record049 26 11583824691216 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12675 14

certified_graph_case record050 26 11588381802512 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12676 14

certified_graph_case record051 26 11684618535040 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12677 14

certified_graph_case record052 26 11684622204944 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12678 14

certified_graph_case record053 26 11709726081152 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07144 14

certified_graph_case record054 26 11822189084688 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12679 14

certified_graph_case record055 26 11846896599168 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07145 14

certified_graph_case record056 26 11958352904448 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07146 14

theorem record057_parameters : Parameters record057 (rowOfCode 26) 11958352969728 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record057_coverage : Coverage record057 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11958352969728 :=
  GraphCoverageDescriptions.coverage_of_checked record057 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07147 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11958352969728
    (by rfl) record057_cells_exact
    (GraphCoverageDescriptions.small_allowed record057 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch071.candidate07147_checked

theorem record057_result : Result (26, 11958352969728) :=
  of_direct_small 26 11958352969728 (by decide) ⟨record057, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record057.direct_core, record057_parameters, record057_coverage⟩

certified_graph_case record058 26 11958357098624 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12680 14

certified_graph_case record059 26 11958359179392 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07148 14

certified_graph_case record060 26 11958476605568 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12681 14

certified_graph_case record061 26 11958551150592 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07149 14

certified_graph_case record062 26 11958553231360 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07150 14

certified_graph_case record063 26 11958604531968 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07151 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017
