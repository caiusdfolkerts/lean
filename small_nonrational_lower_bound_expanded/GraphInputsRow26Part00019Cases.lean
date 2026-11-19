module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00019Checked
public import GraphInputsRow26Part00019Metadata
public import GraphInputsRow26Part00019Frames
public import GraphInputsRow26Part00019Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch071
public import GraphCoverageBatch072
public import GraphCoverageBatch127
public import GraphInputsRow26Part00019Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 12100304969984 GraphCoverageDescriptions.GraphCoverageBatch127.candidate12713 14

certified_graph_case record001 26 12100342743056 GraphCoverageDescriptions.GraphCoverageBatch127.candidate12714 14

certified_graph_case record002 26 12100572364928 GraphCoverageDescriptions.GraphCoverageBatch127.candidate12715 14

certified_graph_case record003 26 12104703754256 GraphCoverageDescriptions.GraphCoverageBatch127.candidate12716 14

certified_graph_case record004 26 12113223434256 GraphCoverageDescriptions.GraphCoverageBatch127.candidate12717 14

certified_graph_case record005 26 12113290534928 GraphCoverageDescriptions.GraphCoverageBatch127.candidate12718 14

certified_graph_case record006 26 12113455136896 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07173 14

certified_graph_case record007 26 12133578407952 GraphCoverageDescriptions.GraphCoverageBatch127.candidate12719 14

certified_graph_case record008 26 12133842649104 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07175 14

certified_graph_case record009 26 12133845221504 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07176 14

certified_graph_case record010 26 12134901792896 GraphCoverageDescriptions.GraphCoverageBatch127.candidate12720 14

theorem record011_parameters : Parameters record011 (rowOfCode 26) 12138137600016 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12138137600016 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch127.candidate12721 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12138137600016
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch127.candidate12721_checked

theorem record011_result : Result (26, 12138137600016) :=
  of_direct_small 26 12138137600016 (by decide) ⟨record011, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00019.record011.direct_core, record011_parameters, record011_coverage⟩

certified_graph_case record012 26 12142287786240 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07177 14

certified_graph_case record013 26 12146727501840 GraphCoverageDescriptions.GraphCoverageBatch127.candidate12722 14

certified_graph_case record014 26 12166054903824 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07181 14

certified_graph_case record015 26 12167932354816 GraphCoverageDescriptions.GraphCoverageBatch127.candidate12723 14

certified_graph_case record016 26 12168204951680 GraphCoverageDescriptions.GraphCoverageBatch127.candidate12724 14

certified_graph_case record017 26 12172496289808 GraphCoverageDescriptions.GraphCoverageBatch127.candidate12725 14

theorem record018_parameters : Parameters record018 (rowOfCode 26) 12172497330192 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record018_coverage : Coverage record018 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12172497330192 :=
  GraphCoverageDescriptions.coverage_of_checked record018 GraphCoverageDescriptions.GraphCoverageBatch127.candidate12726 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12172497330192
    (by rfl) record018_cells_exact
    (GraphCoverageDescriptions.small_allowed record018 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch127.candidate12726_checked

theorem record018_result : Result (26, 12172497330192) :=
  of_direct_small 26 12172497330192 (by decide) ⟨record018, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00019.record018.direct_core, record018_parameters, record018_coverage⟩

certified_graph_case record019 26 12172499902592 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07183 14

certified_graph_case record020 26 12211007324160 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07185 14

certified_graph_case record021 26 12234374299904 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07186 14

certified_graph_case record022 26 12234374332544 GraphCoverageDescriptions.GraphCoverageBatch127.candidate12727 14

certified_graph_case record023 26 12234375921680 GraphCoverageDescriptions.GraphCoverageBatch127.candidate12728 14

certified_graph_case record024 26 12234510123024 GraphCoverageDescriptions.GraphCoverageBatch127.candidate12729 14

certified_graph_case record025 26 12236656558096 GraphCoverageDescriptions.GraphCoverageBatch127.candidate12730 14

certified_graph_case record026 26 12255186927744 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07189 14

certified_graph_case record027 26 12327967588352 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07190 14

certified_graph_case record028 26 12371810680848 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07191 14

certified_graph_case record029 26 12371944882192 GraphCoverageDescriptions.GraphCoverageBatch127.candidate12731 14

certified_graph_case record030 26 12372213284880 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07192 14

certified_graph_case record031 26 12374359719952 GraphCoverageDescriptions.GraphCoverageBatch127.candidate12732 14

certified_graph_case record032 26 12378652590096 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07194 14

certified_graph_case record033 26 12384035946624 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07195 14

certified_graph_case record034 26 12392357445760 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07196 14

certified_graph_case record035 26 12439587487744 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07199 14

certified_graph_case record036 26 12439589568512 GraphCoverageDescriptions.GraphCoverageBatch127.candidate12733 14

certified_graph_case record037 26 12439640869120 GraphCoverageDescriptions.GraphCoverageBatch127.candidate12734 14

certified_graph_case record038 26 12439645063296 GraphCoverageDescriptions.GraphCoverageBatch127.candidate12735 14

certified_graph_case record039 26 12439855857792 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07200 14

certified_graph_case record040 26 12439857938560 GraphCoverageDescriptions.GraphCoverageBatch127.candidate12736 14

certified_graph_case record041 26 12439857971200 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07201 14

certified_graph_case record042 26 12464046489728 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07202 14

theorem record043_parameters : Parameters record043 (rowOfCode 26) 12465136091264 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record043_coverage : Coverage record043 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12465136091264 :=
  GraphCoverageDescriptions.coverage_of_checked record043 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07203 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12465136091264
    (by rfl) record043_cells_exact
    (GraphCoverageDescriptions.small_allowed record043 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch072.candidate07203_checked

theorem record043_result : Result (26, 12465136091264) :=
  of_direct_small 26 12465136091264 (by decide) ⟨record043, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00019.record043.direct_core, record043_parameters, record043_coverage⟩

certified_graph_case record044 26 12465138204672 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07204 14

theorem record045_parameters : Parameters record045 (rowOfCode 26) 12465142236160 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record045_coverage : Coverage record045 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12465142236160 :=
  GraphCoverageDescriptions.coverage_of_checked record045 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07205 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12465142236160
    (by rfl) record045_cells_exact
    (GraphCoverageDescriptions.small_allowed record045 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch072.candidate07205_checked

theorem record045_result : Result (26, 12465142236160) :=
  of_direct_small 26 12465142236160 (by decide) ⟨record045, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00019.record045.direct_core, record045_parameters, record045_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019
