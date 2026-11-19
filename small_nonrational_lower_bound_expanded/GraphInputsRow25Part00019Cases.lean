module
prelude
public meta import GraphCases
public import GraphInputsRow25Part00019Checked
public import GraphInputsRow25Part00019Metadata
public import GraphInputsRow25Part00019Frames
public import GraphInputsRow25Part00019Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch119
public import GraphCoverageBatch120
public import GraphInputsRow25Part00019Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 25 29176002838528 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11992 14

certified_graph_case record001 25 29176007000064 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11993 14

certified_graph_case record002 25 29176010641408 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11994 14

certified_graph_case record003 25 29176518414464 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11995 14

certified_graph_case record004 25 29177591890560 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11996 14

certified_graph_case record005 25 29185108083216 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11997 14

certified_graph_case record006 25 29276808155136 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11998 14

certified_graph_case record007 25 29276940275712 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11999 14

certified_graph_case record008 25 29277198762112 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12000 14

certified_graph_case record009 25 29277204516864 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12001 14

certified_graph_case record010 25 29281744847376 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12002 14

certified_graph_case record011 25 29283288617216 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12003 14

certified_graph_case record012 25 29283643822080 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12004 14

certified_graph_case record013 25 29291878551680 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12005 14

certified_graph_case record014 25 29414369280128 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12006 14

certified_graph_case record015 25 29414375034880 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12007 14

certified_graph_case record016 25 29420814340096 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12008 14

certified_graph_case record017 25 29515304927232 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12009 14

certified_graph_case record018 25 29523873761280 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12010 14

certified_graph_case record019 25 29550466580608 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12011 14

certified_graph_case record020 25 29550534754304 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12012 14

certified_graph_case record021 25 29550538915840 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12013 14

theorem record022_parameters : Parameters record022 (rowOfCode 25) 29550650359808 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record022_coverage : Coverage record022 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29550650359808 :=
  GraphCoverageDescriptions.coverage_of_checked record022 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12014 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29550650359808
    (by rfl) record022_cells_exact
    (GraphCoverageDescriptions.small_allowed record022 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch120.candidate12014_checked

theorem record022_result : Result (25, 29550650359808) :=
  of_direct_small 25 29550650359808 (by decide) ⟨record022, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00019.record022.direct_core, record022_parameters, record022_coverage⟩

certified_graph_case record023 25 29552596369536 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12015 14

certified_graph_case record024 25 29552998875648 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12016 14

certified_graph_case record025 25 29583751790720 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12017 14

certified_graph_case record026 25 29583886024704 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12018 14

certified_graph_case record027 25 29583890186240 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12019 14

certified_graph_case record028 25 29584137652224 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12020 14

certified_graph_case record029 25 29588029835392 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12021 14

certified_graph_case record030 25 29588298270720 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12022 14

theorem record031_parameters : Parameters record031 (rowOfCode 25) 29588314915328 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record031_coverage : Coverage record031 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29588314915328 :=
  GraphCoverageDescriptions.coverage_of_checked record031 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12023 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29588314915328
    (by rfl) record031_cells_exact
    (GraphCoverageDescriptions.small_allowed record031 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch120.candidate12023_checked

theorem record031_result : Result (25, 29588314915328) :=
  of_direct_small 25 29588314915328 (by decide) ⟨record031, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00019.record031.direct_core, record031_parameters, record031_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019
