module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00114Checked
public import GraphInputsRow24Part00114Metadata
public import GraphInputsRow24Part00114Frames
public import GraphInputsRow24Part00114Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch096
public import GraphInputsRow24Part00114Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 27798256255232 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09608 14

theorem record001_parameters : Parameters record001 (rowOfCode 24) 27798313896064 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 27798313896064 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09609 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 27798313896064
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch096.candidate09609_checked

theorem record001_result : Result (24, 27798313896064) :=
  of_direct_small 24 27798313896064 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record001.direct_core, record001_parameters, record001_coverage⟩
#print axioms record001_result

certified_graph_case record002 24 27799354083456 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09610 14

certified_graph_case record003 24 27800658575360 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09611 14

certified_graph_case record004 24 27801533548672 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09612 14

certified_graph_case record005 24 27802738950144 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09613 14

certified_graph_case record006 24 27807029674240 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09614 14

certified_graph_case record007 24 27811324690432 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09615 14

certified_graph_case record008 24 27811333013504 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09616 14

certified_graph_case record009 24 27814379128960 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09617 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114
