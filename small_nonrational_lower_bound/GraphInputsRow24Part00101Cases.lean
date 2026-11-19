module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00101Checked
public import GraphInputsRow24Part00101Metadata
public import GraphInputsRow24Part00101Frames
public import GraphInputsRow24Part00101Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch093
public import GraphInputsRow24Part00101Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 25641525452864 GraphCoverageDescriptions.GraphCoverageBatch093.candidate09321 14

certified_graph_case record001 24 25658186022912 GraphCoverageDescriptions.GraphCoverageBatch093.candidate09322 14

certified_graph_case record002 24 25659208507456 GraphCoverageDescriptions.GraphCoverageBatch093.candidate09323 14

certified_graph_case record003 24 25659275624448 GraphCoverageDescriptions.GraphCoverageBatch093.candidate09324 14

certified_graph_case record004 24 25659277705216 GraphCoverageDescriptions.GraphCoverageBatch093.candidate09325 14

theorem record005_parameters : Parameters record005 (rowOfCode 24) 25659409695232 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25659409695232 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch093.candidate09326 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25659409695232
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch093.candidate09326_checked

theorem record005_result : Result (24, 25659409695232) :=
  of_direct_small 24 25659409695232 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00101.record005.direct_core, record005_parameters, record005_coverage⟩
#print axioms record005_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101
