module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00022Checked
public import GraphInputsRow24Part00022Metadata
public import GraphInputsRow24Part00022Frames
public import GraphInputsRow24Part00022Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch072
public import GraphInputsRow24Part00022Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 24) 12577958528008 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12577958528008 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07230 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12577958528008
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch072.candidate07230_checked

theorem record000_result : Result (24, 12577958528008) :=
  of_direct_small 24 12577958528008 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

certified_graph_case record001 24 12577975304193 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07231 14

certified_graph_case record002 24 12578103296000 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07232 14

theorem record003_parameters : Parameters record003 (rowOfCode 24) 12578354889736 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12578354889736 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07233 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12578354889736
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch072.candidate07233_checked

theorem record003_result : Result (24, 12578354889736) :=
  of_direct_small 24 12578354889736 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result

certified_graph_case record004 24 12578371665921 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07234 14

theorem record005_parameters : Parameters record005 (rowOfCode 24) 12580030711808 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12580030711808 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07235 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12580030711808
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch072.candidate07235_checked

theorem record005_result : Result (24, 12580030711808) :=
  of_direct_small 24 12580030711808 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record005.direct_core, record005_parameters, record005_coverage⟩
#print axioms record005_result

certified_graph_case record006 24 12580249731072 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07236 14

certified_graph_case record007 24 12584323516672 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07237 14

certified_graph_case record008 24 12584323581952 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07238 14

certified_graph_case record009 24 12584542601216 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07239 14

certified_graph_case record010 24 12584794194952 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07240 14

certified_graph_case record011 24 12584810971137 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07241 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022
