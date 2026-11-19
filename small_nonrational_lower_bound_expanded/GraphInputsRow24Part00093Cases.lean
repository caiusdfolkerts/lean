module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00093Checked
public import GraphInputsRow24Part00093Metadata
public import GraphInputsRow24Part00093Frames
public import GraphInputsRow24Part00093Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch091
public import GraphInputsRow24Part00093Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00093
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 25153207803968 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09163 14

certified_graph_case record001 24 25153631748096 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09164 14

certified_graph_case record002 24 25153644036352 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09165 14

theorem record003_parameters : Parameters record003 (rowOfCode 24) 25153656326144 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25153656326144 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09166 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25153656326144
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09166_checked

theorem record003_result : Result (24, 25153656326144) :=
  of_direct_small 24 25153656326144 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00093.record003.direct_core, record003_parameters, record003_coverage⟩

theorem record004_parameters : Parameters record004 (rowOfCode 24) 25153763868672 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25153763868672 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09167 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25153763868672
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09167_checked

theorem record004_result : Result (24, 25153763868672) :=
  of_direct_small 24 25153763868672 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00093.record004.direct_core, record004_parameters, record004_coverage⟩

theorem record005_parameters : Parameters record005 (rowOfCode 24) 25153770110976 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25153770110976 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09168 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25153770110976
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09168_checked

theorem record005_result : Result (24, 25153770110976) :=
  of_direct_small 24 25153770110976 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00093.record005.direct_core, record005_parameters, record005_coverage⟩

certified_graph_case record006 24 25153778237696 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09169 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00093
