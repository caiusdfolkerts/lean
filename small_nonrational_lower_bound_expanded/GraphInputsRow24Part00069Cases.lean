module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00069Checked
public import GraphInputsRow24Part00069Metadata
public import GraphInputsRow24Part00069Frames
public import GraphInputsRow24Part00069Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch086
public import GraphInputsRow24Part00069Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00069
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 24) 23437179371520 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 23437179371520 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch086.candidate08690 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 23437179371520
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch086.candidate08690_checked

theorem record000_result : Result (24, 23437179371520) :=
  of_direct_small 24 23437179371520 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00069.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 24 23443618676736 GraphCoverageDescriptions.GraphCoverageBatch086.candidate08691 14

theorem record002_parameters : Parameters record002 (rowOfCode 24) 23451940175872 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 23451940175872 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch086.candidate08692 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 23451940175872
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch086.candidate08692_checked

theorem record002_result : Result (24, 23451940175872) :=
  of_direct_small 24 23451940175872 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00069.record002.direct_core, record002_parameters, record002_coverage⟩

theorem record003_parameters : Parameters record003 (rowOfCode 24) 23461361680384 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 23461361680384 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch086.candidate08693 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 23461361680384
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch086.candidate08693_checked

theorem record003_result : Result (24, 23461361680384) :=
  of_direct_small 24 23461361680384 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00069.record003.direct_core, record003_parameters, record003_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00069
