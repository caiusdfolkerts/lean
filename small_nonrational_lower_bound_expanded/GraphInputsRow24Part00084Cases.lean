module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00084Checked
public import GraphInputsRow24Part00084Metadata
public import GraphInputsRow24Part00084Frames
public import GraphInputsRow24Part00084Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch090
public import GraphInputsRow24Part00084Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00084
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 24520071348224 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09003 14

theorem record001_parameters : Parameters record001 (rowOfCode 24) 24521111404544 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24521111404544 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24521111404544
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch090.candidate09004_checked

theorem record001_result : Result (24, 24521111404544) :=
  of_direct_small 24 24521111404544 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00084.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 24 24521243361920 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09005 14

certified_graph_case record003 24 24567299211520 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09006 14

certified_graph_case record004 24 24567307307136 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09007 14

certified_graph_case record005 24 24567769729152 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09008 14

certified_graph_case record006 24 24569503156352 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09009 14

theorem record007_parameters : Parameters record007 (rowOfCode 24) 24569651986432 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24569651986432 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24569651986432
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch090.candidate09010_checked

theorem record007_result : Result (24, 24569651986432) :=
  of_direct_small 24 24569651986432 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00084.record007.direct_core, record007_parameters, record007_coverage⟩

certified_graph_case record008 24 24571583531136 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09011 14

certified_graph_case record009 24 24576089145600 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09012 14

theorem record010_parameters : Parameters record010 (rowOfCode 24) 24576091291648 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24576091291648 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09013 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24576091291648
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch090.candidate09013_checked

theorem record010_result : Result (24, 24576091291648) :=
  of_direct_small 24 24576091291648 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00084.record010.direct_core, record010_parameters, record010_coverage⟩

theorem record011_parameters : Parameters record011 (rowOfCode 24) 24576138690816 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24576138690816 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09014 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24576138690816
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch090.candidate09014_checked

theorem record011_result : Result (24, 24576138690816) :=
  of_direct_small 24 24576138690816 (by decide) ⟨record011, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00084.record011.direct_core, record011_parameters, record011_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00084
