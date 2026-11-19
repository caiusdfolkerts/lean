module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00149Checked
public import GraphInputsRow24Part00149Metadata
public import GraphInputsRow24Part00149Frames
public import GraphInputsRow24Part00149Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch102
public import GraphInputsRow24Part00149Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 32474801930496 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10232 14

certified_graph_case record001 24 32474806157312 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10233 14

certified_graph_case record002 24 32474813960192 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10234 14

theorem record003_parameters : Parameters record003 (rowOfCode 24) 32475053297920 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32475053297920 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10235 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32475053297920
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch102.candidate10235_checked

theorem record003_result : Result (24, 32475053297920) :=
  of_direct_small 24 32475053297920 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00149.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result

theorem record004_parameters : Parameters record004 (rowOfCode 24) 32476126774016 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32476126774016 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10236 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32476126774016
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch102.candidate10236_checked

theorem record004_result : Result (24, 32476126774016) :=
  of_direct_small 24 32476126774016 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00149.record004.direct_core, record004_parameters, record004_coverage⟩
#print axioms record004_result

certified_graph_case record005 24 32487535546624 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10237 14

certified_graph_case record006 24 32487692570624 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10238 14

certified_graph_case record007 24 32488609022720 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10239 14

certified_graph_case record008 24 32489315795200 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10240 14

certified_graph_case record009 24 32492232901136 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10241 14

certified_graph_case record010 24 32506745782528 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10242 14

certified_graph_case record011 24 32507014185216 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10243 14

certified_graph_case record012 24 32507026214912 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10244 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149
