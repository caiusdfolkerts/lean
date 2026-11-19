module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00280Checked
public import GraphInputsRow29Part00280Metadata
public import GraphInputsRow29Part00280Frames
public import GraphInputsRow29Part00280Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch123
public import GraphInputsRow29Part00280Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00280
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 34225001086976 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12306 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 34228742000896 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34228742000896 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12307 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34228742000896
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch123.candidate12307_checked

theorem record001_result : Result (29, 34228742000896) :=
  of_direct_small 29 34228742000896 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00280.record001.direct_core, record001_parameters, record001_coverage⟩
#print axioms record001_result

certified_graph_case record002 29 34239496593472 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12308 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00280
