module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00089Checked
public import GraphInputsRow31Part00089Metadata
public import GraphInputsRow31Part00089Frames
public import GraphInputsRow31Part00089Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch163
public import GraphInputsRow31Part00089Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 17670914195712 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16353 14

certified_graph_case record001 31 17671987413248 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16354 14

certified_graph_case record002 31 17701984763904 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16355 14

theorem record003_parameters : Parameters record003 (rowOfCode 31) 17702525599745 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17702525599745 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16356 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17702525599745
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch163.candidate16356_checked

theorem record003_result : Result (31, 17702525599745) :=
  of_direct_small 31 17702525599745 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00089.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result

certified_graph_case record004 31 17702525665280 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16357 14

certified_graph_case record005 31 17704149925888 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16358 14

certified_graph_case record006 31 17704414167040 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16359 14

certified_graph_case record007 31 17704421433408 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16360 14

certified_graph_case record008 31 17706686349313 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16361 14

certified_graph_case record009 31 17706686414848 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16362 14

certified_graph_case record010 31 17715276316672 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16363 14

certified_graph_case record011 31 17715410518016 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16364 14

certified_graph_case record012 31 17721841434880 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16365 14

certified_graph_case record013 31 17739902107712 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16366 14

certified_graph_case record014 31 17739903148096 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16367 14

certified_graph_case record015 31 17748223606848 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16368 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089
