module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00047Checked
public import GraphInputsRow29Part00047Metadata
public import GraphInputsRow29Part00047Frames
public import GraphInputsRow29Part00047Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch109
public import GraphCoverageBatch110
public import GraphCoverageBatch144
public import GraphInputsRow29Part00047Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00047
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 8252288925697 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10999 14

certified_graph_case record001 29 8252288991232 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14471 14

certified_graph_case record002 29 8263697434640 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11000 14

certified_graph_case record003 29 8264073383936 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11001 14

theorem record004_parameters : Parameters record004 (rowOfCode 29) 8264093796368 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8264093796368 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8264093796368
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch110.candidate11002_checked

theorem record004_result : Result (29, 8264093796368) :=
  of_direct_small 29 8264093796368 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00047.record004.direct_core, record004_parameters, record004_coverage⟩
#print axioms record004_result

theorem record005_parameters : Parameters record005 (rowOfCode 29) 8265167536129 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8265167536129 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8265167536129
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch110.candidate11003_checked

theorem record005_result : Result (29, 8265167536129) :=
  of_direct_small 29 8265167536129 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00047.record005.direct_core, record005_parameters, record005_coverage⟩
#print axioms record005_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00047
