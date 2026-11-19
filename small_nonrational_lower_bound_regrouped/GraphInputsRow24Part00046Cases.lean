module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00046Checked
public import GraphInputsRow24Part00046Metadata
public import GraphInputsRow24Part00046Frames
public import GraphInputsRow24Part00046Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch079
public import GraphCoverageBatch080
public import GraphInputsRow24Part00046Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 19097976897536 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07982 14

certified_graph_case record001 24 19097985220608 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07983 14

certified_graph_case record002 24 19098513702912 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07984 14

certified_graph_case record003 24 19099788804352 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07985 14

certified_graph_case record004 24 19099925151744 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07986 14

certified_graph_case record005 24 19099933474816 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07987 14

certified_graph_case record006 24 19100057272320 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07988 14

theorem record007_parameters : Parameters record007 (rowOfCode 24) 19100065595392 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19100065595392 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07989 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19100065595392
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch079.candidate07989_checked

theorem record007_result : Result (24, 19100065595392) :=
  of_direct_small 24 19100065595392 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00046.record007.direct_core, record007_parameters, record007_coverage⟩
#print axioms record007_result

certified_graph_case record008 24 19100329836544 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07990 14

certified_graph_case record009 24 19100525936640 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07991 14

certified_graph_case record010 24 19145229926400 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07992 14

certified_graph_case record011 24 19151931326720 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07993 14

certified_graph_case record012 24 19158114779136 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07994 14

certified_graph_case record013 24 19168508264704 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07995 14

certified_graph_case record014 24 19168642531328 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07996 14

theorem record015_parameters : Parameters record015 (rowOfCode 24) 19168650854400 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record015_coverage : Coverage record015 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19168650854400 :=
  GraphCoverageDescriptions.coverage_of_checked record015 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07997 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19168650854400
    (by rfl) record015_cells_exact
    (GraphCoverageDescriptions.small_allowed record015 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch079.candidate07997_checked

theorem record015_result : Result (24, 19168650854400) :=
  of_direct_small 24 19168650854400 (by decide) ⟨record015, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00046.record015.direct_core, record015_parameters, record015_coverage⟩
#print axioms record015_result

certified_graph_case record016 24 19169045135360 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07998 14

certified_graph_case record017 24 19169111195648 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07999 14

certified_graph_case record018 24 19179382046976 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08000 14

certified_graph_case record019 24 19179390435328 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08001 14

certified_graph_case record020 24 19179514167552 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08002 14

certified_graph_case record021 24 19179522555904 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08003 14

certified_graph_case record022 24 19179782570240 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08004 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046
