module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00005Checked
public import GraphInputsRow29Part00005Metadata
public import GraphInputsRow29Part00005Frames
public import GraphInputsRow29Part00005Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch105
public import GraphCoverageBatch143
public import GraphInputsRow29Part00005Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 1919850578176 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10584 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 1920387448832 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 1920387448832 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10585 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 1920387448832
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch105.candidate10585_checked

theorem record001_result : Result (29, 1920387448832) :=
  of_direct_small 29 1920387448832 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record001.direct_core, record001_parameters, record001_coverage⟩
#print axioms record001_result

theorem record002_parameters : Parameters record002 (rowOfCode 29) 1920395771904 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 1920395771904 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10586 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 1920395771904
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch105.candidate10586_checked

theorem record002_result : Result (29, 1920395771904) :=
  of_direct_small 29 1920395771904 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record002.direct_core, record002_parameters, record002_coverage⟩
#print axioms record002_result

certified_graph_case record003 29 1942606610688 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14324 14

certified_graph_case record004 29 1942606675968 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14325 14

certified_graph_case record005 29 1972073660417 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10587 14

certified_graph_case record006 29 1980663627776 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10588 14

certified_graph_case record007 29 1980787360000 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10589 14

certified_graph_case record008 29 1996492964096 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10590 14

certified_graph_case record009 29 1996501352448 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10591 14

certified_graph_case record010 29 1996893487360 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10592 14

certified_graph_case record011 29 1998573338880 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14326 14

certified_graph_case record012 29 1998581727232 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14327 14

certified_graph_case record013 29 1999613526272 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14328 14

certified_graph_case record014 29 1999621914624 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10593 14

certified_graph_case record015 29 2002874597376 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14329 14

certified_graph_case record016 29 2002940657664 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10594 14

certified_graph_case record017 29 2003134611712 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10595 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005
