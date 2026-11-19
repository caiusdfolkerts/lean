module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00115Checked
public import GraphInputsRow24Part00115Metadata
public import GraphInputsRow24Part00115Frames
public import GraphInputsRow24Part00115Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch096
public import GraphInputsRow24Part00115Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 27817565913088 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09618 14

certified_graph_case record001 24 27868186869760 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09619 14

certified_graph_case record002 24 27874673574144 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09620 14

certified_graph_case record003 24 27903536463872 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09621 14

certified_graph_case record004 24 27903666438400 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09622 14

certified_graph_case record005 24 27903732498688 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09623 14

certified_graph_case record006 24 27915242766336 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09624 14

certified_graph_case record007 24 27915251089408 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09625 14

certified_graph_case record008 24 27936772128768 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09626 14

certified_graph_case record009 24 27936902103296 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09627 14

certified_graph_case record010 24 27936910491648 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09628 14

certified_graph_case record011 24 27937017708800 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09629 14

theorem record012_parameters : Parameters record012 (rowOfCode 24) 27938918563840 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record012_coverage : Coverage record012 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 27938918563840 :=
  GraphCoverageDescriptions.coverage_of_checked record012 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09630 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 27938918563840
    (by rfl) record012_cells_exact
    (GraphCoverageDescriptions.small_allowed record012 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch096.candidate09630_checked

theorem record012_result : Result (24, 27938918563840) :=
  of_direct_small 24 27938918563840 (by decide) ⟨record012, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00115.record012.direct_core, record012_parameters, record012_coverage⟩
#print axioms record012_result

certified_graph_case record013 24 27939048538368 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09631 14

certified_graph_case record014 24 27939050684416 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09632 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115
