module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00103Checked
public import GraphInputsRow29Part00103Metadata
public import GraphInputsRow29Part00103Frames
public import GraphInputsRow29Part00103Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch115
public import GraphCoverageBatch147
public import GraphCoverageBatch148
public import GraphInputsRow29Part00103Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 17532610150400 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11522 14

certified_graph_case record001 29 17549236502528 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11523 14

certified_graph_case record002 29 17566953111552 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11524 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 17595714584896 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17595714584896 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11525 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17595714584896
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch115.candidate11525_checked

theorem record003_result : Result (29, 17595714584896) :=
  of_direct_small 29 17595714584896 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00103.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result

certified_graph_case record004 29 17595718746432 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11526 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 17631130755392 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17631130755392 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11527 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17631130755392
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch115.candidate11527_checked

theorem record005_result : Result (29, 17631130755392) :=
  of_direct_small 29 17631130755392 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00103.record005.direct_core, record005_parameters, record005_coverage⟩
#print axioms record005_result

certified_graph_case record006 29 17632191488320 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14783 14

certified_graph_case record007 29 17632529055872 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14784 14

certified_graph_case record008 29 17632531152960 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14785 14

certified_graph_case record009 29 17636621631744 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14786 14

certified_graph_case record010 29 17636824006784 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14787 14

certified_graph_case record011 29 17636824023104 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11528 14

certified_graph_case record012 29 17640010629248 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14788 14

certified_graph_case record013 29 17640010645568 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11529 14

certified_graph_case record014 29 17672222900288 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11530 14

certified_graph_case record015 29 17701980406532 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14789 14

certified_graph_case record016 29 17702053773568 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14790 14

certified_graph_case record017 29 17702253199488 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14791 14

certified_graph_case record018 29 17702391415040 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14792 14

certified_graph_case record019 29 17704149926144 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14793 14

certified_graph_case record020 29 17704418361472 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14794 14

certified_graph_case record021 29 17706413785856 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14795 14

certified_graph_case record022 29 17706417979648 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14796 14

certified_graph_case record023 29 17706548150400 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14797 14

certified_graph_case record024 29 17706548166720 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14798 14

certified_graph_case record025 29 17706684285184 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14799 14

certified_graph_case record026 29 17706686382336 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14800 14

certified_graph_case record027 29 17706686447616 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11531 14

certified_graph_case record028 29 17706820583680 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14801 14

certified_graph_case record029 29 17715005784320 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14802 14

certified_graph_case record030 29 17715274219648 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14803 14

certified_graph_case record031 29 17717423775872 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14804 14

certified_graph_case record032 29 17721852960832 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11532 14

certified_graph_case record033 29 17739902173248 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14805 14

certified_graph_case record034 29 17740942360640 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14806 14

certified_graph_case record035 29 17743089836096 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14807 14

certified_graph_case record036 29 17775135359232 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14808 14

certified_graph_case record037 29 17775267627072 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14809 14

certified_graph_case record038 29 17775403761920 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14810 14

certified_graph_case record039 29 17775403827200 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11533 14

certified_graph_case record040 29 17775405842688 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14811 14

certified_graph_case record041 29 17777415102528 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14812 14

certified_graph_case record042 29 17777484136704 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14813 14

certified_graph_case record043 29 17783725326336 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11534 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103
