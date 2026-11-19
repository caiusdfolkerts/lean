module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00073Checked
public import GraphInputsRow24Part00073Metadata
public import GraphInputsRow24Part00073Frames
public import GraphInputsRow24Part00073Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch087
public import GraphCoverageBatch088
public import GraphInputsRow24Part00073Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00073
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 23795807027201 GraphCoverageDescriptions.GraphCoverageBatch087.candidate08797 14

certified_graph_case record001 24 23916688969984 GraphCoverageDescriptions.GraphCoverageBatch087.candidate08798 14

certified_graph_case record002 24 23916821090560 GraphCoverageDescriptions.GraphCoverageBatch087.candidate08799 14

certified_graph_case record003 24 23917085331712 GraphCoverageDescriptions.GraphCoverageBatch088.candidate08800 14

certified_graph_case record004 24 23917091622976 GraphCoverageDescriptions.GraphCoverageBatch088.candidate08801 14

certified_graph_case record005 24 23923530928192 GraphCoverageDescriptions.GraphCoverageBatch088.candidate08802 14

certified_graph_case record006 24 23924613071104 GraphCoverageDescriptions.GraphCoverageBatch088.candidate08803 14

certified_graph_case record007 24 23931903805456 GraphCoverageDescriptions.GraphCoverageBatch088.candidate08804 14

certified_graph_case record008 24 23941792940032 GraphCoverageDescriptions.GraphCoverageBatch088.candidate08805 14

theorem record009_parameters : Parameters record009 (rowOfCode 24) 23971286384896 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 23971286384896 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch088.candidate08806 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 23971286384896
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch088.candidate08806_checked

theorem record009_result : Result (24, 23971286384896) :=
  of_direct_small 24 23971286384896 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00073.record009.direct_core, record009_parameters, record009_coverage⟩

theorem record010_parameters : Parameters record010 (rowOfCode 24) 23971554852864 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 23971554852864 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch088.candidate08807 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 23971554852864
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch088.candidate08807_checked

theorem record010_result : Result (24, 23971554852864) :=
  of_direct_small 24 23971554852864 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00073.record010.direct_core, record010_parameters, record010_coverage⟩

theorem record011_parameters : Parameters record011 (rowOfCode 24) 23971563175936 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 23971563175936 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch088.candidate08808 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 23971563175936
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch088.candidate08808_checked

theorem record011_result : Result (24, 23971563175936) :=
  of_direct_small 24 23971563175936 (by decide) ⟨record011, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00073.record011.direct_core, record011_parameters, record011_coverage⟩

certified_graph_case record012 24 23972091527680 GraphCoverageDescriptions.GraphCoverageBatch088.candidate08809 14

certified_graph_case record013 24 23986993954816 GraphCoverageDescriptions.GraphCoverageBatch088.candidate08810 14

certified_graph_case record014 24 23988537458944 GraphCoverageDescriptions.GraphCoverageBatch088.candidate08811 14

certified_graph_case record015 24 23989074329600 GraphCoverageDescriptions.GraphCoverageBatch088.candidate08812 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00073
