module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00032Checked
public import GraphInputsRow26Part00032Metadata
public import GraphInputsRow26Part00032Frames
public import GraphInputsRow26Part00032Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch079
public import GraphCoverageBatch080
public import GraphCoverageBatch128
public import GraphInputsRow26Part00032Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 19100329836544 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07990 14

certified_graph_case record001 26 19100525936640 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07991 14

certified_graph_case record002 26 19145229926400 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07992 14

certified_graph_case record003 26 19151931326720 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07993 14

certified_graph_case record004 26 19158114779136 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07994 14

certified_graph_case record005 26 19168508264704 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07995 14

certified_graph_case record006 26 19168642531328 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07996 14

theorem record007_parameters : Parameters record007 (rowOfCode 26) 19168650854400 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19168650854400 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07997 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19168650854400
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch079.candidate07997_checked

theorem record007_result : Result (26, 19168650854400) :=
  of_direct_small 26 19168650854400 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00032.record007.direct_core, record007_parameters, record007_coverage⟩

certified_graph_case record008 26 19169045135360 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07998 14

certified_graph_case record009 26 19169111195648 GraphCoverageDescriptions.GraphCoverageBatch079.candidate07999 14

certified_graph_case record010 26 19179382046976 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08000 14

certified_graph_case record011 26 19179390435328 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08001 14

certified_graph_case record012 26 19179514167552 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08002 14

certified_graph_case record013 26 19179522555904 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08003 14

certified_graph_case record014 26 19179786797056 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08005 14

certified_graph_case record015 26 19179793039360 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08006 14

certified_graph_case record016 26 19179982831872 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08007 14

certified_graph_case record017 26 19184077521152 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08008 14

certified_graph_case record018 26 19184085909504 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08009 14

certified_graph_case record019 26 19184143581440 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08010 14

certified_graph_case record020 26 19192867733568 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08012 14

certified_graph_case record021 26 19245255704704 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08013 14

certified_graph_case record022 26 19247402139776 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08014 14

certified_graph_case record023 26 19280670834816 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08015 14

certified_graph_case record024 26 19281865638144 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08016 14

certified_graph_case record025 26 19281865703424 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08017 14

certified_graph_case record026 26 19285890105600 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08018 14

certified_graph_case record027 26 19286158508288 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08019 14

certified_graph_case record028 26 19286158573568 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08020 14

certified_graph_case record029 26 19286160589056 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08021 14

certified_graph_case record030 26 19289381802240 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08022 14

certified_graph_case record031 26 19294480007424 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08023 14

certified_graph_case record032 26 19294480072704 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08024 14

certified_graph_case record033 26 19298105954368 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08025 14

certified_graph_case record034 26 19320182735104 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08026 14

certified_graph_case record035 26 19320451137792 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08027 14

certified_graph_case record036 26 19320451203072 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08028 14

certified_graph_case record037 26 19321594056960 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08029 14

certified_graph_case record038 26 19328772636928 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08030 14

certified_graph_case record039 26 19328772702208 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08031 14

certified_graph_case record040 26 19389170598144 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08032 14

certified_graph_case record041 26 19389170663424 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08033 14

certified_graph_case record042 26 19390311436544 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08034 14

certified_graph_case record043 26 19397492162560 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08037 14

certified_graph_case record044 26 19397756403712 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08038 14

certified_graph_case record045 26 19398632935680 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08039 14

certified_graph_case record046 26 19398903468096 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08040 14

certified_graph_case record047 26 19435410685953 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08041 14

certified_graph_case record048 26 19457890123776 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08044 14

certified_graph_case record049 26 19471041298432 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08046 14

certified_graph_case record050 26 19475069927424 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08047 14

certified_graph_case record051 26 19499835197440 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08050 14

certified_graph_case record052 26 19504121839616 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08051 14

certified_graph_case record053 26 19512573493248 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08052 14

certified_graph_case record054 26 19512581816320 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08053 14

certified_graph_case record055 26 19538991153152 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08055 14

certified_graph_case record056 26 19539090243584 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08056 14

certified_graph_case record057 26 19573374091520 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08058 14

certified_graph_case record058 26 19573382479872 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08059 14

certified_graph_case record059 26 19573910798976 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08060 14

theorem record060_parameters : Parameters record060 (rowOfCode 26) 19586194046984 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record060_coverage : Coverage record060 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19586194046984 :=
  GraphCoverageDescriptions.coverage_of_checked record060 GraphCoverageDescriptions.GraphCoverageBatch128.candidate12842 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19586194046984
    (by rfl) record060_cells_exact
    (GraphCoverageDescriptions.small_allowed record060 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch128.candidate12842_checked

theorem record060_result : Result (26, 19586194046984) :=
  of_direct_small 26 19586194046984 (by decide) ⟨record060, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00032.record060.direct_core, record060_parameters, record060_coverage⟩

certified_graph_case record061 26 19586739079296 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08062 14

certified_graph_case record062 26 19587358294272 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08063 14

certified_graph_case record063 26 19587779266688 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08065 14

certified_graph_case record064 26 19588679008512 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08066 14

theorem record065_parameters : Parameters record065 (rowOfCode 26) 19588687396864 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record065_coverage : Coverage record065 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19588687396864 :=
  GraphCoverageDescriptions.coverage_of_checked record065 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08067 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19588687396864
    (by rfl) record065_cells_exact
    (GraphCoverageDescriptions.small_allowed record065 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch080.candidate08067_checked

theorem record065_result : Result (26, 19588687396864) :=
  of_direct_small 26 19588687396864 (by decide) ⟨record065, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00032.record065.direct_core, record065_parameters, record065_coverage⟩

certified_graph_case record066 26 19589079531776 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08068 14

certified_graph_case record067 26 19589090000896 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08069 14

certified_graph_case record068 26 19595320656128 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08074 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032
