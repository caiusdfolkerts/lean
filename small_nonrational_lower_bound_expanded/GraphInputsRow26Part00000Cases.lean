module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00000Checked
public import GraphInputsRow26Part00000Metadata
public import GraphInputsRow26Part00000Frames
public import GraphInputsRow26Part00000Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch061
public import GraphCoverageBatch123
public import GraphInputsRow26Part00000Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 114426986880 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12366 14

certified_graph_case record001 26 247306748160 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12367 14

certified_graph_case record002 26 255764529408 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06136 14

certified_graph_case record003 26 256165052672 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06137 14

certified_graph_case record004 26 256165117952 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06138 14

certified_graph_case record005 26 256293011712 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06139 14

certified_graph_case record006 26 256301400064 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06140 14

certified_graph_case record007 26 264354431232 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06141 14

certified_graph_case record008 26 264482390272 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06143 14

certified_graph_case record009 26 264486551808 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06144 14

certified_graph_case record010 26 264486617088 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06145 14

certified_graph_case record011 26 265015034112 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06146 14

certified_graph_case record012 26 265019260928 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06147 14

certified_graph_case record013 26 265027584000 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06148 14

certified_graph_case record014 26 268647301376 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06149 14

certified_graph_case record015 26 384741507328 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12368 14

certified_graph_case record016 26 389036458240 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12369 14

certified_graph_case record017 26 476945875200 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06150 14

certified_graph_case record018 26 589830390144 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12370 14

certified_graph_case record019 26 662844834048 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12371 14

certified_graph_case record020 26 665329893632 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12372 14

certified_graph_case record021 26 665329958912 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12373 14

certified_graph_case record022 26 665589973248 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12374 14

certified_graph_case record023 26 665598361600 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06151 14

certified_graph_case record024 26 680020476160 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12375 14

theorem record025_parameters : Parameters record025 (rowOfCode 26) 680024637696 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record025_coverage : Coverage record025 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 680024637696 :=
  GraphCoverageDescriptions.coverage_of_checked record025 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12376 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 680024637696
    (by rfl) record025_cells_exact
    (GraphCoverageDescriptions.small_allowed record025 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch123.candidate12376_checked

theorem record025_result : Result (26, 680024637696) :=
  of_direct_small 26 680024637696 (by decide) ⟨record025, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00000.record025.direct_core, record025_parameters, record025_coverage⟩

certified_graph_case record026 26 680024702976 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06152 14

certified_graph_case record027 26 680553120000 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06153 14

certified_graph_case record028 26 680557346816 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06154 14

certified_graph_case record029 26 680565669888 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06155 14

certified_graph_case record030 26 736127648000 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12377 14

certified_graph_case record031 26 736127713280 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06156 14

certified_graph_case record032 26 736255607040 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12378 14

certified_graph_case record033 26 736263995392 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06157 14

certified_graph_case record034 26 737295794432 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06158 14

certified_graph_case record035 26 737304182784 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06159 14

certified_graph_case record036 26 742368837632 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06160 14

theorem record037_parameters : Parameters record037 (rowOfCode 26) 742897254656 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record037_coverage : Coverage record037 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 742897254656 :=
  GraphCoverageDescriptions.coverage_of_checked record037 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06161 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 742897254656
    (by rfl) record037_cells_exact
    (GraphCoverageDescriptions.small_allowed record037 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch061.candidate06161_checked

theorem record037_result : Result (26, 742897254656) :=
  of_direct_small 26 742897254656 (by decide) ⟨record037, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00000.record037.direct_core, record037_parameters, record037_coverage⟩

certified_graph_case record038 26 742901481472 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06162 14

certified_graph_case record039 26 744317026560 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12379 14

certified_graph_case record040 26 744317091840 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06163 14

certified_graph_case record041 26 744977629440 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06165 14

theorem record042_parameters : Parameters record042 (rowOfCode 26) 744981856256 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record042_coverage : Coverage record042 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 744981856256 :=
  GraphCoverageDescriptions.coverage_of_checked record042 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06166 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 744981856256
    (by rfl) record042_cells_exact
    (GraphCoverageDescriptions.small_allowed record042 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch061.candidate06166_checked

theorem record042_result : Result (26, 744981856256) :=
  of_direct_small 26 744981856256 (by decide) ⟨record042, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00000.record042.direct_core, record042_parameters, record042_coverage⟩

certified_graph_case record043 26 744990179328 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06167 14

theorem record044_parameters : Parameters record044 (rowOfCode 26) 746017816832 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record044_coverage : Coverage record044 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 746017816832 :=
  GraphCoverageDescriptions.coverage_of_checked record044 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12380 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 746017816832
    (by rfl) record044_cells_exact
    (GraphCoverageDescriptions.small_allowed record044 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch123.candidate12380_checked

theorem record044_result : Result (26, 746017816832) :=
  of_direct_small 26 746017816832 (by decide) ⟨record044, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00000.record044.direct_core, record044_parameters, record044_coverage⟩

certified_graph_case record045 26 748609896704 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12381 14

certified_graph_case record046 26 751726297344 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12382 14

certified_graph_case record047 26 751730524160 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06168 14

certified_graph_case record048 26 751792357632 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06169 14

certified_graph_case record049 26 751796519168 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06170 14

certified_graph_case record050 26 751796584448 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06171 14

theorem record051_parameters : Parameters record051 (rowOfCode 26) 751829549312 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record051_coverage : Coverage record051 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 751829549312 :=
  GraphCoverageDescriptions.coverage_of_checked record051 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12383 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 751829549312
    (by rfl) record051_cells_exact
    (GraphCoverageDescriptions.small_allowed record051 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch123.candidate12383_checked

theorem record051_result : Result (26, 751829549312) :=
  of_direct_small 26 751829549312 (by decide) ⟨record051, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00000.record051.direct_core, record051_parameters, record051_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000
