module
prelude
public meta import GraphCases
public import GraphInputsRow16Part00023Checked
public import GraphInputsRow16Part00023Metadata
public import GraphInputsRow16Part00023Frames
public import GraphInputsRow16Part00023Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch014
public import GraphInputsRow16Part00023Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 16 24783246885120 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01419 14

certified_graph_case record001 16 24817971503360 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01420 14

certified_graph_case record002 16 24822261252352 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01421 14

certified_graph_case record003 16 24822272761856 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01422 14

certified_graph_case record004 16 24834743501056 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01423 14

certified_graph_case record005 16 24838106783744 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01424 14

certified_graph_case record006 16 24845718978816 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01425 14

certified_graph_case record007 16 24845727367168 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01426 14

certified_graph_case record008 16 24846119502080 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01427 14

certified_graph_case record009 16 24849339154688 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01428 14

certified_graph_case record010 16 24849351184384 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01429 14

certified_graph_case record011 16 24849879728384 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01430 14

certified_graph_case record012 16 24850416599040 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01431 14

certified_graph_case record013 16 24850424922112 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01432 14

certified_graph_case record014 16 24851960103168 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01433 14

certified_graph_case record015 16 24851968491520 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01434 14

certified_graph_case record016 16 24852100612096 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01435 14

certified_graph_case record017 16 24852166672384 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01436 14

certified_graph_case record018 16 24852360626432 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01437 14

certified_graph_case record019 16 24853231501568 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01438 14

certified_graph_case record020 16 24853499904256 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01439 14

certified_graph_case record021 16 24853511933952 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01440 14

certified_graph_case record022 16 24854577348608 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01441 14

certified_graph_case record023 16 24855580279040 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01442 14

certified_graph_case record024 16 24857161040128 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01443 14

certified_graph_case record025 16 24857433669632 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01444 14

certified_graph_case record026 16 24857697910784 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01445 14

certified_graph_case record027 16 24857706233856 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01446 14

certified_graph_case record028 16 24857929121792 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01447 14

certified_graph_case record029 16 24860686352384 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01448 14

certified_graph_case record030 16 24869003624704 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01449 14

certified_graph_case record031 16 24869139972096 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01450 14

certified_graph_case record032 16 24869148295168 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01451 14

certified_graph_case record033 16 24870043812096 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01452 14

theorem record034_parameters : Parameters record034 (rowOfCode 16) 24870180159488 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record034_coverage : Coverage record034 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24870180159488 :=
  GraphCoverageDescriptions.coverage_of_checked record034 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01453 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24870180159488
    (by rfl) record034_cells_exact
    (GraphCoverageDescriptions.small_allowed record034 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch014.candidate01453_checked

theorem record034_result : Result (16, 24870180159488) :=
  of_direct_small 16 24870180159488 (by decide) ⟨record034, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record034.direct_core, record034_parameters, record034_coverage⟩
#print axioms record034_result

theorem record035_parameters : Parameters record035 (rowOfCode 16) 24870188482560 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record035_coverage : Coverage record035 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24870188482560 :=
  GraphCoverageDescriptions.coverage_of_checked record035 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01454 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24870188482560
    (by rfl) record035_cells_exact
    (GraphCoverageDescriptions.small_allowed record035 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch014.candidate01454_checked

theorem record035_result : Result (16, 24870188482560) :=
  of_direct_small 16 24870188482560 (by decide) ⟨record035, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record035.direct_core, record035_parameters, record035_coverage⟩
#print axioms record035_result

certified_graph_case record036 16 24870411370496 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01455 14

certified_graph_case record037 16 24870948175872 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01456 14

certified_graph_case record038 16 24894908694784 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01457 14

certified_graph_case record039 16 24916384612608 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01458 14

certified_graph_case record040 16 24917924413696 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01459 14

certified_graph_case record041 16 24933564481536 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01460 14

certified_graph_case record042 16 24933572804608 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01461 14

certified_graph_case record043 16 24934604668928 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01462 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023
