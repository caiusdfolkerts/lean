module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00156Checked
public import GraphInputsRow29Part00156Metadata
public import GraphInputsRow29Part00156Frames
public import GraphInputsRow29Part00156Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch117
public import GraphCoverageBatch152
public import GraphInputsRow29Part00156Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00156
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 24896583778304 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24896583778304 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11780 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24896583778304
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch117.candidate11780_checked

theorem record000_result : Result (29, 24896583778304) :=
  of_direct_small 29 24896583778304 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00156.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 29 24902255001856 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15219 14

theorem record002_parameters : Parameters record002 (rowOfCode 29) 24964497572096 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24964497572096 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15220 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24964497572096
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch152.candidate15220_checked

theorem record002_result : Result (29, 24964497572096) :=
  of_direct_small 29 24964497572096 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00156.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 29 24966716260352 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15221 14

certified_graph_case record004 29 25016188567808 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15222 14

certified_graph_case record005 29 25025030193152 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15223 14

certified_graph_case record006 29 25031270994048 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11781 14

certified_graph_case record007 29 25116985819392 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15224 14

certified_graph_case record008 29 25117254287360 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15225 14

certified_graph_case record009 29 25117262610432 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11782 14

certified_graph_case record010 29 25117522690048 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15226 14

certified_graph_case record011 29 25117774317568 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11783 14

certified_graph_case record012 29 25125558814976 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15227 14

certified_graph_case record013 29 25125852282880 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15228 14

theorem record014_parameters : Parameters record014 (rowOfCode 29) 25126095685632 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record014_coverage : Coverage record014 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25126095685632 :=
  GraphCoverageDescriptions.coverage_of_checked record014 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11784 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25126095685632
    (by rfl) record014_cells_exact
    (GraphCoverageDescriptions.small_allowed record014 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch117.candidate11784_checked

theorem record014_result : Result (29, 25126095685632) :=
  of_direct_small 29 25126095685632 (by decide) ⟨record014, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00156.record014.direct_core, record014_parameters, record014_coverage⟩

certified_graph_case record015 29 25126112330240 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15229 14

certified_graph_case record016 29 25134148749440 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15230 14

certified_graph_case record017 29 25142738551300 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11785 14

certified_graph_case record018 29 25152471466240 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11786 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00156
