module
prelude
public meta import GraphCases
public import GraphInputsRow16Part00020Checked
public import GraphInputsRow16Part00020Metadata
public import GraphInputsRow16Part00020Frames
public import GraphInputsRow16Part00020Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch012
public import GraphCoverageBatch013
public import GraphInputsRow16Part00020Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 16) 22864975626240 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22864975626240 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01252 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22864975626240
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch012.candidate01252_checked

theorem record000_result : Result (16, 22864975626240) :=
  of_direct_small 16 22864975626240 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00020.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

certified_graph_case record001 16 22872116494336 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01253 14

certified_graph_case record002 16 22879459639552 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01254 14

certified_graph_case record003 16 22887417282816 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01255 14

certified_graph_case record004 16 22887417348096 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01256 14

certified_graph_case record005 16 22889299542016 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01257 14

certified_graph_case record006 16 22893460226304 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01258 14

certified_graph_case record007 16 22893460291584 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01259 14

certified_graph_case record008 16 22893594492928 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01260 14

certified_graph_case record009 16 22893859709184 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01261 14

certified_graph_case record010 16 22893862895616 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01262 14

certified_graph_case record011 16 22898929631232 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01263 14

certified_graph_case record012 16 22902184394752 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01264 14

certified_graph_case record013 16 22907515371520 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01265 14

certified_graph_case record014 16 22913961959424 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01266 14

certified_graph_case record015 16 22920388706560 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01267 14

certified_graph_case record016 16 22920388771840 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01268 14

certified_graph_case record017 16 22922530980096 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01269 14

certified_graph_case record018 16 22922535141632 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01270 14

certified_graph_case record019 16 22922535206912 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01271 14

certified_graph_case record020 16 22922799382784 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01272 14

certified_graph_case record021 16 22922799448064 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01273 14

certified_graph_case record022 16 22926830157824 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01274 14

certified_graph_case record023 16 22926881458432 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01275 14

certified_graph_case record024 16 22927094398976 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01276 14

certified_graph_case record025 16 22927098560512 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01277 14

certified_graph_case record026 16 22929289019648 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01278 14

certified_graph_case record027 16 22945997160704 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01279 14

certified_graph_case record028 16 22948081762304 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01280 14

certified_graph_case record029 16 22948287225856 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01281 14

certified_graph_case record030 16 22948288136192 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01282 14

certified_graph_case record031 16 22948552377344 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01283 14

certified_graph_case record032 16 22976096403712 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01284 14

certified_graph_case record033 16 22988973965568 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01285 14

certified_graph_case record034 16 23147492425984 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01286 14

certified_graph_case record035 16 23147494572032 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01287 14

certified_graph_case record036 16 23147500814336 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01288 14

certified_graph_case record037 16 23179713069056 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01289 14

certified_graph_case record038 16 23199880347904 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01290 14

certified_graph_case record039 16 23211902304256 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01291 14

certified_graph_case record040 16 23211908546560 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01292 14

certified_graph_case record041 16 23215577563392 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01293 14

certified_graph_case record042 16 23216044146944 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01294 14

certified_graph_case record043 16 23219742654464 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01295 14

certified_graph_case record044 16 23247695397120 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01296 14

certified_graph_case record045 16 23247755215104 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01297 14

certified_graph_case record046 16 23247761457408 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01298 14

certified_graph_case record047 16 23247761522688 GraphCoverageDescriptions.GraphCoverageBatch012.candidate01299 14

certified_graph_case record048 16 23248164110400 GraphCoverageDescriptions.GraphCoverageBatch013.candidate01300 14

certified_graph_case record049 16 23248165150784 GraphCoverageDescriptions.GraphCoverageBatch013.candidate01301 14

certified_graph_case record050 16 23248223879424 GraphCoverageDescriptions.GraphCoverageBatch013.candidate01302 14

certified_graph_case record051 16 23248289939712 GraphCoverageDescriptions.GraphCoverageBatch013.candidate01303 14

certified_graph_case record052 16 23248292085760 GraphCoverageDescriptions.GraphCoverageBatch013.candidate01304 14

certified_graph_case record053 16 23248298328064 GraphCoverageDescriptions.GraphCoverageBatch013.candidate01305 14

certified_graph_case record054 16 23248300408832 GraphCoverageDescriptions.GraphCoverageBatch013.candidate01306 14

certified_graph_case record055 16 23249841832192 GraphCoverageDescriptions.GraphCoverageBatch013.candidate01307 14

certified_graph_case record056 16 23251384803392 GraphCoverageDescriptions.GraphCoverageBatch013.candidate01308 14

certified_graph_case record057 16 23280427745280 GraphCoverageDescriptions.GraphCoverageBatch013.candidate01309 14

certified_graph_case record058 16 23280495886336 GraphCoverageDescriptions.GraphCoverageBatch013.candidate01310 14

certified_graph_case record059 16 23283077562368 GraphCoverageDescriptions.GraphCoverageBatch013.candidate01311 14

certified_graph_case record060 16 23283715538944 GraphCoverageDescriptions.GraphCoverageBatch013.candidate01312 14

certified_graph_case record061 16 23284167163904 GraphCoverageDescriptions.GraphCoverageBatch013.candidate01313 14

certified_graph_case record062 16 23284838040064 GraphCoverageDescriptions.GraphCoverageBatch013.candidate01314 14

certified_graph_case record063 16 23316379418624 GraphCoverageDescriptions.GraphCoverageBatch013.candidate01315 14

theorem record064_parameters : Parameters record064 (rowOfCode 16) 23348073725952 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record064_coverage : Coverage record064 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 23348073725952 :=
  GraphCoverageDescriptions.coverage_of_checked record064 GraphCoverageDescriptions.GraphCoverageBatch013.candidate01316 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 23348073725952
    (by rfl) record064_cells_exact
    (GraphCoverageDescriptions.small_allowed record064 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch013.candidate01316_checked

theorem record064_result : Result (16, 23348073725952) :=
  of_direct_small 16 23348073725952 (by decide) ⟨record064, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00020.record064.direct_core, record064_parameters, record064_coverage⟩
#print axioms record064_result

certified_graph_case record065 16 23372249465088 GraphCoverageDescriptions.GraphCoverageBatch013.candidate01317 14

certified_graph_case record066 16 23372249530368 GraphCoverageDescriptions.GraphCoverageBatch013.candidate01318 14

certified_graph_case record067 16 23372449726720 GraphCoverageDescriptions.GraphCoverageBatch013.candidate01319 14

theorem record068_parameters : Parameters record068 (rowOfCode 16) 23372449792000 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record068_coverage : Coverage record068 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 23372449792000 :=
  GraphCoverageDescriptions.coverage_of_checked record068 GraphCoverageDescriptions.GraphCoverageBatch013.candidate01320 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 23372449792000
    (by rfl) record068_cells_exact
    (GraphCoverageDescriptions.small_allowed record068 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch013.candidate01320_checked

theorem record068_result : Result (16, 23372449792000) :=
  of_direct_small 16 23372449792000 (by decide) ⟨record068, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00020.record068.direct_core, record068_parameters, record068_coverage⟩
#print axioms record068_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020
