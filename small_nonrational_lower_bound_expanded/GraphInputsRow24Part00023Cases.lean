module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00023Checked
public import GraphInputsRow24Part00023Metadata
public import GraphInputsRow24Part00023Frames
public import GraphInputsRow24Part00023Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch072
public import GraphCoverageBatch073
public import GraphInputsRow24Part00023Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 12586804314880 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07242 14

certified_graph_case record001 24 12588952911872 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07243 14

certified_graph_case record002 24 12592913451136 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07244 14

certified_graph_case record003 24 12654462636288 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07245 14

certified_graph_case record004 24 12723182174208 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07246 14

certified_graph_case record005 24 12864232358656 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07247 14

theorem record006_parameters : Parameters record006 (rowOfCode 24) 12898600484864 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12898600484864 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07248 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12898600484864
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch072.candidate07248_checked

theorem record006_result : Result (24, 12898600484864) :=
  of_direct_small 24 12898600484864 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00023.record006.direct_core, record006_parameters, record006_coverage⟩

certified_graph_case record007 24 13104356261888 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07249 14

certified_graph_case record008 24 13125441226752 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07250 14

certified_graph_case record009 24 13125709791232 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07251 14

certified_graph_case record010 24 13134278560000 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07252 14

certified_graph_case record011 24 13134412972032 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07253 14

certified_graph_case record012 24 13136568516608 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07254 14

certified_graph_case record013 24 13238779609152 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07255 14

certified_graph_case record014 24 13304479121664 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07256 14

certified_graph_case record015 24 13306367672576 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07257 14

certified_graph_case record016 24 13308371468544 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07258 14

certified_graph_case record017 24 13308639871232 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07259 14

certified_graph_case record018 24 13308639936512 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07260 14

certified_graph_case record019 24 13310921548032 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07261 14

certified_graph_case record020 24 13350177177664 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07262 14

certified_graph_case record021 24 13350178226208 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07263 14

certified_graph_case record022 24 13377292222720 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07264 14

certified_graph_case record023 24 13377357316096 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07265 14

certified_graph_case record024 24 13379506807040 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07266 14

certified_graph_case record025 24 13384805269632 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07267 14

certified_graph_case record026 24 13385678815232 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07268 14

certified_graph_case record027 24 13386945429760 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07269 14

certified_graph_case record028 24 13422590697504 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07270 14

certified_graph_case record029 24 13513654288512 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07271 14

certified_graph_case record030 24 13516677325056 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07272 14

certified_graph_case record031 24 13524115947776 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07273 14

certified_graph_case record032 24 13524384383104 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07274 14

certified_graph_case record033 24 13524652818432 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07275 14

certified_graph_case record034 24 13524656979968 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07276 14

certified_graph_case record035 24 13610291052672 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07277 14

certified_graph_case record036 24 13643526717568 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07278 14

certified_graph_case record037 24 13651891257600 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07279 14

certified_graph_case record038 24 13652159660288 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07280 14

certified_graph_case record039 24 13652170129408 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07281 14

certified_graph_case record040 24 13669071126528 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07282 14

certified_graph_case record041 24 13669607931904 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07283 14

certified_graph_case record042 24 13754142130208 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07284 14

certified_graph_case record043 24 13822626693376 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07285 14

certified_graph_case record044 24 13822895161344 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07286 14

certified_graph_case record045 24 13823096398080 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07287 14

certified_graph_case record046 24 13839202521120 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07288 14

certified_graph_case record047 24 13856130760960 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07289 14

certified_graph_case record048 24 13856130826240 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07290 14

certified_graph_case record049 24 13858521547008 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07291 14

certified_graph_case record050 24 13858529935360 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07292 14

certified_graph_case record051 24 13873550754048 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07293 14

certified_graph_case record052 24 13873562255361 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07294 14

certified_graph_case record053 24 13890486894624 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07295 14

certified_graph_case record054 24 13899934040064 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07296 14

certified_graph_case record055 24 13900003156224 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07297 14

certified_graph_case record056 24 13903627030560 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07298 14

certified_graph_case record057 24 13929385361664 GraphCoverageDescriptions.GraphCoverageBatch072.candidate07299 14

certified_graph_case record058 24 13935436693504 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07300 14

certified_graph_case record059 24 13935828828416 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07301 14

certified_graph_case record060 24 13937975263488 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07302 14

certified_graph_case record061 24 13937986764801 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07303 14

certified_graph_case record062 24 13937986772992 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07304 14

certified_graph_case record063 24 13976629944576 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07305 14

certified_graph_case record064 24 14004550434816 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07306 14

certified_graph_case record065 24 14004558757888 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07307 14

certified_graph_case record066 24 14010254688512 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07308 14

certified_graph_case record067 24 14010989740032 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07309 14

certified_graph_case record068 24 14012607692800 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07310 14

certified_graph_case record069 24 14013144498176 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07311 14

certified_graph_case record070 24 14197287092480 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07312 14

certified_graph_case record071 24 14197823963136 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07313 14

certified_graph_case record072 24 14197832286208 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07314 14

certified_graph_case record073 24 14201447842048 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07315 14

certified_graph_case record074 24 14201720471552 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07316 14

certified_graph_case record075 24 14201984712704 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07317 14

certified_graph_case record076 24 14201993035776 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07318 14

certified_graph_case record077 24 14203528216832 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07319 14

theorem record078_parameters : Parameters record078 (rowOfCode 24) 14204263268352 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record078_coverage : Coverage record078 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 14204263268352 :=
  GraphCoverageDescriptions.coverage_of_checked record078 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07320 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 14204263268352
    (by rfl) record078_cells_exact
    (GraphCoverageDescriptions.small_allowed record078 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch073.candidate07320_checked

theorem record078_result : Result (24, 14204263268352) :=
  of_direct_small 24 14204263268352 (by decide) ⟨record078, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00023.record078.direct_core, record078_parameters, record078_coverage⟩

certified_graph_case record079 24 14216410988800 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07321 14

certified_graph_case record080 24 14218627710976 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07322 14

theorem record081_parameters : Parameters record081 (rowOfCode 24) 14218900275200 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record081_coverage : Coverage record081 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 14218900275200 :=
  GraphCoverageDescriptions.coverage_of_checked record081 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07323 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 14218900275200
    (by rfl) record081_cells_exact
    (GraphCoverageDescriptions.small_allowed record081 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch073.candidate07323_checked

theorem record081_result : Result (24, 14218900275200) :=
  of_direct_small 24 14218900275200 (by decide) ⟨record081, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00023.record081.direct_core, record081_parameters, record081_coverage⟩

theorem record082_parameters : Parameters record082 (rowOfCode 24) 14220708085760 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record082_coverage : Coverage record082 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 14220708085760 :=
  GraphCoverageDescriptions.coverage_of_checked record082 GraphCoverageDescriptions.GraphCoverageBatch073.candidate07324 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 14220708085760
    (by rfl) record082_cells_exact
    (GraphCoverageDescriptions.small_allowed record082 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch073.candidate07324_checked

theorem record082_result : Result (24, 14220708085760) :=
  of_direct_small 24 14220708085760 (by decide) ⟨record082, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00023.record082.direct_core, record082_parameters, record082_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023
