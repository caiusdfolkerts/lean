module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00004Checked
public import GraphInputsRow24Part00004Metadata
public import GraphInputsRow24Part00004Frames
public import GraphInputsRow24Part00004Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch062
public import GraphCoverageBatch063
public import GraphInputsRow24Part00004Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 2420424343808 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06285 14

certified_graph_case record001 24 2420424409088 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06286 14

certified_graph_case record002 24 2420625711104 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06287 14

certified_graph_case record003 24 2446667579648 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06288 14

certified_graph_case record004 24 2446667644928 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06289 14

certified_graph_case record005 24 2453040889856 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06290 14

certified_graph_case record006 24 2454716580096 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06291 14

certified_graph_case record007 24 2454716645376 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06292 14

certified_graph_case record008 24 2454720611584 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06293 14

theorem record009_parameters : Parameters record009 (rowOfCode 24) 2455257481217 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 2455257481217 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06294 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 2455257481217
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch062.candidate06294_checked

theorem record009_result : Result (24, 2455257481217) :=
  of_direct_small 24 2455257481217 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00004.record009.direct_core, record009_parameters, record009_coverage⟩
#print axioms record009_result

certified_graph_case record010 24 2459552465024 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06295 14

certified_graph_case record011 24 2469679596800 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06296 14

certified_graph_case record012 24 2469811781888 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06297 14

certified_graph_case record013 24 2469820170240 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06298 14

certified_graph_case record014 24 2470018351104 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06299 14

certified_graph_case record015 24 2470212305152 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06300 14

certified_graph_case record016 24 2470220693504 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06301 14

certified_graph_case record017 24 2522695663616 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06302 14

certified_graph_case record018 24 2583838097664 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06303 14

certified_graph_case record019 24 2583838162944 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06304 14

certified_graph_case record020 24 2584240734336 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06305 14

certified_graph_case record021 24 2588131033088 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06306 14

certified_graph_case record022 24 2588401483904 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06307 14

certified_graph_case record023 24 2590277468160 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06308 14

certified_graph_case record024 24 2601017966592 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06309 14

certified_graph_case record025 24 2601410134144 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06310 14

certified_graph_case record026 24 2601546448896 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06311 14

certified_graph_case record027 24 2605302448384 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06312 14

certified_graph_case record028 24 2605306675200 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06313 14

certified_graph_case record029 24 2605310836736 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06314 14

certified_graph_case record030 24 2605570883712 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06315 14

theorem record031_parameters : Parameters record031 (rowOfCode 24) 2605839319040 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record031_coverage : Coverage record031 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 2605839319040 :=
  GraphCoverageDescriptions.coverage_of_checked record031 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06316 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 2605839319040
    (by rfl) record031_cells_exact
    (GraphCoverageDescriptions.small_allowed record031 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch063.candidate06316_checked

theorem record031_result : Result (24, 2605839319040) :=
  of_direct_small 24 2605839319040 (by decide) ⟨record031, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00004.record031.direct_core, record031_parameters, record031_coverage⟩
#print axioms record031_result

theorem record032_parameters : Parameters record032 (rowOfCode 24) 2605843480576 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record032_coverage : Coverage record032 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 2605843480576 :=
  GraphCoverageDescriptions.coverage_of_checked record032 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06317 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 2605843480576
    (by rfl) record032_cells_exact
    (GraphCoverageDescriptions.small_allowed record032 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch063.candidate06317_checked

theorem record032_result : Result (24, 2605843480576) :=
  of_direct_small 24 2605843480576 (by decide) ⟨record032, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00004.record032.direct_core, record032_parameters, record032_coverage⟩
#print axioms record032_result

certified_graph_case record033 24 2607250702592 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06318 14

certified_graph_case record034 24 2607259090944 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06319 14

theorem record035_parameters : Parameters record035 (rowOfCode 24) 2607382823168 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record035_coverage : Coverage record035 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 2607382823168 :=
  GraphCoverageDescriptions.coverage_of_checked record035 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06320 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 2607382823168
    (by rfl) record035_cells_exact
    (GraphCoverageDescriptions.small_allowed record035 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch063.candidate06320_checked

theorem record035_result : Result (24, 2607382823168) :=
  of_direct_small 24 2607382823168 (by decide) ⟨record035, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00004.record035.direct_core, record035_parameters, record035_coverage⟩
#print axioms record035_result

certified_graph_case record036 24 2607387049984 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06321 14

certified_graph_case record037 24 2607391211520 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06322 14

certified_graph_case record038 24 2607457271808 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06323 14

certified_graph_case record039 24 2607651258496 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06324 14

certified_graph_case record040 24 2607851520128 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06325 14

certified_graph_case record041 24 2652555477248 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06326 14

theorem record042_parameters : Parameters record042 (rowOfCode 24) 2675976470528 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record042_coverage : Coverage record042 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 2675976470528 :=
  GraphCoverageDescriptions.coverage_of_checked record042 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06327 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 2675976470528
    (by rfl) record042_cells_exact
    (GraphCoverageDescriptions.small_allowed record042 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch063.candidate06327_checked

theorem record042_result : Result (24, 2675976470528) :=
  of_direct_small 24 2675976470528 (by decide) ⟨record042, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00004.record042.direct_core, record042_parameters, record042_coverage⟩
#print axioms record042_result

certified_graph_case record043 24 2686715986176 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06328 14

certified_graph_case record044 24 2686843945216 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06329 14

certified_graph_case record045 24 2686848106752 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06330 14

certified_graph_case record046 24 2686848172032 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06331 14

certified_graph_case record047 24 2686914167040 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06332 14

certified_graph_case record048 24 2686914232320 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06333 14

certified_graph_case record049 24 2687116542080 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06334 14

certified_graph_case record050 24 2687118622848 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06335 14

certified_graph_case record051 24 2789191286912 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06336 14

certified_graph_case record052 24 2796707479568 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06337 14

certified_graph_case record053 24 2801801462016 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06338 14

certified_graph_case record054 24 2801805656192 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06339 14

certified_graph_case record055 24 2827508351232 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06340 14

certified_graph_case record056 24 2828919734288 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06341 14

certified_graph_case record057 24 2836094091520 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06342 14

certified_graph_case record058 24 2934280569088 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06343 14

certified_graph_case record059 24 2981986631936 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06344 14

certified_graph_case record060 24 2981995020288 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06345 14

certified_graph_case record061 24 2982193201152 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06346 14

certified_graph_case record062 24 2982387155200 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06347 14

certified_graph_case record063 24 2982395543552 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06348 14

certified_graph_case record064 24 3034807631888 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06349 14

certified_graph_case record065 24 3096012947712 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06350 14

certified_graph_case record066 24 3096013012992 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06351 14

certified_graph_case record067 24 3096415584384 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06352 14

certified_graph_case record068 24 3098093322496 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06353 14

certified_graph_case record069 24 3098093387776 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06354 14

certified_graph_case record070 24 3102386257920 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06355 14

certified_graph_case record071 24 3102452318208 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06356 14

certified_graph_case record072 24 3102656708736 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06357 14

certified_graph_case record073 24 3115801673728 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06358 14

certified_graph_case record074 24 3119425552640 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06359 14

certified_graph_case record075 24 3119433940992 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06360 14

certified_graph_case record076 24 3119557673216 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06361 14

certified_graph_case record077 24 3119561900032 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06362 14

certified_graph_case record078 24 3119566061568 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06363 14

certified_graph_case record079 24 3119632121856 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06364 14

certified_graph_case record080 24 3119826108544 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06365 14

certified_graph_case record081 24 3120026370176 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06366 14

certified_graph_case record082 24 3120094543872 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06367 14

certified_graph_case record083 24 3120098705408 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06368 14

certified_graph_case record084 24 3131329052672 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06369 14

certified_graph_case record085 24 3135886163968 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06370 14

certified_graph_case record086 24 3153330208768 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06371 14

certified_graph_case record087 24 3153334370304 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06372 14

certified_graph_case record088 24 3157077950464 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06373 14

certified_graph_case record089 24 3157081981952 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06374 14

certified_graph_case record090 24 3157337997440 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06375 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004
