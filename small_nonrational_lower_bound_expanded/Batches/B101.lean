module
public meta import LowerSchemas.Batches
public meta import ProjectionVertexSets
public import TerminalGeometry
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Papers.FiniteProjectionChecks

section
set_option debug.skipKernelTC false


section BundlePart0
/- Source: ProjectionCertificates/R_m15e10q1_0462.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0462

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 173, 525, 197, 837, 361, 241, 158, 526, 534, 426, 434, 850, 724, 368, 13, 69, 133, 517, 41, 265, 521, 97, 161, 193, 321, 769, 14, 22, 518, 138, 266, 522, 146, 274, 530, 418, 770, 140, 524, 148, 532, 196, 580, 168, 296, 112, 176, 304, 208, 336, 592, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_173, vertices_525, vertices_197, vertices_837, vertices_361, vertices_241, vertices_158, vertices_526, vertices_534, vertices_426, vertices_434, vertices_850, vertices_724, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_133, vertices_517, vertices_41, vertices_265, vertices_521, vertices_97, vertices_161, vertices_193, vertices_321, vertices_769, vertices_14, vertices_22, vertices_518, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_418, vertices_770, vertices_140, vertices_524, vertices_148, vertices_532, vertices_196, vertices_580, vertices_168, vertices_296, vertices_112, vertices_176, vertices_304, vertices_208, vertices_336, vertices_592, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_173), (false, vertices_525), (false, vertices_197), (false, vertices_837), (false, vertices_361), (false, vertices_241), (true, vertices_14), (true, vertices_22), (true, vertices_518), (true, vertices_138), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_418), (true, vertices_148), (true, vertices_532), (true, vertices_304), (true, vertices_336), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_173) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_197) then 1 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_22) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_274) then 7 else
  if p.val = (true, vertices_530) then 8 else
  if p.val = (true, vertices_418) then 16 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_592) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 525 1 197 14 22 518 138 146 274 530 148 532 304 336 592 779 418 173 837 361 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 6 7 418
cert_row_4 1 0 1 2 3 6 158 14 3
cert_row_4 2 0 3 5 7 8 850 274 2
cert_row_4 3 1 3 5 6 8 724 148 2
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 14 158 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 426
cert_cover_5 3 0 0 2 4 6 138 426 2
cert_coverFacet 4 434
cert_cover_5 4 0 0 3 4 6 146 434 2
cert_coverFacet 5 850
cert_cover_5 5 2 0 3 5 7 274 850 2
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 148 724 2
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0462

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0463.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0463

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 327, 803, 85, 665, 465, 897, 302, 526, 682, 220, 540, 364, 232, 992, 7, 259, 515, 21, 69, 81, 145, 529, 321, 385, 641, 769, 14, 262, 518, 42, 522, 290, 546, 28, 300, 76, 524, 84, 532, 324, 152, 536, 104, 168, 200, 648, 208, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_327, vertices_803, vertices_85, vertices_665, vertices_465, vertices_897, vertices_302, vertices_526, vertices_682, vertices_220, vertices_540, vertices_364, vertices_232, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_259, vertices_515, vertices_21, vertices_69, vertices_81, vertices_145, vertices_529, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_262, vertices_518, vertices_42, vertices_522, vertices_290, vertices_546, vertices_28, vertices_300, vertices_76, vertices_524, vertices_84, vertices_532, vertices_324, vertices_152, vertices_536, vertices_104, vertices_168, vertices_200, vertices_648, vertices_208, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_327), (false, vertices_803), (false, vertices_85), (false, vertices_665), (false, vertices_465), (false, vertices_897), (true, vertices_14), (true, vertices_42), (true, vertices_522), (true, vertices_28), (true, vertices_300), (true, vertices_76), (true, vertices_524), (true, vertices_104), (true, vertices_168), (true, vertices_200), (true, vertices_224), (true, vertices_352), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 15 else
  if p.val = (false, vertices_327) then 16 else
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_85) then 0 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_300) then 19 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_47 85 897 14 42 522 28 76 524 104 168 200 224 352 672 535 327 803 300 665 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 42 3
cert_row_4 1 1 2 3 5 6 220 28 3
cert_row_2 2 1 2 4 7 300
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 3 1 4
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 2 0 1 2 4 14 302 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 682
cert_cover_5 2 0 0 2 4 6 42 682 3
cert_coverFacet 3 220
cert_cover_5 3 1 1 2 3 5 28 220 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 364
cert_cover_5 5 2 1 2 4 5 300 364 3
cert_coverFacet 6 232
cert_cover_2 6 4 2 5 6 104 232 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0463

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0464.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0464

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 157, 45, 613, 645, 313, 241, 902, 218, 346, 394, 866, 812, 396, 368, 13, 37, 133, 517, 25, 41, 49, 145, 97, 193, 577, 641, 90, 138, 266, 194, 322, 578, 386, 642, 770, 44, 140, 268, 548, 388, 644, 772, 152, 280, 296, 392, 112, 304, 208, 336, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_157, vertices_45, vertices_613, vertices_645, vertices_313, vertices_241, vertices_902, vertices_218, vertices_346, vertices_394, vertices_866, vertices_812, vertices_396, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_133, vertices_517, vertices_25, vertices_41, vertices_49, vertices_145, vertices_97, vertices_193, vertices_577, vertices_641, vertices_90, vertices_138, vertices_266, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_268, vertices_548, vertices_388, vertices_644, vertices_772, vertices_152, vertices_280, vertices_296, vertices_392, vertices_112, vertices_304, vertices_208, vertices_336, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_157), (false, vertices_45), (false, vertices_613), (false, vertices_645), (false, vertices_313), (false, vertices_241), (true, vertices_90), (true, vertices_138), (true, vertices_266), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_268), (true, vertices_388), (true, vertices_772), (true, vertices_392), (true, vertices_336), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_45) then 0 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_645) then 1 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_90) then 16 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 45 1 645 138 266 322 386 770 268 388 772 392 336 352 800 707 90 157 613 313 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 6 7 8 902 386 1
cert_row_4 2 0 4 5 7 8 866 322 1
cert_row_4 3 1 2 4 7 8 812 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 6 90 218 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 7 90 346 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 322 866 1
cert_coverFacet 5 812
cert_cover_5 5 3 1 2 4 7 44 812 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0464

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0465.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0465

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 523, 83, 611, 557, 361, 465, 158, 654, 722, 284, 300, 436, 740, 480, 11, 19, 67, 515, 41, 265, 521, 81, 273, 97, 545, 321, 142, 26, 522, 82, 146, 578, 642, 28, 44, 268, 524, 148, 276, 164, 292, 548, 644, 280, 296, 208, 400, 224, 352, 608, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_523, vertices_83, vertices_611, vertices_557, vertices_361, vertices_465, vertices_158, vertices_654, vertices_722, vertices_284, vertices_300, vertices_436, vertices_740, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_67, vertices_515, vertices_41, vertices_265, vertices_521, vertices_81, vertices_273, vertices_97, vertices_545, vertices_321, vertices_142, vertices_26, vertices_522, vertices_82, vertices_146, vertices_578, vertices_642, vertices_28, vertices_44, vertices_268, vertices_524, vertices_148, vertices_276, vertices_164, vertices_292, vertices_548, vertices_644, vertices_280, vertices_296, vertices_208, vertices_400, vertices_224, vertices_352, vertices_608, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_523), (false, vertices_83), (false, vertices_611), (false, vertices_557), (false, vertices_361), (false, vertices_465), (true, vertices_142), (true, vertices_146), (true, vertices_642), (true, vertices_28), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_164), (true, vertices_292), (true, vertices_644), (true, vertices_224), (true, vertices_416), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 15 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_83) then 1 else
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_142) then 17 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_23 523 83 146 642 28 268 148 276 164 292 644 224 416 704 283 611 142 557 361 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 6 142
cert_row_4 1 0 3 5 6 8 722 82 3
cert_row_4 2 1 3 4 6 7 436 148 2
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 142 158 3
cert_coverFacet 1 654
cert_cover_5 1 0 0 1 2 8 142 654 3
cert_coverFacet 2 722
cert_cover_5 2 1 0 3 5 6 82 722 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 436
cert_cover_5 5 2 1 3 4 6 148 436 2
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 164 740 2
cert_coverFacet 7 480
cert_cover_2 7 5 4 6 7 224 480 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0465

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0466.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0466

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 653, 165, 805, 185, 281, 369, 206, 590, 394, 466, 866, 244, 612, 408, 37, 133, 517, 25, 137, 265, 521, 49, 273, 161, 289, 769, 78, 138, 266, 522, 194, 322, 578, 386, 770, 140, 524, 100, 164, 548, 196, 580, 152, 280, 392, 112, 176, 208, 336, 400, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_653, vertices_165, vertices_805, vertices_185, vertices_281, vertices_369, vertices_206, vertices_590, vertices_394, vertices_466, vertices_866, vertices_244, vertices_612, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_25, vertices_137, vertices_265, vertices_521, vertices_49, vertices_273, vertices_161, vertices_289, vertices_769, vertices_78, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_140, vertices_524, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_152, vertices_280, vertices_392, vertices_112, vertices_176, vertices_208, vertices_336, vertices_400, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_653), (false, vertices_165), (false, vertices_805), (false, vertices_185), (false, vertices_281), (false, vertices_369), (true, vertices_78), (true, vertices_138), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_100), (true, vertices_196), (true, vertices_580), (true, vertices_392), (true, vertices_208), (true, vertices_400), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (true, vertices_78) then 16 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 165 1 281 138 194 322 578 386 100 196 580 392 208 400 608 779 78 653 805 185 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 4 5 7 8 866 322 1
cert_row_4 2 0 3 5 6 7 466 194 1
cert_row_4 3 1 3 4 5 6 244 100 1
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 6 78 206 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 466
cert_cover_5 3 2 0 3 5 6 194 466 1
cert_coverFacet 4 866
cert_cover_5 4 1 0 4 5 7 322 866 1
cert_coverFacet 5 244
cert_cover_5 5 3 1 3 4 5 100 244 1
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0466

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0467.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0467

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 181, 789, 645, 313, 737, 353, 174, 526, 710, 794, 458, 60, 540, 488, 21, 133, 517, 49, 273, 97, 161, 289, 321, 577, 641, 769, 14, 134, 518, 138, 266, 522, 194, 322, 578, 770, 28, 44, 524, 52, 532, 164, 644, 56, 280, 536, 168, 296, 456, 784, 224, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_181, vertices_789, vertices_645, vertices_313, vertices_737, vertices_353, vertices_174, vertices_526, vertices_710, vertices_794, vertices_458, vertices_60, vertices_540, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_49, vertices_273, vertices_97, vertices_161, vertices_289, vertices_321, vertices_577, vertices_641, vertices_769, vertices_14, vertices_134, vertices_518, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_770, vertices_28, vertices_44, vertices_524, vertices_52, vertices_532, vertices_164, vertices_644, vertices_56, vertices_280, vertices_536, vertices_168, vertices_296, vertices_456, vertices_784, vertices_224, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_181), (false, vertices_789), (false, vertices_645), (false, vertices_313), (false, vertices_737), (false, vertices_353), (true, vertices_14), (true, vertices_134), (true, vertices_518), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_194), (true, vertices_28), (true, vertices_44), (true, vertices_524), (true, vertices_536), (true, vertices_168), (true, vertices_456)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 15 else
  if p.val = (false, vertices_181) then 17 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_313) then 20 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (false, vertices_353) then 1 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_522) then 7 else
  if p.val = (true, vertices_194) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_44) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_456) then 21 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_645), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_456), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 6 174 14 3
cert_row_4 1 0 1 5 6 8 710 134 2
cert_row_2 2 2 5 6 7 456
cert_row_4 3 0 2 3 7 8 794 266 2
cert_rows
cert_pivot_2 4 1 5 0
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 0 0 1 2 4 14 174 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 710
cert_cover_5 2 1 0 1 5 6 134 710 2
cert_coverFacet 3 794
cert_cover_5 3 3 0 2 3 7 266 794 2
cert_coverFacet 4 458
cert_cover_5 4 2 0 2 5 6 138 458 2
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 488
cert_cover_5 7 2 2 4 5 6 168 488 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0467

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0468.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0468

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 29, 109, 709, 345, 913, 449, 286, 302, 550, 434, 658, 738, 612, 488, 13, 21, 69, 517, 25, 73, 273, 529, 193, 321, 385, 641, 270, 22, 38, 518, 146, 274, 530, 162, 290, 546, 642, 28, 44, 100, 548, 580, 280, 104, 296, 328, 400, 656, 224, 608, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_29, vertices_109, vertices_709, vertices_345, vertices_913, vertices_449, vertices_286, vertices_302, vertices_550, vertices_434, vertices_658, vertices_738, vertices_612, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_69, vertices_517, vertices_25, vertices_73, vertices_273, vertices_529, vertices_193, vertices_321, vertices_385, vertices_641, vertices_270, vertices_22, vertices_38, vertices_518, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_28, vertices_44, vertices_100, vertices_548, vertices_580, vertices_280, vertices_104, vertices_296, vertices_328, vertices_400, vertices_656, vertices_224, vertices_608, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_29), (false, vertices_109), (false, vertices_709), (false, vertices_345), (false, vertices_913), (false, vertices_449), (true, vertices_270), (true, vertices_38), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_548), (true, vertices_296), (true, vertices_224), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 15 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_913) then 23 else
  if p.val = (false, vertices_449) then 1 else
  if p.val = (true, vertices_270) then 16 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 29 1 449 38 146 274 162 290 546 642 548 296 224 608 416 535 270 109 709 345 913
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 7 270
cert_row_4 1 0 3 4 6 7 434 146 2
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 270 286 3
cert_coverFacet 1 302
cert_cover_5 1 0 0 1 2 4 270 302 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 434
cert_cover_5 3 1 0 3 4 6 146 434 2
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 162 738 2
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0468

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0469.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0469

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 557, 793, 425, 625, 177, 206, 334, 394, 242, 338, 172, 780, 852, 740, 41, 265, 521, 49, 145, 273, 529, 161, 545, 385, 78, 138, 266, 82, 146, 274, 194, 322, 386, 44, 140, 268, 524, 164, 548, 196, 324, 580, 772, 168, 392, 776, 112, 176, 336, 592, 784, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_557, vertices_793, vertices_425, vertices_625, vertices_177, vertices_206, vertices_334, vertices_394, vertices_242, vertices_338, vertices_172, vertices_780, vertices_852, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_265, vertices_521, vertices_49, vertices_145, vertices_273, vertices_529, vertices_161, vertices_545, vertices_385, vertices_78, vertices_138, vertices_266, vertices_82, vertices_146, vertices_274, vertices_194, vertices_322, vertices_386, vertices_44, vertices_140, vertices_268, vertices_524, vertices_164, vertices_548, vertices_196, vertices_324, vertices_580, vertices_772, vertices_168, vertices_392, vertices_776, vertices_112, vertices_176, vertices_336, vertices_592, vertices_784, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_557), (false, vertices_793), (false, vertices_425), (false, vertices_625), (false, vertices_177), (true, vertices_78), (true, vertices_138), (true, vertices_266), (true, vertices_82), (true, vertices_194), (true, vertices_322), (true, vertices_140), (true, vertices_268), (true, vertices_164), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_336), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 177 138 266 82 194 322 140 268 164 196 324 580 772 336 224 403 78 557 793 425 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 3 4 5 6 242 82 2
cert_row_4 2 1 3 5 7 8 852 324 1
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 6 78 206 3
cert_coverFacet 1 334
cert_cover_5 1 0 0 1 2 7 78 334 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 242
cert_cover_5 3 1 0 3 4 5 82 242 2
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 172
cert_cover_2 5 2 1 4 6 44 172 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 852
cert_cover_5 7 2 1 3 5 7 324 852 1
cert_coverFacet 8 740
cert_cover_5 8 3 1 4 5 6 164 740 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0469

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0470.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0470

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 397, 525, 213, 533, 625, 961, 46, 526, 566, 234, 458, 866, 188, 240, 13, 21, 133, 517, 265, 521, 81, 529, 193, 577, 385, 769, 14, 38, 518, 42, 202, 266, 522, 98, 546, 322, 770, 44, 140, 524, 52, 148, 532, 168, 392, 112, 176, 560, 208, 224, 608, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_397, vertices_525, vertices_213, vertices_533, vertices_625, vertices_961, vertices_46, vertices_526, vertices_566, vertices_234, vertices_458, vertices_866, vertices_188, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_133, vertices_517, vertices_265, vertices_521, vertices_81, vertices_529, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_38, vertices_518, vertices_42, vertices_202, vertices_266, vertices_522, vertices_98, vertices_546, vertices_322, vertices_770, vertices_44, vertices_140, vertices_524, vertices_52, vertices_148, vertices_532, vertices_168, vertices_392, vertices_112, vertices_176, vertices_560, vertices_208, vertices_224, vertices_608, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_397), (false, vertices_525), (false, vertices_213), (false, vertices_533), (false, vertices_625), (false, vertices_961), (true, vertices_14), (true, vertices_38), (true, vertices_518), (true, vertices_42), (true, vertices_202), (true, vertices_98), (true, vertices_546), (true, vertices_322), (true, vertices_44), (true, vertices_52), (true, vertices_168), (true, vertices_176), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_38) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_202) then 16 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_52) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_224) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 7 8 866 98 3
cert_row_2 1 0 2 5 6 202
cert_row_4 2 0 1 3 4 8 566 38 2
cert_row_4 3 1 2 3 4 6 188 44 2
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 46
cert_cover_2 0 1 0 2 4 14 46 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 566
cert_cover_5 2 2 0 1 3 4 38 566 2
cert_coverFacet 3 234
cert_cover_5 3 1 0 2 4 5 42 234 3
cert_coverFacet 4 458
cert_cover_5 4 1 0 2 5 7 202 458 3
cert_coverFacet 5 866
cert_cover_5 5 0 0 4 5 7 98 866 3
cert_coverFacet 6 188
cert_cover_5 6 3 1 2 3 4 44 188 2
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0470

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0471.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0471

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [39, 583, 651, 179, 117, 593, 913, 398, 526, 422, 364, 588, 968, 880, 432, 7, 35, 131, 515, 37, 69, 49, 81, 145, 529, 577, 641, 14, 38, 390, 518, 138, 522, 162, 76, 268, 524, 100, 292, 580, 328, 584, 392, 648, 112, 176, 304, 592, 400, 784, 352, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_39, vertices_583, vertices_651, vertices_179, vertices_117, vertices_593, vertices_913, vertices_398, vertices_526, vertices_422, vertices_364, vertices_588, vertices_968, vertices_880, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_35, vertices_131, vertices_515, vertices_37, vertices_69, vertices_49, vertices_81, vertices_145, vertices_529, vertices_577, vertices_641, vertices_14, vertices_38, vertices_390, vertices_518, vertices_138, vertices_522, vertices_162, vertices_76, vertices_268, vertices_524, vertices_100, vertices_292, vertices_580, vertices_328, vertices_584, vertices_392, vertices_648, vertices_112, vertices_176, vertices_304, vertices_592, vertices_400, vertices_784, vertices_352, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_39), (false, vertices_583), (false, vertices_651), (false, vertices_179), (false, vertices_117), (false, vertices_593), (false, vertices_913), (true, vertices_14), (true, vertices_390), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_292), (true, vertices_328), (true, vertices_584), (true, vertices_392), (true, vertices_304), (true, vertices_352), (true, vertices_416), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 14 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_39) then 0 else
  if p.val = (false, vertices_583) then 15 else
  if p.val = (false, vertices_651) then 19 else
  if p.val = (false, vertices_179) then 20 else
  if p.val = (false, vertices_117) then 16 else
  if p.val = (false, vertices_593) then 1 else
  if p.val = (false, vertices_913) then 23 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_390) then 17 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_39), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_4 1 1 2 4 5 7 364 76 2
cert_row_4 2 2 5 6 7 8 968 328 2
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 422
cert_cover_5 2 0 0 1 4 6 38 422 3
cert_coverFacet 3 364
cert_cover_5 3 1 1 2 4 5 76 364 2
cert_coverFacet 4 588
cert_cover_2 4 2 1 5 8 76 588 3
cert_coverFacet 5 968
cert_cover_5 5 2 2 5 6 7 328 968 2
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0471

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0472.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0472

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 339, 387, 643, 677, 457, 241, 790, 906, 316, 236, 652, 780, 564, 376, 19, 131, 259, 515, 49, 81, 161, 545, 193, 321, 385, 641, 274, 530, 386, 642, 770, 44, 140, 268, 524, 52, 276, 532, 164, 548, 644, 772, 312, 104, 200, 328, 392, 648, 776, 112, 560, 336, 224]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_339, vertices_387, vertices_643, vertices_677, vertices_457, vertices_241, vertices_790, vertices_906, vertices_316, vertices_236, vertices_652, vertices_780, vertices_564, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_49, vertices_81, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_164, vertices_548, vertices_644, vertices_772, vertices_312, vertices_104, vertices_200, vertices_328, vertices_392, vertices_648, vertices_776, vertices_112, vertices_560, vertices_336, vertices_224] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_339), (false, vertices_387), (false, vertices_643), (false, vertices_677), (false, vertices_457), (false, vertices_241), (true, vertices_770), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_772), (true, vertices_312), (true, vertices_104), (true, vertices_648), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 15 else
  if p.val = (false, vertices_339) then 16 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_643) then 1 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_312) then 21 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_776) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_312), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 5 6 236 44 3
cert_row_2 1 2 3 4 7 312
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 0 2 6 7 8 906 386 1
cert_rows
cert_pivot_2 5 4 1 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 906
cert_cover_5 1 3 0 2 6 7 386 906 1
cert_coverFacet 2 316
cert_cover_5 2 1 1 2 3 4 44 316 2
cert_coverFacet 3 236
cert_cover_5 3 0 1 2 4 5 44 236 3
cert_coverFacet 4 652
cert_cover_2 4 2 1 6 8 140 652 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 376
cert_cover_5 7 1 2 3 4 5 312 376 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0472

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0473.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0473

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 565, 341, 581, 809, 433, 206, 590, 426, 778, 466, 652, 212, 660, 696, 21, 69, 517, 49, 273, 289, 545, 321, 577, 769, 78, 138, 266, 522, 194, 322, 578, 386, 770, 140, 524, 84, 148, 532, 196, 580, 644, 168, 296, 552, 648, 776, 176, 560, 208, 336, 400, 656, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_565, vertices_341, vertices_581, vertices_809, vertices_433, vertices_206, vertices_590, vertices_426, vertices_778, vertices_466, vertices_652, vertices_212, vertices_660, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_517, vertices_49, vertices_273, vertices_289, vertices_545, vertices_321, vertices_577, vertices_769, vertices_78, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_140, vertices_524, vertices_84, vertices_148, vertices_532, vertices_196, vertices_580, vertices_644, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_176, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_565), (false, vertices_341), (false, vertices_581), (false, vertices_809), (false, vertices_433), (true, vertices_78), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_194), (true, vertices_386), (true, vertices_140), (true, vertices_524), (true, vertices_148), (true, vertices_196), (true, vertices_644), (true, vertices_168), (true, vertices_648), (true, vertices_208), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_341) then 20 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 581 138 266 522 194 386 140 524 148 196 644 168 648 208 656 835 78 565 341 809 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 3 5 6 7 466 194 1
cert_row_4 2 0 2 4 6 7 426 138 2
cert_row_4 3 2 3 4 6 8 696 168 1
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 6 78 206 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 426
cert_cover_5 2 2 0 2 4 6 138 426 2
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 466
cert_cover_5 4 1 0 3 5 6 194 466 1
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 696
cert_cover_5 8 3 2 3 4 6 168 696 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0473

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0474.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0474

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 405, 197, 837, 665, 817, 110, 206, 570, 650, 866, 428, 356, 312, 408, 69, 133, 261, 145, 273, 529, 193, 577, 641, 769, 78, 42, 138, 522, 98, 546, 194, 578, 642, 44, 140, 100, 292, 196, 324, 388, 56, 152, 280, 536, 296, 392, 648, 304, 560, 400, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_405, vertices_197, vertices_837, vertices_665, vertices_817, vertices_110, vertices_206, vertices_570, vertices_650, vertices_866, vertices_428, vertices_356, vertices_312, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_641, vertices_769, vertices_78, vertices_42, vertices_138, vertices_522, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_44, vertices_140, vertices_100, vertices_292, vertices_196, vertices_324, vertices_388, vertices_56, vertices_152, vertices_280, vertices_536, vertices_296, vertices_392, vertices_648, vertices_304, vertices_560, vertices_400, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_405), (false, vertices_197), (false, vertices_837), (false, vertices_665), (false, vertices_817), (true, vertices_78), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_98), (true, vertices_546), (true, vertices_44), (true, vertices_140), (true, vertices_100), (true, vertices_292), (true, vertices_56), (true, vertices_280), (true, vertices_296), (true, vertices_392), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 197 42 138 522 98 546 44 140 100 292 56 280 296 392 352 707 78 405 837 665 817
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 42 2
cert_row_4 1 0 4 5 7 8 866 98 3
cert_row_2 2 0 1 2 5 78
cert_row_4 3 1 2 4 6 7 428 44 3
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 2 0 1 2 4 78 110 3
cert_coverFacet 1 206
cert_cover_5 1 2 0 1 2 6 78 206 3
cert_coverFacet 2 570
cert_cover_5 2 0 0 2 3 4 42 570 2
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 866
cert_cover_5 4 1 0 4 5 7 98 866 3
cert_coverFacet 5 428
cert_cover_5 5 3 1 2 4 6 44 428 3
cert_coverFacet 6 356
cert_cover_2 6 4 1 5 7 100 356 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0474

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0475.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0475

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 157, 661, 569, 233, 865, 286, 142, 838, 646, 394, 482, 820, 312, 424, 149, 25, 41, 137, 529, 97, 545, 193, 577, 641, 14, 134, 262, 518, 138, 266, 194, 322, 578, 386, 642, 28, 140, 276, 532, 644, 772, 56, 280, 168, 296, 392, 304, 560, 224, 352, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_157, vertices_661, vertices_569, vertices_233, vertices_865, vertices_286, vertices_142, vertices_838, vertices_646, vertices_394, vertices_482, vertices_820, vertices_312, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_149, vertices_25, vertices_41, vertices_137, vertices_529, vertices_97, vertices_545, vertices_193, vertices_577, vertices_641, vertices_14, vertices_134, vertices_262, vertices_518, vertices_138, vertices_266, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_28, vertices_140, vertices_276, vertices_532, vertices_644, vertices_772, vertices_56, vertices_280, vertices_168, vertices_296, vertices_392, vertices_304, vertices_560, vertices_224, vertices_352, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_157), (false, vertices_661), (false, vertices_569), (false, vertices_233), (false, vertices_865), (true, vertices_14), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_266), (true, vertices_322), (true, vertices_386), (true, vertices_276), (true, vertices_772), (true, vertices_280), (true, vertices_296), (true, vertices_392), (true, vertices_304), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 7 286 14 3
cert_row_4 1 0 4 5 6 7 482 194 1
cert_row_4 2 0 1 5 7 8 838 262 2
cert_row_4 3 1 3 4 7 8 820 276 2
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 14 286 3
cert_coverFacet 1 142
cert_cover_2 1 1 0 2 6 14 142 3
cert_coverFacet 2 838
cert_cover_5 2 2 0 1 5 7 262 838 2
cert_coverFacet 3 646
cert_cover_2 3 1 0 6 8 134 646 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 482
cert_cover_5 5 1 0 4 5 6 194 482 1
cert_coverFacet 6 820
cert_cover_5 6 3 1 3 4 7 276 820 2
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0475

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0476.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0476

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 555, 541, 345, 913, 865, 78, 526, 662, 230, 930, 284, 460, 404, 480, 43, 25, 73, 521, 273, 529, 97, 545, 321, 769, 14, 70, 134, 518, 74, 522, 98, 162, 546, 642, 28, 76, 268, 524, 148, 276, 532, 196, 388, 280, 328, 400, 656, 224, 352, 416, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_555, vertices_541, vertices_345, vertices_913, vertices_865, vertices_78, vertices_526, vertices_662, vertices_230, vertices_930, vertices_284, vertices_460, vertices_404, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_43, vertices_25, vertices_73, vertices_521, vertices_273, vertices_529, vertices_97, vertices_545, vertices_321, vertices_769, vertices_14, vertices_70, vertices_134, vertices_518, vertices_74, vertices_522, vertices_98, vertices_162, vertices_546, vertices_642, vertices_28, vertices_76, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_196, vertices_388, vertices_280, vertices_328, vertices_400, vertices_656, vertices_224, vertices_352, vertices_416, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_555), (false, vertices_541), (false, vertices_345), (false, vertices_913), (false, vertices_865), (true, vertices_14), (true, vertices_70), (true, vertices_134), (true, vertices_518), (true, vertices_162), (true, vertices_642), (true, vertices_76), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_196), (true, vertices_388), (true, vertices_224), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 16 else
  if p.val = (false, vertices_555) then 17 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_913) then 23 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 134 2
cert_row_4 1 0 4 6 7 8 930 162 3
cert_row_4 2 0 1 4 5 6 230 70 2
cert_row_4 3 1 2 5 6 7 460 76 3
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 662
cert_cover_5 2 0 0 1 3 6 134 662 2
cert_coverFacet 3 230
cert_cover_5 3 2 0 1 4 5 70 230 2
cert_coverFacet 4 930
cert_cover_5 4 1 0 4 6 7 162 930 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 460
cert_cover_5 6 3 1 2 5 6 76 460 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 480
cert_cover_2 8 5 4 6 7 224 480 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0476

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0477.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0477

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 583, 803, 681, 721, 481, 286, 526, 778, 668, 372, 596, 248, 312, 808, 71, 259, 515, 161, 289, 545, 193, 321, 577, 641, 14, 262, 518, 266, 522, 770, 28, 524, 84, 276, 532, 324, 580, 56, 152, 280, 168, 296, 552, 648, 776, 112, 304, 208, 592, 656, 224, 352, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_583, vertices_803, vertices_681, vertices_721, vertices_481, vertices_286, vertices_526, vertices_778, vertices_668, vertices_372, vertices_596, vertices_248, vertices_312, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_71, vertices_259, vertices_515, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_14, vertices_262, vertices_518, vertices_266, vertices_522, vertices_770, vertices_28, vertices_524, vertices_84, vertices_276, vertices_532, vertices_324, vertices_580, vertices_56, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_112, vertices_304, vertices_208, vertices_592, vertices_656, vertices_224, vertices_352, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_583), (false, vertices_803), (false, vertices_681), (false, vertices_721), (false, vertices_481), (true, vertices_14), (true, vertices_266), (true, vertices_522), (true, vertices_28), (true, vertices_524), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_776), (true, vertices_112), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 16 else
  if p.val = (false, vertices_583) then 17 else
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_304) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 7 286 14 3
cert_row_4 1 1 2 3 6 8 668 28 3
cert_row_4 2 1 3 4 5 7 372 84 2
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 14 286 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 668
cert_cover_5 3 1 1 2 3 6 28 668 3
cert_coverFacet 4 372
cert_cover_5 4 2 1 3 4 5 84 372 2
cert_coverFacet 5 596
cert_cover_2 5 3 1 5 8 84 596 3
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 56 248 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0477

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0478.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0478

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [59, 267, 419, 901, 793, 561, 737, 94, 334, 626, 354, 540, 780, 724, 484, 11, 35, 259, 25, 265, 49, 529, 161, 545, 385, 641, 769, 78, 26, 266, 50, 82, 98, 290, 322, 28, 268, 524, 84, 532, 196, 324, 388, 644, 772, 536, 776, 560, 592, 224, 352, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_59, vertices_267, vertices_419, vertices_901, vertices_793, vertices_561, vertices_737, vertices_94, vertices_334, vertices_626, vertices_354, vertices_540, vertices_780, vertices_724, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_25, vertices_265, vertices_49, vertices_529, vertices_161, vertices_545, vertices_385, vertices_641, vertices_769, vertices_78, vertices_26, vertices_266, vertices_50, vertices_82, vertices_98, vertices_290, vertices_322, vertices_28, vertices_268, vertices_524, vertices_84, vertices_532, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_536, vertices_776, vertices_560, vertices_592, vertices_224, vertices_352, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_59), (false, vertices_267), (false, vertices_419), (false, vertices_901), (false, vertices_793), (false, vertices_561), (false, vertices_737), (true, vertices_78), (true, vertices_82), (true, vertices_98), (true, vertices_322), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_532), (true, vertices_196), (true, vertices_324), (true, vertices_592), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_59) then 15 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_561) then 1 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 3 4 5 8 626 50 3
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 1 4 5 6 7 484 196 1
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 78 94 3
cert_coverFacet 1 334
cert_cover_5 1 0 0 1 2 7 78 334 3
cert_coverFacet 2 626
cert_cover_5 2 1 0 3 4 5 50 626 3
cert_coverFacet 3 354
cert_cover_2 3 4 0 5 7 98 354 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 724
cert_cover_5 6 2 1 3 5 6 84 724 3
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 196 484 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0478

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0479.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0479

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 709, 665, 457, 785, 865, 62, 174, 394, 818, 418, 540, 652, 628, 484, 25, 137, 265, 273, 529, 193, 321, 577, 641, 769, 46, 26, 138, 266, 50, 274, 162, 290, 386, 28, 140, 524, 52, 532, 100, 164, 196, 580, 644, 536, 392, 648, 560, 784, 352, 608, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_709, vertices_665, vertices_457, vertices_785, vertices_865, vertices_62, vertices_174, vertices_394, vertices_818, vertices_418, vertices_540, vertices_652, vertices_628, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_46, vertices_26, vertices_138, vertices_266, vertices_50, vertices_274, vertices_162, vertices_290, vertices_386, vertices_28, vertices_140, vertices_524, vertices_52, vertices_532, vertices_100, vertices_164, vertices_196, vertices_580, vertices_644, vertices_536, vertices_392, vertices_648, vertices_560, vertices_784, vertices_352, vertices_608, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_709), (false, vertices_665), (false, vertices_457), (false, vertices_785), (false, vertices_865), (true, vertices_46), (true, vertices_138), (true, vertices_50), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_28), (true, vertices_140), (true, vertices_524), (true, vertices_52), (true, vertices_532), (true, vertices_100), (true, vertices_164), (true, vertices_560), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 16 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_46) then 17 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_164) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 785 138 50 162 290 386 28 140 524 52 532 100 164 560 416 283 46 709 665 457 865
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 3 4 7 8 818 50 3
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 46 62 3
cert_coverFacet 1 174
cert_cover_5 1 0 0 1 2 6 46 174 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 818
cert_cover_5 3 1 0 3 4 7 50 818 3
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 628
cert_cover_5 7 2 1 3 4 5 52 628 3
cert_coverFacet 8 484
cert_cover_5 8 3 1 4 5 6 100 484 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0479

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0480.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0480

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 555, 597, 665, 241, 865, 398, 778, 434, 802, 844, 652, 372, 404, 660, 43, 137, 521, 81, 145, 529, 97, 161, 545, 577, 138, 266, 522, 162, 290, 546, 386, 770, 140, 268, 524, 84, 148, 276, 532, 324, 580, 388, 644, 648, 776, 112, 176, 304, 400, 656, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_555, vertices_597, vertices_665, vertices_241, vertices_865, vertices_398, vertices_778, vertices_434, vertices_802, vertices_844, vertices_652, vertices_372, vertices_404, vertices_660] (by decide +kernel)
  polygons := literalFinset [vertices_43, vertices_137, vertices_521, vertices_81, vertices_145, vertices_529, vertices_97, vertices_161, vertices_545, vertices_577, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_140, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_324, vertices_580, vertices_388, vertices_644, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_400, vertices_656, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_555), (false, vertices_597), (false, vertices_665), (false, vertices_241), (false, vertices_865), (true, vertices_266), (true, vertices_290), (true, vertices_386), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_324), (true, vertices_388), (true, vertices_644), (true, vertices_776), (true, vertices_304), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 16 else
  if p.val = (false, vertices_555) then 17 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 5 7 8 844 268 2
cert_row_4 1 0 1 2 6 7 398 138 1
cert_row_4 2 0 3 4 6 7 434 162 1
cert_row_4 3 1 3 4 5 7 372 84 2
cert_rows
cert_pivot_2 8 2 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 138 398 1
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 434
cert_cover_5 2 2 0 3 4 6 162 434 1
cert_coverFacet 3 802
cert_cover_2 3 4 0 7 8 290 802 3
cert_coverFacet 4 844
cert_cover_5 4 0 1 2 5 7 268 844 2
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 372
cert_cover_5 6 3 1 3 4 5 84 372 2
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 660
cert_cover_2 8 3 1 6 8 148 660 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0480

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0481.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0481

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 213, 405, 613, 809, 369, 390, 646, 314, 218, 650, 778, 402, 716, 632, 149, 69, 261, 517, 81, 273, 97, 289, 545, 769, 134, 262, 518, 26, 138, 266, 522, 146, 274, 386, 642, 770, 196, 580, 388, 644, 56, 88, 296, 552, 200, 584, 648, 776, 112, 304, 208, 400, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_213, vertices_405, vertices_613, vertices_809, vertices_369, vertices_390, vertices_646, vertices_314, vertices_218, vertices_650, vertices_778, vertices_402, vertices_716, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_149, vertices_69, vertices_261, vertices_517, vertices_81, vertices_273, vertices_97, vertices_289, vertices_545, vertices_769, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_386, vertices_642, vertices_770, vertices_196, vertices_580, vertices_388, vertices_644, vertices_56, vertices_88, vertices_296, vertices_552, vertices_200, vertices_584, vertices_648, vertices_776, vertices_112, vertices_304, vertices_208, vertices_400, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_213), (false, vertices_405), (false, vertices_613), (false, vertices_809), (false, vertices_369), (true, vertices_134), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_386), (true, vertices_642), (true, vertices_644), (true, vertices_56), (true, vertices_88), (true, vertices_200), (true, vertices_584), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_648) then 14 else
  0
cert_priority
cert_nodeAtPriority_68 0 134 1 26 138 266 522 146 274 386 642 644 56 88 200 584 648 775 213 405 613 809 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 7 314 26 3
cert_row_4 1 0 2 3 5 6 218 26 3
cert_row_4 2 1 2 5 6 8 716 196 1
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 390
cert_cover_2 0 1 0 6 7 134 390 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 314
cert_cover_5 2 0 0 2 3 4 26 314 3
cert_coverFacet 3 218
cert_cover_5 3 1 0 2 3 5 26 218 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 778
cert_cover_2 5 2 0 7 8 266 778 3
cert_coverFacet 6 402
cert_cover_2 6 3 0 6 7 146 402 3
cert_coverFacet 7 716
cert_cover_5 7 2 1 2 5 6 196 716 1
cert_coverFacet 8 632
cert_cover_5 8 3 2 3 4 5 56 632 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0481

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0482.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0482

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 109, 333, 185, 913, 481, 542, 270, 614, 326, 786, 962, 556, 568, 752, 77, 25, 41, 265, 145, 273, 97, 161, 321, 385, 14, 70, 262, 518, 26, 266, 274, 530, 322, 578, 770, 44, 268, 524, 100, 548, 324, 56, 536, 552, 176, 560, 656, 784, 224, 608, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_109, vertices_333, vertices_185, vertices_913, vertices_481, vertices_542, vertices_270, vertices_614, vertices_326, vertices_786, vertices_962, vertices_556, vertices_568, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_77, vertices_25, vertices_41, vertices_265, vertices_145, vertices_273, vertices_97, vertices_161, vertices_321, vertices_385, vertices_14, vertices_70, vertices_262, vertices_518, vertices_26, vertices_266, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_44, vertices_268, vertices_524, vertices_100, vertices_548, vertices_324, vertices_56, vertices_536, vertices_552, vertices_176, vertices_560, vertices_656, vertices_784, vertices_224, vertices_608, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_109), (false, vertices_333), (false, vertices_185), (false, vertices_913), (false, vertices_481), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_530), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_524), (true, vertices_548), (true, vertices_536), (true, vertices_552), (true, vertices_560), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 16 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_913) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 14 3
cert_row_4 1 0 1 4 5 8 614 70 2
cert_row_4 2 0 5 6 7 8 962 322 2
cert_row_4 3 3 4 5 6 8 752 176 2
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 14 542 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 614
cert_cover_5 2 1 0 1 4 5 70 614 2
cert_coverFacet 3 326
cert_cover_2 3 1 0 5 7 70 326 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 962
cert_cover_5 5 2 0 5 6 7 322 962 2
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 176 752 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0482

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0483.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0483

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 781, 341, 149, 677, 721, 558, 314, 778, 370, 738, 156, 284, 172, 248, 21, 133, 261, 517, 81, 145, 321, 577, 641, 769, 42, 266, 522, 306, 98, 546, 322, 578, 770, 28, 44, 140, 268, 524, 148, 276, 164, 548, 56, 152, 280, 168, 776, 112, 208, 336, 224, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_781, vertices_341, vertices_149, vertices_677, vertices_721, vertices_558, vertices_314, vertices_778, vertices_370, vertices_738, vertices_156, vertices_284, vertices_172, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_321, vertices_577, vertices_641, vertices_769, vertices_42, vertices_266, vertices_522, vertices_306, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_44, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_164, vertices_548, vertices_56, vertices_152, vertices_280, vertices_168, vertices_776, vertices_112, vertices_208, vertices_336, vertices_224, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_781), (false, vertices_341), (false, vertices_149), (false, vertices_677), (false, vertices_721), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_306), (true, vertices_98), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_140), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_112), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_341) then 20 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_306) then 17 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
cert_nodeAtPriority_19 0 149 1 42 266 522 98 546 28 44 140 56 152 280 168 112 224 835 306 781 341 677 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 7 306
cert_row_4 1 0 1 2 4 8 558 42 1
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 7 1 0 2
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 42 558 1
cert_coverFacet 1 314
cert_cover_5 1 0 0 2 3 4 42 314 2
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 370
cert_cover_5 3 0 0 3 4 5 306 370 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 98 738 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 172
cert_cover_2 7 2 1 4 6 44 172 3
cert_coverFacet 8 248
cert_cover_5 8 3 2 3 4 5 56 248 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0483

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0484.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0484

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 157, 77, 565, 713, 433, 673, 334, 774, 818, 482, 738, 284, 788, 472, 13, 21, 69, 517, 73, 137, 49, 145, 161, 545, 577, 641, 70, 262, 518, 226, 290, 546, 322, 578, 770, 28, 76, 268, 276, 532, 772, 152, 280, 200, 328, 304, 560, 400, 784, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_157, vertices_77, vertices_565, vertices_713, vertices_433, vertices_673, vertices_334, vertices_774, vertices_818, vertices_482, vertices_738, vertices_284, vertices_788, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_69, vertices_517, vertices_73, vertices_137, vertices_49, vertices_145, vertices_161, vertices_545, vertices_577, vertices_641, vertices_70, vertices_262, vertices_518, vertices_226, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_76, vertices_268, vertices_276, vertices_532, vertices_772, vertices_152, vertices_280, vertices_200, vertices_328, vertices_304, vertices_560, vertices_400, vertices_784, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_157), (false, vertices_77), (false, vertices_565), (false, vertices_713), (false, vertices_433), (false, vertices_673), (true, vertices_262), (true, vertices_226), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_770), (true, vertices_268), (true, vertices_276), (true, vertices_772), (true, vertices_280), (true, vertices_328), (true, vertices_784), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 15 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_77) then 0 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_673) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_226) then 16 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 77 1 673 262 290 546 322 770 268 276 772 280 328 784 448 583 226 157 565 713 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 7 334 70 2
cert_row_4 1 0 3 4 7 8 818 290 1
cert_row_2 2 0 4 5 6 226
cert_row_4 3 2 3 5 6 7 472 152 2
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 70 334 2
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 818
cert_cover_5 2 1 0 3 4 7 290 818 1
cert_coverFacet 3 482
cert_cover_5 3 2 0 4 5 7 226 482 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 8 226 738 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 152 472 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0484

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0485.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0485

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 563, 227, 613, 537, 201, 841, 406, 534, 422, 550, 852, 356, 920, 488, 19, 35, 131, 25, 73, 137, 521, 529, 97, 545, 193, 577, 22, 38, 390, 518, 146, 530, 162, 546, 276, 532, 100, 292, 548, 324, 580, 152, 536, 200, 328, 392, 776, 400, 784, 224, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_563, vertices_227, vertices_613, vertices_537, vertices_201, vertices_841, vertices_406, vertices_534, vertices_422, vertices_550, vertices_852, vertices_356, vertices_920, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_25, vertices_73, vertices_137, vertices_521, vertices_529, vertices_97, vertices_545, vertices_193, vertices_577, vertices_22, vertices_38, vertices_390, vertices_518, vertices_146, vertices_530, vertices_162, vertices_546, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_152, vertices_536, vertices_200, vertices_328, vertices_392, vertices_776, vertices_400, vertices_784, vertices_224, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_563), (false, vertices_227), (false, vertices_613), (false, vertices_537), (false, vertices_201), (false, vertices_841), (true, vertices_22), (true, vertices_38), (true, vertices_390), (true, vertices_518), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_324), (true, vertices_392), (true, vertices_400), (true, vertices_784), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 18 else
  if p.val = (false, vertices_563) then 19 else
  if p.val = (false, vertices_227) then 20 else
  if p.val = (false, vertices_613) then 15 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_38) then 3 else
  if p.val = (true, vertices_390) then 16 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 1 537 0 201 22 38 518 276 532 292 324 392 400 784 352 416 613 390 155 563 227 841
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_4 1 1 3 5 7 8 852 276 2
cert_row_4 2 2 3 6 7 8 920 152 3
cert_row_4 3 2 4 5 6 7 488 200 1
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 22 406 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 422
cert_cover_5 2 0 0 1 4 6 38 422 3
cert_coverFacet 3 550
cert_cover_2 3 1 0 4 8 38 550 3
cert_coverFacet 4 852
cert_cover_5 4 1 1 3 5 7 276 852 2
cert_coverFacet 5 356
cert_cover_2 5 4 1 5 7 100 356 3
cert_coverFacet 6 920
cert_cover_5 6 2 2 3 6 7 152 920 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 200 488 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0485

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0486.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0486

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 613, 421, 233, 465, 833, 158, 174, 278, 550, 570, 850, 404, 728, 616, 37, 261, 517, 97, 161, 193, 321, 577, 385, 769, 142, 22, 38, 262, 518, 26, 42, 274, 530, 546, 770, 148, 276, 164, 548, 388, 152, 536, 104, 168, 552, 200, 584, 208, 336, 592, 400, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_613, vertices_421, vertices_233, vertices_465, vertices_833, vertices_158, vertices_174, vertices_278, vertices_550, vertices_570, vertices_850, vertices_404, vertices_728, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_97, vertices_161, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_142, vertices_22, vertices_38, vertices_262, vertices_518, vertices_26, vertices_42, vertices_274, vertices_530, vertices_546, vertices_770, vertices_148, vertices_276, vertices_164, vertices_548, vertices_388, vertices_152, vertices_536, vertices_104, vertices_168, vertices_552, vertices_200, vertices_584, vertices_208, vertices_336, vertices_592, vertices_400, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_613), (false, vertices_421), (false, vertices_233), (false, vertices_465), (false, vertices_833), (true, vertices_142), (true, vertices_22), (true, vertices_38), (true, vertices_26), (true, vertices_42), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_148), (true, vertices_276), (true, vertices_152), (true, vertices_536), (true, vertices_552), (true, vertices_584), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_142) then 17 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 833 22 38 26 42 274 530 546 148 276 152 536 552 584 592 775 142 613 421 233 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 6 142
cert_row_4 1 0 2 3 4 8 570 26 3
cert_row_4 2 0 3 5 7 8 850 274 2
cert_row_4 3 2 3 5 6 8 728 152 2
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 142 158 3
cert_coverFacet 1 174
cert_cover_5 1 0 0 1 2 4 142 174 3
cert_coverFacet 2 278
cert_cover_2 2 1 0 3 7 22 278 3
cert_coverFacet 3 550
cert_cover_2 3 1 0 4 8 38 550 3
cert_coverFacet 4 570
cert_cover_5 4 1 0 2 3 4 26 570 3
cert_coverFacet 5 850
cert_cover_5 5 2 0 3 5 7 274 850 2
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 728
cert_cover_5 7 3 2 3 5 6 152 728 2
cert_coverFacet 8 616
cert_cover_2 8 4 2 5 8 104 616 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0486

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0487.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0487

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 93, 781, 229, 549, 537, 721, 806, 666, 282, 778, 242, 370, 364, 344, 13, 37, 69, 517, 25, 521, 81, 529, 161, 545, 193, 641, 26, 266, 522, 114, 146, 274, 162, 290, 546, 642, 770, 76, 268, 100, 292, 548, 772, 88, 280, 536, 328, 776, 208, 336, 656, 224, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_93, vertices_781, vertices_229, vertices_549, vertices_537, vertices_721, vertices_806, vertices_666, vertices_282, vertices_778, vertices_242, vertices_370, vertices_364, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_517, vertices_25, vertices_521, vertices_81, vertices_529, vertices_161, vertices_545, vertices_193, vertices_641, vertices_26, vertices_266, vertices_522, vertices_114, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_76, vertices_268, vertices_100, vertices_292, vertices_548, vertices_772, vertices_88, vertices_280, vertices_536, vertices_328, vertices_776, vertices_208, vertices_336, vertices_656, vertices_224, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_93), (false, vertices_781), (false, vertices_229), (false, vertices_549), (false, vertices_537), (false, vertices_721), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_114), (true, vertices_146), (true, vertices_274), (true, vertices_290), (true, vertices_770), (true, vertices_292), (true, vertices_280), (true, vertices_328), (true, vertices_336), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_229) then 20 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_114) then 16 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
cert_nodeAtPriority_15 0 549 1 537 26 266 522 146 274 290 770 292 280 328 336 352 675 114 93 781 229 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 26 3
cert_row_2 1 0 3 4 5 114
cert_row_4 2 0 1 4 7 8 806 290 1
cert_row_4 3 1 2 4 5 7 364 76 2
cert_rows
cert_pivot_2 6 3 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 2 0 1 4 7 290 806 1
cert_coverFacet 1 666
cert_cover_5 1 0 0 2 3 6 26 666 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 242
cert_cover_5 4 1 0 3 4 6 114 242 3
cert_coverFacet 5 370
cert_cover_5 5 1 0 3 4 7 114 370 3
cert_coverFacet 6 364
cert_cover_5 6 3 1 2 4 5 76 364 2
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0487

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0488.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0488

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 613, 313, 601, 233, 801, 398, 214, 598, 806, 154, 282, 484, 216, 424, 25, 41, 73, 273, 529, 97, 289, 545, 577, 769, 86, 134, 262, 518, 26, 138, 266, 146, 274, 530, 770, 100, 292, 548, 196, 580, 388, 88, 152, 280, 168, 296, 200, 392, 208, 592, 224, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_613, vertices_313, vertices_601, vertices_233, vertices_801, vertices_398, vertices_214, vertices_598, vertices_806, vertices_154, vertices_282, vertices_484, vertices_216, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_73, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_577, vertices_769, vertices_86, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_770, vertices_100, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_88, vertices_152, vertices_280, vertices_168, vertices_296, vertices_200, vertices_392, vertices_208, vertices_592, vertices_224, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_613), (false, vertices_313), (false, vertices_601), (false, vertices_233), (false, vertices_801), (true, vertices_86), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_292), (true, vertices_196), (true, vertices_388), (true, vertices_152), (true, vertices_392), (true, vertices_208), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_601) then 22 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_86) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_146) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 1 2 6 7 398 134 2
cert_row_4 2 0 1 4 7 8 806 262 2
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 134 398 2
cert_coverFacet 1 214
cert_cover_5 1 0 0 1 3 6 86 214 3
cert_coverFacet 2 598
cert_cover_5 2 0 0 1 3 8 86 598 3
cert_coverFacet 3 806
cert_cover_5 3 2 0 1 4 7 262 806 2
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 282
cert_cover_2 5 2 0 3 7 26 282 3
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 100 484 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0488

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0489.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0489

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 541, 309, 613, 793, 481, 654, 154, 282, 778, 466, 738, 188, 676, 432, 21, 37, 517, 537, 273, 97, 289, 321, 577, 769, 26, 138, 266, 522, 146, 274, 194, 322, 578, 642, 770, 28, 140, 524, 52, 164, 548, 644, 152, 280, 776, 176, 304, 400, 224, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_541, vertices_309, vertices_613, vertices_793, vertices_481, vertices_654, vertices_154, vertices_282, vertices_778, vertices_466, vertices_738, vertices_188, vertices_676, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_517, vertices_537, vertices_273, vertices_97, vertices_289, vertices_321, vertices_577, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_140, vertices_524, vertices_52, vertices_164, vertices_548, vertices_644, vertices_152, vertices_280, vertices_776, vertices_176, vertices_304, vertices_400, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_541), (false, vertices_309), (false, vertices_613), (false, vertices_793), (false, vertices_481), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_194), (true, vertices_642), (true, vertices_140), (true, vertices_164), (true, vertices_644), (true, vertices_152), (true, vertices_176), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_541) then 21 else
  if p.val = (false, vertices_309) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_793) then 22 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 7 466 146 2
cert_row_4 1 0 4 5 6 8 738 194 1
cert_row_4 2 0 1 2 6 8 654 138 1
cert_row_4 3 1 2 3 4 6 188 28 3
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 138 654 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 466
cert_cover_5 4 0 0 3 5 6 146 466 2
cert_coverFacet 5 738
cert_cover_5 5 1 0 4 5 6 194 738 1
cert_coverFacet 6 188
cert_cover_5 6 3 1 2 3 4 28 188 3
cert_coverFacet 7 676
cert_cover_2 7 4 1 6 8 164 676 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0489

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0490.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0490

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 115, 675, 771, 901, 337, 481, 782, 58, 554, 604, 284, 468, 740, 632, 19, 35, 259, 515, 81, 273, 97, 161, 321, 385, 641, 769, 26, 42, 266, 522, 50, 546, 770, 28, 268, 524, 84, 276, 196, 580, 388, 644, 772, 56, 600, 280, 552, 112, 336, 224, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_115, vertices_675, vertices_771, vertices_901, vertices_337, vertices_481, vertices_782, vertices_58, vertices_554, vertices_604, vertices_284, vertices_468, vertices_740, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_515, vertices_81, vertices_273, vertices_97, vertices_161, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_546, vertices_770, vertices_28, vertices_268, vertices_524, vertices_84, vertices_276, vertices_196, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_600, vertices_280, vertices_552, vertices_112, vertices_336, vertices_224, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_115), (false, vertices_675), (false, vertices_771), (false, vertices_901), (false, vertices_337), (false, vertices_481), (true, vertices_42), (true, vertices_522), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_276), (true, vertices_196), (true, vertices_580), (true, vertices_56), (true, vertices_600), (true, vertices_552), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 15 else
  if p.val = (false, vertices_115) then 16 else
  if p.val = (false, vertices_675) then 17 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_337) then 1 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_600) then 21 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_600), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_2 1 2 3 5 8 600
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 1 4 5 6 8 740 196 1
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 604
cert_cover_5 3 1 1 2 3 5 28 604 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 468
cert_cover_5 5 2 1 3 5 6 84 468 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 196 740 1
cert_coverFacet 7 632
cert_cover_5 7 1 2 3 4 5 56 632 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0490

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0491.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0491

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 61, 409, 681, 625, 785, 206, 334, 394, 850, 738, 284, 172, 372, 228, 25, 41, 137, 49, 273, 529, 545, 385, 641, 769, 78, 138, 266, 194, 322, 578, 386, 642, 770, 28, 44, 140, 268, 52, 276, 100, 164, 196, 324, 280, 168, 392, 112, 336, 592, 784, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_61, vertices_409, vertices_681, vertices_625, vertices_785, vertices_206, vertices_334, vertices_394, vertices_850, vertices_738, vertices_284, vertices_172, vertices_372, vertices_228] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_137, vertices_49, vertices_273, vertices_529, vertices_545, vertices_385, vertices_641, vertices_769, vertices_78, vertices_138, vertices_266, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_140, vertices_268, vertices_52, vertices_276, vertices_100, vertices_164, vertices_196, vertices_324, vertices_280, vertices_168, vertices_392, vertices_112, vertices_336, vertices_592, vertices_784, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_61), (false, vertices_409), (false, vertices_681), (false, vertices_625), (false, vertices_785), (true, vertices_78), (true, vertices_138), (true, vertices_266), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_140), (true, vertices_268), (true, vertices_276), (true, vertices_100), (true, vertices_164), (true, vertices_196), (true, vertices_324), (true, vertices_336), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_61) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_324) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 785 138 266 194 322 578 140 268 276 100 164 196 324 336 224 899 78 61 409 681 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 4 5 6 8 738 194 1
cert_row_4 2 0 3 5 7 8 850 322 1
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 6 78 206 3
cert_coverFacet 1 334
cert_cover_5 1 0 0 1 2 7 78 334 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 850
cert_cover_5 3 2 0 3 5 7 322 850 1
cert_coverFacet 4 738
cert_cover_5 4 1 0 4 5 6 194 738 1
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 172
cert_cover_2 6 2 1 4 6 44 172 3
cert_coverFacet 7 372
cert_cover_5 7 3 1 3 4 5 52 372 3
cert_coverFacet 8 228
cert_cover_2 8 4 1 5 6 100 228 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0491

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3063 : Certifies 3063 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0462.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3064 : Certifies 3064 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0463.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3065 : Certifies 3065 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0464.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3066 : Certifies 3066 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0465.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3067 : Certifies 3067 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0466.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3068 : Certifies 3068 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0467.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3069 : Certifies 3069 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0468.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3070 : Certifies 3070 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0469.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3071 : Certifies 3071 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0470.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3072 : Certifies 3072 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0471.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3073 : Certifies 3073 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0472.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3074 : Certifies 3074 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0473.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3075 : Certifies 3075 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0474.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3076 : Certifies 3076 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0475.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3077 : Certifies 3077 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0476.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3078 : Certifies 3078 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0477.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3079 : Certifies 3079 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0478.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3080 : Certifies 3080 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0479.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3081 : Certifies 3081 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0480.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3082 : Certifies 3082 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0481.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3083 : Certifies 3083 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0482.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3084 : Certifies 3084 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0483.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3085 : Certifies 3085 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0484.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3086 : Certifies 3086 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0485.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3087 : Certifies 3087 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0486.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3088 : Certifies 3088 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0487.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3089 : Certifies 3089 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0488.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3090 : Certifies 3090 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0489.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3091 : Certifies 3091 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0490.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3092 : Certifies 3092 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0491.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B101 (j : Fin 30) :
    Certifies (3063 + j.val) := by
  fin_cases j
  · exact projection_3063
  · exact projection_3064
  · exact projection_3065
  · exact projection_3066
  · exact projection_3067
  · exact projection_3068
  · exact projection_3069
  · exact projection_3070
  · exact projection_3071
  · exact projection_3072
  · exact projection_3073
  · exact projection_3074
  · exact projection_3075
  · exact projection_3076
  · exact projection_3077
  · exact projection_3078
  · exact projection_3079
  · exact projection_3080
  · exact projection_3081
  · exact projection_3082
  · exact projection_3083
  · exact projection_3084
  · exact projection_3085
  · exact projection_3086
  · exact projection_3087
  · exact projection_3088
  · exact projection_3089
  · exact projection_3090
  · exact projection_3091
  · exact projection_3092

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
