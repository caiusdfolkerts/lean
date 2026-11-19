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
/- Source: ProjectionCertificates/R_m16e10q1_0467.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0467

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 523, 403, 675, 589, 661, 277, 298, 554, 482, 124, 316, 596, 744, 368, 976, 11, 131, 259, 515, 13, 21, 261, 517, 521, 145, 273, 641, 42, 266, 522, 162, 290, 546, 386, 60, 76, 268, 84, 276, 532, 580, 104, 296, 552, 584, 112, 304, 336, 592, 400, 656, 224, 352, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_523, vertices_403, vertices_675, vertices_589, vertices_661, vertices_277, vertices_298, vertices_554, vertices_482, vertices_124, vertices_316, vertices_596, vertices_744, vertices_368, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_131, vertices_259, vertices_515, vertices_13, vertices_21, vertices_261, vertices_517, vertices_521, vertices_145, vertices_273, vertices_641, vertices_42, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_60, vertices_76, vertices_268, vertices_84, vertices_276, vertices_532, vertices_580, vertices_104, vertices_296, vertices_552, vertices_584, vertices_112, vertices_304, vertices_336, vertices_592, vertices_400, vertices_656, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_523), (false, vertices_403), (false, vertices_675), (false, vertices_589), (false, vertices_661), (false, vertices_277), (true, vertices_42), (true, vertices_290), (true, vertices_60), (true, vertices_84), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_112), (true, vertices_304), (true, vertices_336), (true, vertices_592), (true, vertices_224), (true, vertices_352), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 24 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 17 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_403) then 18 else
  if p.val = (false, vertices_675) then 19 else
  if p.val = (false, vertices_589) then 21 else
  if p.val = (false, vertices_661) then 22 else
  if p.val = (false, vertices_277) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_60) then 23 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_448) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
cert_nodeAtPriority_6 523 277 42 290 84 104 296 552 112 304 336 592 224 352 448 704 271 403 675 589 661 60
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 4 5 6 7 482 162 2
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 5 6 7 8 976 336 2
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 298
cert_cover_2 0 2 0 4 7 42 298 3
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 482
cert_cover_5 2 1 0 4 5 6 162 482 2
cert_coverFacet 3 124
cert_cover_5 3 0 1 2 3 5 60 124 3
cert_coverFacet 4 316
cert_cover_5 4 0 1 2 3 7 60 316 3
cert_coverFacet 5 596
cert_cover_2 5 3 1 5 8 84 596 3
cert_coverFacet 6 744
cert_cover_5 6 2 2 4 5 6 104 744 3
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coverFacet 8 976
cert_cover_5 8 3 3 5 6 7 336 976 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0467

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0468.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0468

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 403, 643, 557, 313, 241, 673, 838, 738, 450, 60, 220, 460, 780, 628, 408, 131, 259, 515, 41, 265, 521, 49, 145, 273, 161, 545, 641, 194, 322, 578, 386, 642, 770, 28, 44, 204, 268, 524, 52, 84, 548, 324, 580, 772, 56, 152, 280, 392, 776, 112, 208, 400, 224, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_403, vertices_643, vertices_557, vertices_313, vertices_241, vertices_673, vertices_838, vertices_738, vertices_450, vertices_60, vertices_220, vertices_460, vertices_780, vertices_628, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_41, vertices_265, vertices_521, vertices_49, vertices_145, vertices_273, vertices_161, vertices_545, vertices_641, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_204, vertices_268, vertices_524, vertices_52, vertices_84, vertices_548, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_392, vertices_776, vertices_112, vertices_208, vertices_400, vertices_224, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_403), (false, vertices_643), (false, vertices_557), (false, vertices_313), (false, vertices_241), (false, vertices_673), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_28), (true, vertices_204), (true, vertices_268), (true, vertices_52), (true, vertices_84), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_152), (true, vertices_392), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_403) then 18 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_557) then 20 else
  if p.val = (false, vertices_313) then 23 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (false, vertices_673) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_204) then 21 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_608) then 14 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
cert_nodeAtPriority_61 0 643 1 673 194 322 578 28 268 52 84 324 580 772 152 392 608 448 779 403 557 204 313 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 6 204
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 738
cert_cover_5 1 2 0 4 5 6 194 738 1
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 220
cert_cover_5 4 0 1 2 3 5 28 220 3
cert_coverFacet 5 460
cert_cover_5 5 0 1 2 5 7 204 460 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 628
cert_cover_5 7 3 1 3 4 5 52 628 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0468

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0469.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0469

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 61, 269, 357, 793, 561, 737, 398, 218, 602, 778, 482, 156, 692, 420, 720, 13, 37, 261, 25, 265, 49, 529, 97, 545, 321, 577, 769, 90, 138, 266, 522, 194, 322, 578, 386, 770, 28, 140, 268, 52, 148, 164, 292, 388, 152, 536, 776, 560, 208, 592, 656, 224, 352, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_61, vertices_269, vertices_357, vertices_793, vertices_561, vertices_737, vertices_398, vertices_218, vertices_602, vertices_778, vertices_482, vertices_156, vertices_692, vertices_420, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_261, vertices_25, vertices_265, vertices_49, vertices_529, vertices_97, vertices_545, vertices_321, vertices_577, vertices_769, vertices_90, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_28, vertices_140, vertices_268, vertices_52, vertices_148, vertices_164, vertices_292, vertices_388, vertices_152, vertices_536, vertices_776, vertices_560, vertices_208, vertices_592, vertices_656, vertices_224, vertices_352, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_61), (false, vertices_269), (false, vertices_357), (false, vertices_793), (false, vertices_561), (false, vertices_737), (true, vertices_90), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_194), (true, vertices_386), (true, vertices_140), (true, vertices_148), (true, vertices_164), (true, vertices_388), (true, vertices_152), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_61) then 20 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (false, vertices_793) then 23 else
  if p.val = (false, vertices_561) then 1 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_90) then 18 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 1 269 0 561 138 266 522 194 386 140 148 164 388 152 208 592 656 416 835 90 61 357 793 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 6 8 692 52 3
cert_row_2 1 0 2 3 5 90
cert_row_4 2 0 1 2 6 7 398 138 1
cert_row_4 3 0 4 5 6 7 482 194 1
cert_rows
cert_pivot_2 8 3 1 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 2 0 1 2 6 138 398 1
cert_coverFacet 1 218
cert_cover_5 1 1 0 2 3 6 90 218 3
cert_coverFacet 2 602
cert_cover_5 2 1 0 2 3 8 90 602 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 482
cert_cover_5 4 3 0 4 5 6 194 482 1
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 692
cert_cover_5 6 0 1 3 4 6 52 692 3
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coverFacet 8 720
cert_cover_2 8 5 3 6 8 208 720 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0469

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0470.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0470

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 781, 677, 197, 325, 569, 425, 214, 122, 362, 690, 418, 852, 660, 600, 840, 69, 133, 261, 517, 41, 265, 521, 161, 545, 193, 321, 385, 106, 50, 82, 146, 162, 290, 194, 322, 386, 84, 148, 532, 196, 324, 644, 772, 56, 88, 536, 296, 328, 584, 776, 560, 592, 656, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_781, vertices_677, vertices_197, vertices_325, vertices_569, vertices_425, vertices_214, vertices_122, vertices_362, vertices_690, vertices_418, vertices_852, vertices_660, vertices_600, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_517, vertices_41, vertices_265, vertices_521, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_106, vertices_50, vertices_82, vertices_146, vertices_162, vertices_290, vertices_194, vertices_322, vertices_386, vertices_84, vertices_148, vertices_532, vertices_196, vertices_324, vertices_644, vertices_772, vertices_56, vertices_88, vertices_536, vertices_296, vertices_328, vertices_584, vertices_776, vertices_560, vertices_592, vertices_656, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_781), (false, vertices_677), (false, vertices_197), (false, vertices_325), (false, vertices_569), (false, vertices_425), (true, vertices_106), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_162), (true, vertices_290), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_88), (true, vertices_328), (true, vertices_584), (true, vertices_592), (true, vertices_656), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 17 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_325) then 1 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_425) then 24 else
  if p.val = (true, vertices_106) then 18 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_832) then 15 else
  0
cert_priority
cert_nodeAtPriority_39 0 197 1 325 50 82 146 162 290 84 148 532 88 328 584 592 656 832 451 106 781 677 569 425
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 3 4 6 8 690 50 3
cert_row_4 2 0 1 3 5 6 214 82 1
cert_row_4 3 1 3 5 7 8 852 84 3
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 2 0 1 3 5 82 214 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 4 106 122 2
cert_coverFacet 2 362
cert_cover_5 2 0 0 2 4 7 106 362 3
cert_coverFacet 3 690
cert_cover_5 3 1 0 3 4 6 50 690 3
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 852
cert_cover_5 5 3 1 3 5 7 84 852 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coverFacet 8 840
cert_cover_2 8 5 2 7 8 328 840 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0470

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0471.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0471

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 587, 565, 681, 241, 849, 398, 794, 482, 834, 284, 540, 652, 372, 420, 676, 75, 137, 521, 49, 81, 529, 161, 545, 193, 577, 138, 266, 522, 194, 322, 578, 386, 770, 28, 140, 268, 524, 52, 276, 532, 164, 292, 548, 388, 644, 280, 536, 648, 112, 336, 784, 224, 352, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_587, vertices_565, vertices_681, vertices_241, vertices_849, vertices_398, vertices_794, vertices_482, vertices_834, vertices_284, vertices_540, vertices_652, vertices_372, vertices_420, vertices_676] (by decide +kernel)
  polygons := literalFinset [vertices_75, vertices_137, vertices_521, vertices_49, vertices_81, vertices_529, vertices_161, vertices_545, vertices_193, vertices_577, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_28, vertices_140, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_280, vertices_536, vertices_648, vertices_112, vertices_336, vertices_784, vertices_224, vertices_352, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_587), (false, vertices_565), (false, vertices_681), (false, vertices_241), (false, vertices_849), (true, vertices_266), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_164), (true, vertices_292), (true, vertices_388), (true, vertices_644), (true, vertices_280), (true, vertices_536), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 18 else
  if p.val = (false, vertices_587) then 19 else
  if p.val = (false, vertices_565) then 21 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (false, vertices_849) then 26 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_644) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_536) then 14 else
  if p.val = (true, vertices_352) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 7 8 794 266 2
cert_row_4 1 0 1 2 6 7 398 138 1
cert_row_4 2 0 4 5 6 7 482 194 1
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 8 2 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 138 398 1
cert_coverFacet 1 794
cert_cover_5 1 0 0 2 3 7 266 794 2
cert_coverFacet 2 482
cert_cover_5 2 2 0 4 5 6 194 482 1
cert_coverFacet 3 834
cert_cover_2 3 5 0 7 8 322 834 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 372
cert_cover_5 7 3 1 3 4 5 52 372 3
cert_coverFacet 8 420
cert_cover_2 8 4 1 6 7 164 420 3
cert_coverFacet 9 676
cert_cover_2 9 4 1 6 8 164 676 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0471

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0472.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0472

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 541, 109, 165, 585, 721, 481, 398, 526, 534, 810, 466, 786, 428, 616, 880, 13, 21, 37, 133, 73, 521, 145, 529, 97, 161, 193, 577, 14, 22, 134, 518, 266, 522, 146, 274, 530, 386, 770, 44, 396, 524, 532, 164, 104, 296, 552, 584, 208, 336, 592, 784, 352, 608, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_541, vertices_109, vertices_165, vertices_585, vertices_721, vertices_481, vertices_398, vertices_526, vertices_534, vertices_810, vertices_466, vertices_786, vertices_428, vertices_616, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_37, vertices_133, vertices_73, vertices_521, vertices_145, vertices_529, vertices_97, vertices_161, vertices_193, vertices_577, vertices_14, vertices_22, vertices_134, vertices_518, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_770, vertices_44, vertices_396, vertices_524, vertices_532, vertices_164, vertices_104, vertices_296, vertices_552, vertices_584, vertices_208, vertices_336, vertices_592, vertices_784, vertices_352, vertices_608, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_541), (false, vertices_109), (false, vertices_165), (false, vertices_585), (false, vertices_721), (false, vertices_481), (true, vertices_14), (true, vertices_518), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_770), (true, vertices_396), (true, vertices_296), (true, vertices_552), (true, vertices_336), (true, vertices_784), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 21 24 18 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 17 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_109) then 22 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_585) then 1 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_396) then 23 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_608) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 23 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 24 => Sum.inl 2
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 2 4 7 8 810 266 2
cert_row_4 2 0 3 5 6 7 466 146 2
cert_row_4 3 3 4 5 7 8 880 336 1
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 810
cert_cover_5 3 1 0 2 4 7 266 810 2
cert_coverFacet 4 466
cert_cover_5 4 2 0 3 5 6 146 466 2
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 428
cert_cover_5 6 0 1 2 4 6 44 428 3
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coverFacet 8 880
cert_cover_5 8 3 3 4 5 7 336 880 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0472

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0473.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0473

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 709, 601, 281, 233, 689, 305, 590, 790, 454, 106, 778, 482, 436, 660, 792, 25, 41, 73, 265, 49, 273, 529, 161, 289, 193, 577, 641, 70, 262, 518, 42, 74, 266, 522, 98, 290, 450, 770, 148, 276, 532, 196, 580, 388, 644, 280, 536, 104, 584, 776, 176, 304, 656, 784, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_709, vertices_601, vertices_281, vertices_233, vertices_689, vertices_305, vertices_590, vertices_790, vertices_454, vertices_106, vertices_778, vertices_482, vertices_436, vertices_660, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_73, vertices_265, vertices_49, vertices_273, vertices_529, vertices_161, vertices_289, vertices_193, vertices_577, vertices_641, vertices_70, vertices_262, vertices_518, vertices_42, vertices_74, vertices_266, vertices_522, vertices_98, vertices_290, vertices_450, vertices_770, vertices_148, vertices_276, vertices_532, vertices_196, vertices_580, vertices_388, vertices_644, vertices_280, vertices_536, vertices_104, vertices_584, vertices_776, vertices_176, vertices_304, vertices_656, vertices_784, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_709), (false, vertices_601), (false, vertices_281), (false, vertices_233), (false, vertices_689), (false, vertices_305), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_74), (true, vertices_522), (true, vertices_98), (true, vertices_450), (true, vertices_770), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_388), (true, vertices_776), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 17 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_601) then 22 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_689) then 25 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_450) then 18 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_450), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 70 2
cert_row_2 1 0 5 6 7 450
cert_row_4 2 0 1 3 7 8 790 262 2
cert_row_4 3 1 3 4 6 7 436 148 2
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 70 590 2
cert_coverFacet 1 790
cert_cover_5 1 2 0 1 3 7 262 790 2
cert_coverFacet 2 454
cert_cover_5 2 1 0 1 5 6 70 454 3
cert_coverFacet 3 106
cert_cover_2 3 2 0 4 5 42 106 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 482
cert_cover_5 5 1 0 4 5 6 98 482 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 148 436 2
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 792
cert_cover_2 8 3 2 7 8 280 792 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0473

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0474.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0474

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 227, 387, 771, 781, 361, 465, 790, 178, 562, 402, 348, 716, 692, 212, 744, 35, 131, 259, 515, 41, 265, 521, 97, 193, 321, 385, 769, 50, 146, 274, 530, 162, 546, 386, 770, 76, 268, 524, 84, 148, 276, 532, 196, 644, 772, 104, 552, 712, 328, 176, 560, 208, 336, 400, 224, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_227, vertices_387, vertices_771, vertices_781, vertices_361, vertices_465, vertices_790, vertices_178, vertices_562, vertices_402, vertices_348, vertices_716, vertices_692, vertices_212, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_41, vertices_265, vertices_521, vertices_97, vertices_193, vertices_321, vertices_385, vertices_769, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_386, vertices_770, vertices_76, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_644, vertices_772, vertices_104, vertices_552, vertices_712, vertices_328, vertices_176, vertices_560, vertices_208, vertices_336, vertices_400, vertices_224, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_227), (false, vertices_387), (false, vertices_771), (false, vertices_781), (false, vertices_361), (false, vertices_465), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_76), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_196), (true, vertices_644), (true, vertices_712), (true, vertices_176), (true, vertices_560), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 17 else
  if p.val = (false, vertices_227) then 18 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_644) then 12 else
  if p.val = (true, vertices_712) then 23 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 23 => Sum.inr ⟨(true, vertices_712), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_4 1 1 2 3 5 7 348 76 2
cert_row_2 2 2 5 6 8 712
cert_row_4 3 1 3 4 6 8 692 148 2
cert_rows
cert_pivot_2 0 7 2 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 178
cert_cover_2 1 3 0 4 6 50 178 3
cert_coverFacet 2 562
cert_cover_2 2 3 0 4 8 50 562 3
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 348
cert_cover_5 4 1 1 2 3 5 76 348 2
cert_coverFacet 5 716
cert_cover_5 5 2 1 2 5 6 76 716 3
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 148 692 2
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coverFacet 8 744
cert_cover_5 8 2 2 4 5 6 104 744 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0474

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0475.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0475

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 541, 173, 805, 601, 361, 678, 346, 434, 210, 802, 706, 156, 724, 408, 424, 13, 37, 517, 537, 41, 73, 289, 321, 577, 769, 82, 146, 274, 162, 290, 546, 194, 322, 578, 642, 770, 28, 140, 148, 532, 164, 548, 644, 88, 152, 280, 168, 296, 328, 392, 208, 592, 400, 416, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_541, vertices_173, vertices_805, vertices_601, vertices_361, vertices_678, vertices_346, vertices_434, vertices_210, vertices_802, vertices_706, vertices_156, vertices_724, vertices_408, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_517, vertices_537, vertices_41, vertices_73, vertices_289, vertices_321, vertices_577, vertices_769, vertices_82, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_140, vertices_148, vertices_532, vertices_164, vertices_548, vertices_644, vertices_88, vertices_152, vertices_280, vertices_168, vertices_296, vertices_328, vertices_392, vertices_208, vertices_592, vertices_400, vertices_416, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_541), (false, vertices_173), (false, vertices_805), (false, vertices_601), (false, vertices_361), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_194), (true, vertices_642), (true, vertices_148), (true, vertices_644), (true, vertices_152), (true, vertices_280), (true, vertices_392), (true, vertices_208), (true, vertices_400), (true, vertices_416), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_541) then 23 else
  if p.val = (false, vertices_173) then 20 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_601) then 24 else
  if p.val = (false, vertices_361) then 25 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_416) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 7 346 82 1
cert_row_4 1 0 3 4 6 7 434 146 2
cert_row_4 2 0 1 4 6 8 678 162 1
cert_row_4 3 1 3 5 6 8 724 148 2
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 162 678 1
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 5 82 346 1
cert_coverFacet 2 434
cert_cover_5 2 1 0 3 4 6 146 434 2
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 156
cert_cover_2 6 2 1 3 6 28 156 3
cert_coverFacet 7 724
cert_cover_5 7 3 1 3 5 6 148 724 2
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 424
cert_cover_2 9 4 2 6 7 168 424 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0475

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0476.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0476

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 653, 269, 457, 849, 737, 62, 286, 614, 242, 594, 786, 556, 440, 680, 464, 13, 261, 517, 137, 265, 193, 321, 577, 641, 769, 30, 38, 262, 518, 50, 82, 274, 530, 98, 578, 770, 44, 268, 524, 548, 56, 280, 168, 552, 392, 648, 176, 208, 336, 592, 400, 784, 224, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_653, vertices_269, vertices_457, vertices_849, vertices_737, vertices_62, vertices_286, vertices_614, vertices_242, vertices_594, vertices_786, vertices_556, vertices_440, vertices_680, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_261, vertices_517, vertices_137, vertices_265, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_30, vertices_38, vertices_262, vertices_518, vertices_50, vertices_82, vertices_274, vertices_530, vertices_98, vertices_578, vertices_770, vertices_44, vertices_268, vertices_524, vertices_548, vertices_56, vertices_280, vertices_168, vertices_552, vertices_392, vertices_648, vertices_176, vertices_208, vertices_336, vertices_592, vertices_400, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_653), (false, vertices_269), (false, vertices_457), (false, vertices_849), (false, vertices_737), (true, vertices_30), (true, vertices_38), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_578), (true, vertices_44), (true, vertices_548), (true, vertices_56), (true, vertices_280), (true, vertices_168), (true, vertices_552), (true, vertices_176), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 18 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (false, vertices_849) then 25 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_30) then 19 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
cert_nodeAtPriority_66 269 38 50 82 274 530 98 578 44 548 56 280 168 552 176 208 400 775 30 653 457 849 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 8 614 38 3
cert_row_2 1 0 1 2 3 30
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 8 1 0 2
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 1 0 1 2 4 30 62 3
cert_coverFacet 1 286
cert_cover_5 1 1 0 1 2 7 30 286 3
cert_coverFacet 2 614
cert_cover_5 2 0 0 1 4 5 38 614 3
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 50 242 3
cert_coverFacet 4 594
cert_cover_2 4 3 0 5 8 82 594 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 440
cert_cover_5 7 3 2 3 4 6 56 440 3
cert_coverFacet 8 680
cert_cover_2 8 4 2 6 8 168 680 3
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0476

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0477.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0477

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 675, 835, 597, 357, 549, 417, 662, 154, 282, 786, 124, 188, 676, 856, 488, 131, 259, 515, 37, 69, 517, 161, 289, 545, 321, 577, 385, 26, 138, 266, 146, 274, 530, 642, 770, 60, 84, 148, 532, 100, 164, 548, 644, 88, 152, 280, 104, 168, 328, 392, 592, 784, 352, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_675, vertices_835, vertices_597, vertices_357, vertices_549, vertices_417, vertices_662, vertices_154, vertices_282, vertices_786, vertices_124, vertices_188, vertices_676, vertices_856, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_37, vertices_69, vertices_517, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_26, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_60, vertices_84, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_644, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_328, vertices_392, vertices_592, vertices_784, vertices_352, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_675), (false, vertices_835), (false, vertices_597), (false, vertices_357), (false, vertices_549), (false, vertices_417), (true, vertices_26), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_60), (true, vertices_148), (true, vertices_164), (true, vertices_644), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_104), (true, vertices_168), (true, vertices_328), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 24 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 17 else
  if p.val = (false, vertices_675) then 18 else
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_597) then 21 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_417) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_60) then 23 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_328) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
cert_nodeAtPriority_6 549 417 26 146 274 530 148 164 644 88 152 280 104 168 328 784 395 675 835 597 357 60
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 3 5 7 8 856 88 3
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 124
cert_cover_5 4 1 1 2 3 5 60 124 3
cert_coverFacet 5 188
cert_cover_5 5 1 1 2 3 6 60 188 3
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 856
cert_cover_5 7 2 2 3 5 7 88 856 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 104 488 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0477

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0478.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0478

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 179, 403, 611, 841, 481, 542, 278, 562, 156, 236, 332, 780, 468, 696, 616, 147, 35, 259, 515, 97, 161, 321, 577, 385, 769, 22, 262, 518, 50, 274, 530, 546, 28, 76, 140, 268, 524, 148, 276, 196, 324, 772, 152, 536, 104, 168, 552, 328, 584, 776, 176, 560, 400, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_179, vertices_403, vertices_611, vertices_841, vertices_481, vertices_542, vertices_278, vertices_562, vertices_156, vertices_236, vertices_332, vertices_780, vertices_468, vertices_696, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_147, vertices_35, vertices_259, vertices_515, vertices_97, vertices_161, vertices_321, vertices_577, vertices_385, vertices_769, vertices_22, vertices_262, vertices_518, vertices_50, vertices_274, vertices_530, vertices_546, vertices_28, vertices_76, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_196, vertices_324, vertices_772, vertices_152, vertices_536, vertices_104, vertices_168, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_560, vertices_400, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_179), (false, vertices_403), (false, vertices_611), (false, vertices_841), (false, vertices_481), (true, vertices_22), (true, vertices_530), (true, vertices_28), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_196), (true, vertices_324), (true, vertices_152), (true, vertices_536), (true, vertices_104), (true, vertices_168), (true, vertices_552), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 17 23 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 18 else
  if p.val = (false, vertices_179) then 20 else
  if p.val = (false, vertices_403) then 21 else
  if p.val = (false, vertices_611) then 22 else
  if p.val = (false, vertices_841) then 24 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_104) then 13 else
  if p.val = (true, vertices_168) then 14 else
  if p.val = (true, vertices_552) then 15 else
  if p.val = (true, vertices_560) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 22 2
cert_row_4 1 1 3 5 6 7 468 148 2
cert_row_4 2 1 2 4 5 6 236 76 2
cert_row_4 3 2 3 4 6 8 696 152 2
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 22 542 2
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 562
cert_cover_2 2 3 0 4 8 50 562 3
cert_coverFacet 3 156
cert_cover_2 3 2 1 3 6 28 156 3
cert_coverFacet 4 236
cert_cover_5 4 2 1 2 4 5 76 236 2
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 468
cert_cover_5 7 1 1 3 5 6 148 468 2
cert_coverFacet 8 696
cert_cover_5 8 3 2 3 4 6 152 696 2
cert_coverFacet 9 616
cert_cover_2 9 4 2 5 8 104 616 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0478

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0479.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0479

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 267, 355, 837, 905, 625, 673, 158, 286, 690, 306, 716, 780, 372, 212, 720, 11, 35, 259, 137, 265, 97, 161, 545, 321, 577, 641, 769, 30, 138, 266, 50, 146, 274, 162, 290, 140, 268, 524, 84, 148, 276, 196, 324, 580, 772, 648, 776, 112, 304, 560, 208, 592, 656, 352, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_267, vertices_355, vertices_837, vertices_905, vertices_625, vertices_673, vertices_158, vertices_286, vertices_690, vertices_306, vertices_716, vertices_780, vertices_372, vertices_212, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_137, vertices_265, vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_641, vertices_769, vertices_30, vertices_138, vertices_266, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_140, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_196, vertices_324, vertices_580, vertices_772, vertices_648, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_592, vertices_656, vertices_352, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_267), (false, vertices_355), (false, vertices_837), (false, vertices_905), (false, vertices_625), (false, vertices_673), (true, vertices_30), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_196), (true, vertices_304), (true, vertices_208), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 17 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_355) then 18 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_905) then 23 else
  if p.val = (false, vertices_625) then 25 else
  if p.val = (false, vertices_673) then 1 else
  if p.val = (true, vertices_30) then 19 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_30), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 5 7 372 84 2
cert_row_4 1 0 3 4 6 8 690 50 3
cert_row_2 2 0 1 2 3 30
cert_row_4 3 1 2 5 6 8 716 140 2
cert_rows
cert_pivot_2 7 4 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 2 0 1 2 6 30 158 3
cert_coverFacet 1 286
cert_cover_5 1 2 0 1 2 7 30 286 3
cert_coverFacet 2 690
cert_cover_5 2 1 0 3 4 6 50 690 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 716
cert_cover_5 4 3 1 2 5 6 140 716 2
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 372
cert_cover_5 6 0 1 3 4 5 84 372 2
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coverFacet 8 720
cert_cover_2 8 5 3 6 8 208 720 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0479

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0480.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0480

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 29, 109, 405, 325, 569, 241, 782, 410, 666, 738, 834, 284, 556, 868, 688, 13, 21, 69, 261, 25, 41, 49, 145, 97, 193, 321, 385, 154, 266, 522, 194, 322, 578, 386, 642, 770, 28, 44, 268, 524, 276, 100, 548, 324, 772, 280, 536, 552, 176, 560, 400, 656, 224, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_29, vertices_109, vertices_405, vertices_325, vertices_569, vertices_241, vertices_782, vertices_410, vertices_666, vertices_738, vertices_834, vertices_284, vertices_556, vertices_868, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_69, vertices_261, vertices_25, vertices_41, vertices_49, vertices_145, vertices_97, vertices_193, vertices_321, vertices_385, vertices_154, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_524, vertices_276, vertices_100, vertices_548, vertices_324, vertices_772, vertices_280, vertices_536, vertices_552, vertices_176, vertices_560, vertices_400, vertices_656, vertices_224, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_29), (false, vertices_109), (false, vertices_405), (false, vertices_325), (false, vertices_569), (false, vertices_241), (true, vertices_154), (true, vertices_266), (true, vertices_522), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_268), (true, vertices_524), (true, vertices_548), (true, vertices_772), (true, vertices_280), (true, vertices_656), (true, vertices_608), (true, vertices_672), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 17 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_109) then 20 else
  if p.val = (false, vertices_405) then 21 else
  if p.val = (false, vertices_325) then 1 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (true, vertices_154) then 18 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_672) then 14 else
  if p.val = (true, vertices_832) then 15 else
  0
cert_priority
cert_nodeAtPriority_50 1 29 0 325 266 522 578 642 770 268 524 548 772 280 656 608 672 832 451 154 109 405 569 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 7 154 410 3
cert_coverFacet 2 666
cert_cover_5 2 0 0 2 3 8 154 666 3
cert_coverFacet 3 738
cert_cover_5 3 2 0 4 5 6 194 738 1
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 868
cert_cover_5 7 3 1 4 5 7 100 868 3
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0480

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0481.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0481

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 653, 313, 537, 689, 481, 94, 142, 230, 282, 850, 450, 604, 868, 676, 816, 25, 137, 265, 521, 49, 529, 161, 289, 385, 641, 14, 70, 134, 26, 138, 266, 82, 274, 194, 322, 386, 92, 140, 524, 100, 164, 548, 580, 644, 280, 536, 304, 560, 592, 784, 224, 352, 672, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_653, vertices_313, vertices_537, vertices_689, vertices_481, vertices_94, vertices_142, vertices_230, vertices_282, vertices_850, vertices_450, vertices_604, vertices_868, vertices_676, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_521, vertices_49, vertices_529, vertices_161, vertices_289, vertices_385, vertices_641, vertices_14, vertices_70, vertices_134, vertices_26, vertices_138, vertices_266, vertices_82, vertices_274, vertices_194, vertices_322, vertices_386, vertices_92, vertices_140, vertices_524, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_280, vertices_536, vertices_304, vertices_560, vertices_592, vertices_784, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_653), (false, vertices_313), (false, vertices_537), (false, vertices_689), (false, vertices_481), (true, vertices_14), (true, vertices_70), (true, vertices_134), (true, vertices_26), (true, vertices_82), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_92), (true, vertices_100), (true, vertices_164), (true, vertices_548), (true, vertices_580), (true, vertices_592), (true, vertices_784), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_653) then 20 else
  if p.val = (false, vertices_313) then 23 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_689) then 25 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_92) then 21 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_580) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_800) then 15 else
  if p.val = (true, vertices_832) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 5 92
cert_row_4 1 0 1 4 5 6 230 70 2
cert_row_4 2 0 3 5 7 8 850 82 3
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 14 94 3
cert_coverFacet 1 142
cert_cover_2 1 1 0 2 6 14 142 3
cert_coverFacet 2 230
cert_cover_5 2 1 0 1 4 5 70 230 2
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 850
cert_cover_5 4 2 0 3 5 7 82 850 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 604
cert_cover_5 6 0 1 2 3 8 92 604 3
cert_coverFacet 7 868
cert_cover_5 7 3 1 4 5 7 100 868 3
cert_coverFacet 8 676
cert_cover_2 8 4 1 6 8 164 676 3
cert_coverFacet 9 816
cert_cover_2 9 4 3 7 8 304 816 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0481

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0482.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0482

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 157, 541, 837, 721, 481, 558, 142, 774, 234, 818, 418, 376, 568, 216, 848, 29, 133, 261, 517, 145, 529, 193, 321, 577, 385, 14, 134, 262, 518, 42, 138, 162, 290, 546, 386, 770, 140, 524, 772, 56, 88, 152, 536, 104, 552, 200, 304, 560, 208, 336, 592, 784, 224, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_157, vertices_541, vertices_837, vertices_721, vertices_481, vertices_558, vertices_142, vertices_774, vertices_234, vertices_818, vertices_418, vertices_376, vertices_568, vertices_216, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_133, vertices_261, vertices_517, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_14, vertices_134, vertices_262, vertices_518, vertices_42, vertices_138, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_140, vertices_524, vertices_772, vertices_56, vertices_88, vertices_152, vertices_536, vertices_104, vertices_552, vertices_200, vertices_304, vertices_560, vertices_208, vertices_336, vertices_592, vertices_784, vertices_224, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_157), (false, vertices_541), (false, vertices_837), (false, vertices_721), (false, vertices_481), (true, vertices_14), (true, vertices_518), (true, vertices_42), (true, vertices_138), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_56), (true, vertices_88), (true, vertices_104), (true, vertices_552), (true, vertices_200), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 18 else
  if p.val = (false, vertices_157) then 20 else
  if p.val = (false, vertices_541) then 21 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_336) then 15 else
  if p.val = (true, vertices_784) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 14 3
cert_row_4 1 0 2 4 5 6 234 42 3
cert_row_4 2 0 3 4 7 8 818 290 1
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 14 558 3
cert_coverFacet 1 142
cert_cover_2 1 1 0 2 6 14 142 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 234
cert_cover_5 3 1 0 2 4 5 42 234 3
cert_coverFacet 4 818
cert_cover_5 4 2 0 3 4 7 290 818 1
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 56 376 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coverFacet 9 848
cert_cover_2 9 5 3 7 8 336 848 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0482

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0483.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0483

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 613, 421, 773, 121, 169, 457, 902, 346, 626, 402, 658, 572, 668, 172, 408, 37, 261, 517, 41, 73, 137, 97, 161, 321, 577, 385, 769, 82, 146, 274, 530, 322, 578, 386, 642, 770, 540, 44, 140, 164, 548, 388, 644, 772, 56, 88, 152, 280, 168, 328, 392, 112, 560, 400, 656, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_613, vertices_421, vertices_773, vertices_121, vertices_169, vertices_457, vertices_902, vertices_346, vertices_626, vertices_402, vertices_658, vertices_572, vertices_668, vertices_172, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_41, vertices_73, vertices_137, vertices_97, vertices_161, vertices_321, vertices_577, vertices_385, vertices_769, vertices_82, vertices_146, vertices_274, vertices_530, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_540, vertices_44, vertices_140, vertices_164, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_168, vertices_328, vertices_392, vertices_112, vertices_560, vertices_400, vertices_656, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_613), (false, vertices_421), (false, vertices_773), (false, vertices_121), (false, vertices_169), (false, vertices_457), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_540), (true, vertices_44), (true, vertices_140), (true, vertices_644), (true, vertices_152), (true, vertices_280), (true, vertices_560), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_121) then 23 else
  if p.val = (false, vertices_169) then 1 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_540) then 21 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_656) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_540), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_2 1 1 2 3 8 540
cert_row_4 2 0 2 3 5 7 346 82 1
cert_row_4 3 0 3 4 5 8 626 82 2
cert_rows
cert_pivot_2 6 1 2 0
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 346
cert_cover_5 1 2 0 2 3 5 82 346 1
cert_coverFacet 2 626
cert_cover_5 2 3 0 3 4 5 82 626 2
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 572
cert_cover_5 5 1 1 2 3 4 540 572 3
cert_coverFacet 6 668
cert_cover_5 6 1 1 2 3 6 540 668 3
cert_coverFacet 7 172
cert_cover_2 7 2 1 4 6 44 172 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0483

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0484.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0484

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 59, 523, 211, 301, 781, 181, 197, 282, 842, 338, 740, 804, 440, 976, 928, 11, 19, 67, 515, 269, 37, 69, 133, 517, 41, 521, 49, 145, 193, 26, 266, 522, 82, 274, 322, 578, 164, 292, 548, 196, 580, 772, 56, 280, 296, 776, 176, 208, 336, 400, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_59, vertices_523, vertices_211, vertices_301, vertices_781, vertices_181, vertices_197, vertices_282, vertices_842, vertices_338, vertices_740, vertices_804, vertices_440, vertices_976, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_67, vertices_515, vertices_269, vertices_37, vertices_69, vertices_133, vertices_517, vertices_41, vertices_521, vertices_49, vertices_145, vertices_193, vertices_26, vertices_266, vertices_522, vertices_82, vertices_274, vertices_322, vertices_578, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_772, vertices_56, vertices_280, vertices_296, vertices_776, vertices_176, vertices_208, vertices_336, vertices_400, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_59), (false, vertices_523), (false, vertices_211), (false, vertices_301), (false, vertices_781), (false, vertices_181), (false, vertices_197), (true, vertices_266), (true, vertices_274), (true, vertices_322), (true, vertices_548), (true, vertices_280), (true, vertices_336), (true, vertices_400), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 23 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 16 else
  if p.val = (false, vertices_59) then 17 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_211) then 18 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_181) then 22 else
  if p.val = (false, vertices_197) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_704) then 12 else
  if p.val = (true, vertices_832) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 266 2
cert_row_4 1 1 4 5 6 8 740 164 2
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 282
cert_cover_2 0 2 0 3 7 26 282 3
cert_coverFacet 1 842
cert_cover_5 1 0 0 2 5 7 266 842 2
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 740
cert_cover_5 3 1 1 4 5 6 164 740 2
cert_coverFacet 4 804
cert_cover_2 4 4 1 7 8 292 804 3
cert_coverFacet 5 440
cert_cover_5 5 2 2 3 4 6 56 440 3
cert_coverFacet 6 976
cert_cover_5 6 3 3 5 6 7 208 976 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0484

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0485.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0485

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 779, 611, 195, 61, 269, 229, 553, 850, 450, 668, 908, 180, 632, 496, 912, 67, 131, 259, 515, 13, 37, 133, 261, 41, 265, 521, 97, 545, 193, 194, 322, 578, 386, 770, 28, 652, 268, 52, 148, 164, 388, 56, 536, 552, 776, 112, 176, 336, 592, 400, 656, 784, 224, 608, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_779, vertices_611, vertices_195, vertices_61, vertices_269, vertices_229, vertices_553, vertices_850, vertices_450, vertices_668, vertices_908, vertices_180, vertices_632, vertices_496, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_13, vertices_37, vertices_133, vertices_261, vertices_41, vertices_265, vertices_521, vertices_97, vertices_545, vertices_193, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_28, vertices_652, vertices_268, vertices_52, vertices_148, vertices_164, vertices_388, vertices_56, vertices_536, vertices_552, vertices_776, vertices_112, vertices_176, vertices_336, vertices_592, vertices_400, vertices_656, vertices_784, vertices_224, vertices_608, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_779), (false, vertices_611), (false, vertices_195), (false, vertices_61), (false, vertices_269), (false, vertices_229), (false, vertices_553), (true, vertices_322), (true, vertices_652), (true, vertices_148), (true, vertices_536), (true, vertices_112), (true, vertices_176), (true, vertices_336), (true, vertices_592), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 23 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 16 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_611) then 18 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_61) then 20 else
  if p.val = (false, vertices_269) then 1 else
  if p.val = (false, vertices_229) then 21 else
  if p.val = (false, vertices_553) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_652) then 22 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_448) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 8 652
cert_row_4 1 0 3 5 7 8 850 322 1
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 850
cert_cover_5 0 1 0 3 5 7 322 850 1
cert_coverFacet 1 450
cert_cover_2 1 5 0 6 7 194 450 3
cert_coverFacet 2 668
cert_cover_5 2 0 1 2 3 6 28 668 3
cert_coverFacet 3 908
cert_cover_5 3 0 1 2 6 7 652 908 3
cert_coverFacet 4 180
cert_cover_2 4 3 1 4 6 52 180 3
cert_coverFacet 5 632
cert_cover_5 5 2 2 3 4 5 56 632 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coverFacet 7 912
cert_cover_2 7 6 3 7 8 400 912 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0485

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0486.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0486

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 519, 451, 771, 541, 241, 849, 398, 526, 810, 124, 428, 180, 600, 616, 992, 7, 131, 259, 515, 21, 517, 81, 145, 529, 193, 321, 769, 14, 134, 518, 266, 522, 386, 770, 28, 44, 396, 524, 52, 148, 164, 88, 536, 104, 296, 552, 584, 112, 176, 592, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_519, vertices_451, vertices_771, vertices_541, vertices_241, vertices_849, vertices_398, vertices_526, vertices_810, vertices_124, vertices_428, vertices_180, vertices_600, vertices_616, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_131, vertices_259, vertices_515, vertices_21, vertices_517, vertices_81, vertices_145, vertices_529, vertices_193, vertices_321, vertices_769, vertices_14, vertices_134, vertices_518, vertices_266, vertices_522, vertices_386, vertices_770, vertices_28, vertices_44, vertices_396, vertices_524, vertices_52, vertices_148, vertices_164, vertices_88, vertices_536, vertices_104, vertices_296, vertices_552, vertices_584, vertices_112, vertices_176, vertices_592, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_519), (false, vertices_451), (false, vertices_771), (false, vertices_541), (false, vertices_241), (false, vertices_849), (true, vertices_14), (true, vertices_266), (true, vertices_522), (true, vertices_44), (true, vertices_396), (true, vertices_52), (true, vertices_164), (true, vertices_88), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_584), (true, vertices_608), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 23 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 17 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_451) then 18 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_541) then 20 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (false, vertices_849) then 25 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_396) then 21 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_416) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 266 2
cert_row_4 1 1 2 3 4 5 124 28 3
cert_row_2 2 1 2 6 7 396
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 3 1 4
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 2 0 1 2 6 14 398 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 810
cert_cover_5 2 0 0 2 4 7 266 810 2
cert_coverFacet 3 124
cert_cover_5 3 1 1 2 3 4 28 124 3
cert_coverFacet 4 428
cert_cover_5 4 2 1 2 4 6 44 428 3
cert_coverFacet 5 180
cert_cover_2 5 3 1 4 6 52 180 3
cert_coverFacet 6 600
cert_cover_2 6 3 2 5 8 88 600 3
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coverFacet 8 992
cert_cover_5 8 3 4 5 6 7 224 992 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0486

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0487.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0487

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 709, 665, 281, 617, 241, 305, 590, 790, 454, 106, 778, 482, 436, 660, 792, 25, 41, 265, 521, 49, 145, 273, 97, 289, 193, 577, 641, 70, 262, 518, 42, 74, 266, 522, 98, 290, 450, 770, 148, 276, 532, 196, 580, 388, 644, 280, 536, 104, 584, 776, 176, 304, 656, 784, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_709, vertices_665, vertices_281, vertices_617, vertices_241, vertices_305, vertices_590, vertices_790, vertices_454, vertices_106, vertices_778, vertices_482, vertices_436, vertices_660, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_521, vertices_49, vertices_145, vertices_273, vertices_97, vertices_289, vertices_193, vertices_577, vertices_641, vertices_70, vertices_262, vertices_518, vertices_42, vertices_74, vertices_266, vertices_522, vertices_98, vertices_290, vertices_450, vertices_770, vertices_148, vertices_276, vertices_532, vertices_196, vertices_580, vertices_388, vertices_644, vertices_280, vertices_536, vertices_104, vertices_584, vertices_776, vertices_176, vertices_304, vertices_656, vertices_784, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_709), (false, vertices_665), (false, vertices_281), (false, vertices_617), (false, vertices_241), (false, vertices_305), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_74), (true, vertices_522), (true, vertices_98), (true, vertices_450), (true, vertices_770), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_388), (true, vertices_776), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 17 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_450) then 18 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_450), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 70 2
cert_row_2 1 0 5 6 7 450
cert_row_4 2 0 1 3 7 8 790 262 2
cert_row_4 3 1 3 4 6 7 436 148 2
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 70 590 2
cert_coverFacet 1 790
cert_cover_5 1 2 0 1 3 7 262 790 2
cert_coverFacet 2 454
cert_cover_5 2 1 0 1 5 6 70 454 3
cert_coverFacet 3 106
cert_cover_2 3 2 0 4 5 42 106 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 482
cert_cover_5 5 1 0 4 5 6 98 482 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 148 436 2
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 792
cert_cover_2 8 3 2 7 8 280 792 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0487

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0488.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0488

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [15, 551, 267, 899, 109, 425, 689, 286, 534, 850, 348, 244, 564, 232, 968, 720, 7, 11, 259, 515, 13, 37, 41, 265, 161, 545, 385, 641, 14, 22, 518, 266, 274, 530, 770, 284, 76, 52, 84, 532, 100, 548, 104, 168, 200, 328, 392, 176, 560, 208, 336, 592, 656, 224, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_15, vertices_551, vertices_267, vertices_899, vertices_109, vertices_425, vertices_689, vertices_286, vertices_534, vertices_850, vertices_348, vertices_244, vertices_564, vertices_232, vertices_968, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_515, vertices_13, vertices_37, vertices_41, vertices_265, vertices_161, vertices_545, vertices_385, vertices_641, vertices_14, vertices_22, vertices_518, vertices_266, vertices_274, vertices_530, vertices_770, vertices_284, vertices_76, vertices_52, vertices_84, vertices_532, vertices_100, vertices_548, vertices_104, vertices_168, vertices_200, vertices_328, vertices_392, vertices_176, vertices_560, vertices_208, vertices_336, vertices_592, vertices_656, vertices_224, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_15), (false, vertices_551), (false, vertices_267), (false, vertices_899), (false, vertices_109), (false, vertices_425), (false, vertices_689), (true, vertices_22), (true, vertices_274), (true, vertices_530), (true, vertices_284), (true, vertices_52), (true, vertices_84), (true, vertices_532), (true, vertices_200), (true, vertices_328), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_224), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_15) then 0 else
  if p.val = (false, vertices_551) then 17 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_109) then 20 else
  if p.val = (false, vertices_425) then 23 else
  if p.val = (false, vertices_689) then 25 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_284) then 21 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_704) then 14 else
  if p.val = (true, vertices_832) then 15 else
  0
cert_priority
cert_nodeAtPriority_61 0 15 1 267 22 274 530 52 84 532 200 328 208 336 592 224 704 832 551 899 109 284 425 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 7 8 850 274 2
cert_row_4 1 1 3 4 5 6 244 52 3
cert_row_2 2 1 2 3 7 284
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 2 0 1 2 3 14 286 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 850
cert_cover_5 2 0 0 3 5 7 274 850 2
cert_coverFacet 3 348
cert_cover_5 3 2 1 2 3 5 284 348 3
cert_coverFacet 4 244
cert_cover_5 4 1 1 3 4 5 52 244 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 232
cert_cover_2 6 4 2 5 6 104 232 3
cert_coverFacet 7 968
cert_cover_5 7 3 2 5 6 7 200 968 3
cert_coverFacet 8 720
cert_cover_2 8 5 3 6 8 208 720 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0488

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0489.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0489

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 333, 789, 709, 369, 561, 225, 30, 526, 566, 410, 714, 434, 284, 588, 488, 69, 261, 517, 49, 273, 529, 97, 161, 545, 193, 321, 641, 14, 22, 518, 26, 138, 522, 50, 402, 162, 546, 642, 28, 76, 268, 524, 276, 532, 580, 280, 200, 328, 584, 392, 304, 560, 224, 352, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_333, vertices_789, vertices_709, vertices_369, vertices_561, vertices_225, vertices_30, vertices_526, vertices_566, vertices_410, vertices_714, vertices_434, vertices_284, vertices_588, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_641, vertices_14, vertices_22, vertices_518, vertices_26, vertices_138, vertices_522, vertices_50, vertices_402, vertices_162, vertices_546, vertices_642, vertices_28, vertices_76, vertices_268, vertices_524, vertices_276, vertices_532, vertices_580, vertices_280, vertices_200, vertices_328, vertices_584, vertices_392, vertices_304, vertices_560, vertices_224, vertices_352, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_333), (false, vertices_789), (false, vertices_709), (false, vertices_369), (false, vertices_561), (false, vertices_225), (true, vertices_14), (true, vertices_22), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_50), (true, vertices_402), (true, vertices_28), (true, vertices_524), (true, vertices_280), (true, vertices_200), (true, vertices_584), (true, vertices_392), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 17 else
  if p.val = (false, vertices_333) then 20 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_22) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_138) then 6 else
  if p.val = (true, vertices_522) then 7 else
  if p.val = (true, vertices_50) then 8 else
  if p.val = (true, vertices_402) then 18 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
cert_nodeAtPriority_21 0 561 1 225 14 22 518 26 138 522 50 28 524 280 200 584 392 416 675 402 333 789 709 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 22 3
cert_row_2 1 0 3 6 7 402
cert_row_4 2 0 2 5 6 8 714 138 2
cert_row_4 3 2 4 5 6 7 488 200 1
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 566
cert_cover_5 2 0 0 1 3 4 22 566 3
cert_coverFacet 3 410
cert_cover_5 3 1 0 2 3 6 26 410 3
cert_coverFacet 4 714
cert_cover_5 4 2 0 2 5 6 138 714 2
cert_coverFacet 5 434
cert_cover_5 5 1 0 3 4 6 50 434 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 588
cert_cover_2 7 2 1 5 8 76 588 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 200 488 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0489

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0490.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0490

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 779, 595, 147, 213, 357, 833, 570, 154, 394, 684, 908, 228, 804, 248, 880, 19, 131, 259, 515, 69, 133, 261, 81, 145, 321, 577, 769, 26, 138, 266, 522, 146, 530, 386, 652, 100, 164, 292, 548, 196, 388, 772, 56, 152, 168, 552, 392, 776, 112, 560, 208, 592, 224, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_779, vertices_595, vertices_147, vertices_213, vertices_357, vertices_833, vertices_570, vertices_154, vertices_394, vertices_684, vertices_908, vertices_228, vertices_804, vertices_248, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_69, vertices_133, vertices_261, vertices_81, vertices_145, vertices_321, vertices_577, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_652, vertices_100, vertices_164, vertices_292, vertices_548, vertices_196, vertices_388, vertices_772, vertices_56, vertices_152, vertices_168, vertices_552, vertices_392, vertices_776, vertices_112, vertices_560, vertices_208, vertices_592, vertices_224, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_779), (false, vertices_595), (false, vertices_147), (false, vertices_213), (false, vertices_357), (false, vertices_833), (true, vertices_26), (true, vertices_138), (true, vertices_652), (true, vertices_164), (true, vertices_548), (true, vertices_772), (true, vertices_56), (true, vertices_152), (true, vertices_168), (true, vertices_552), (true, vertices_392), (true, vertices_112), (true, vertices_560), (true, vertices_224), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 24 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 17 else
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_595) then 19 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_213) then 21 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_833) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_652) then 23 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
cert_nodeAtPriority_6 147 833 26 138 164 548 772 56 152 168 552 392 112 560 224 800 391 779 595 213 357 652
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 8 652
cert_row_4 1 0 2 3 4 8 570 26 3
cert_row_4 2 2 3 4 5 6 248 56 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 570
cert_cover_5 0 1 0 2 3 4 26 570 3
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 684
cert_cover_5 3 0 1 2 4 6 652 684 2
cert_coverFacet 4 908
cert_cover_5 4 0 1 2 6 7 652 908 3
cert_coverFacet 5 228
cert_cover_2 5 4 1 5 6 100 228 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 248
cert_cover_5 7 2 2 3 4 5 56 248 3
cert_coverFacet 8 880
cert_cover_5 8 3 3 4 5 7 112 880 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0490

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0491.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0491

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [43, 75, 675, 835, 173, 457, 913, 62, 94, 626, 844, 396, 436, 596, 788, 688, 11, 35, 67, 515, 41, 73, 137, 161, 321, 385, 641, 769, 30, 42, 74, 50, 82, 546, 578, 44, 76, 140, 268, 52, 84, 276, 532, 164, 580, 388, 772, 328, 392, 176, 560, 592, 400, 656, 784, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_43, vertices_75, vertices_675, vertices_835, vertices_173, vertices_457, vertices_913, vertices_62, vertices_94, vertices_626, vertices_844, vertices_396, vertices_436, vertices_596, vertices_788, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_67, vertices_515, vertices_41, vertices_73, vertices_137, vertices_161, vertices_321, vertices_385, vertices_641, vertices_769, vertices_30, vertices_42, vertices_74, vertices_50, vertices_82, vertices_546, vertices_578, vertices_44, vertices_76, vertices_140, vertices_268, vertices_52, vertices_84, vertices_276, vertices_532, vertices_164, vertices_580, vertices_388, vertices_772, vertices_328, vertices_392, vertices_176, vertices_560, vertices_592, vertices_400, vertices_656, vertices_784, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_43), (false, vertices_75), (false, vertices_675), (false, vertices_835), (false, vertices_173), (false, vertices_457), (false, vertices_913), (true, vertices_30), (true, vertices_50), (true, vertices_82), (true, vertices_76), (true, vertices_268), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_580), (true, vertices_388), (true, vertices_772), (true, vertices_176), (true, vertices_560), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 16 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_43) then 0 else
  if p.val = (false, vertices_75) then 1 else
  if p.val = (false, vertices_675) then 20 else
  if p.val = (false, vertices_835) then 21 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (false, vertices_913) then 25 else
  if p.val = (true, vertices_30) then 18 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_592) then 15 else
  0
cert_priority
cert_nodeAtPriority_50 0 43 1 75 50 82 76 268 52 84 276 532 580 388 772 176 560 592 173 30 675 835 457 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 6 7 436 52 3
cert_row_4 1 0 3 4 5 8 626 50 3
cert_row_2 2 0 1 2 3 30
cert_row_4 3 1 2 5 7 8 844 76 3
cert_rows
cert_pivot_2 6 4 0 1
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 2 0 1 2 4 30 62 3
cert_coverFacet 1 94
cert_cover_5 1 2 0 1 2 5 30 94 3
cert_coverFacet 2 626
cert_cover_5 2 1 0 3 4 5 50 626 3
cert_coverFacet 3 844
cert_cover_5 3 3 1 2 5 7 76 844 3
cert_coverFacet 4 396
cert_cover_2 4 2 1 6 7 140 396 3
cert_coverFacet 5 436
cert_cover_5 5 0 1 3 4 6 52 436 3
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0491

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0492.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0492

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 789, 421, 313, 241, 657, 334, 782, 198, 618, 722, 452, 568, 792, 488, 624, 133, 261, 517, 49, 145, 273, 529, 161, 289, 641, 270, 70, 134, 518, 74, 522, 194, 578, 642, 196, 324, 388, 772, 56, 280, 536, 104, 296, 552, 328, 776, 112, 560, 208, 592, 656, 784, 224, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_789, vertices_421, vertices_313, vertices_241, vertices_657, vertices_334, vertices_782, vertices_198, vertices_618, vertices_722, vertices_452, vertices_568, vertices_792, vertices_488, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_49, vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_641, vertices_270, vertices_70, vertices_134, vertices_518, vertices_74, vertices_522, vertices_194, vertices_578, vertices_642, vertices_196, vertices_324, vertices_388, vertices_772, vertices_56, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_328, vertices_776, vertices_112, vertices_560, vertices_208, vertices_592, vertices_656, vertices_784, vertices_224, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_789), (false, vertices_421), (false, vertices_313), (false, vertices_241), (false, vertices_657), (true, vertices_270), (true, vertices_70), (true, vertices_74), (true, vertices_522), (true, vertices_194), (true, vertices_578), (true, vertices_196), (true, vertices_324), (true, vertices_536), (true, vertices_104), (true, vertices_552), (true, vertices_328), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 18 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_421) then 22 else
  if p.val = (false, vertices_313) then 24 else
  if p.val = (false, vertices_241) then 26 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_270) then 19 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_608) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
cert_nodeAtPriority_14 657 70 74 522 194 578 196 324 536 104 552 328 776 560 592 608 448 647 270 789 421 313 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 7 270
cert_row_4 1 0 3 5 6 8 722 194 1
cert_row_4 2 0 2 4 5 8 618 74 2
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 270 334 3
cert_coverFacet 1 782
cert_cover_5 1 0 0 1 2 8 270 782 3
cert_coverFacet 2 198
cert_cover_2 2 1 0 5 6 70 198 3
cert_coverFacet 3 618
cert_cover_5 3 2 0 2 4 5 74 618 2
cert_coverFacet 4 722
cert_cover_5 4 1 0 3 5 6 194 722 1
cert_coverFacet 5 452
cert_cover_2 5 5 1 6 7 196 452 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 104 488 3
cert_coverFacet 9 624
cert_cover_2 9 4 3 5 8 112 624 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0492

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0494.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0494

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 589, 341, 805, 625, 401, 417, 654, 122, 154, 618, 930, 332, 396, 900, 472, 69, 261, 517, 49, 81, 145, 273, 161, 289, 545, 577, 385, 26, 106, 138, 522, 50, 146, 162, 546, 642, 76, 140, 268, 524, 324, 388, 644, 772, 88, 152, 328, 584, 392, 112, 336, 400, 608, 416, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_589, vertices_341, vertices_805, vertices_625, vertices_401, vertices_417, vertices_654, vertices_122, vertices_154, vertices_618, vertices_930, vertices_332, vertices_396, vertices_900, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_49, vertices_81, vertices_145, vertices_273, vertices_161, vertices_289, vertices_545, vertices_577, vertices_385, vertices_26, vertices_106, vertices_138, vertices_522, vertices_50, vertices_146, vertices_162, vertices_546, vertices_642, vertices_76, vertices_140, vertices_268, vertices_524, vertices_324, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_328, vertices_584, vertices_392, vertices_112, vertices_336, vertices_400, vertices_608, vertices_416, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_589), (false, vertices_341), (false, vertices_805), (false, vertices_625), (false, vertices_401), (false, vertices_417), (true, vertices_26), (true, vertices_106), (true, vertices_138), (true, vertices_522), (true, vertices_546), (true, vertices_642), (true, vertices_140), (true, vertices_268), (true, vertices_388), (true, vertices_644), (true, vertices_88), (true, vertices_152), (true, vertices_328), (true, vertices_392), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 17 else
  if p.val = (false, vertices_589) then 20 else
  if p.val = (false, vertices_341) then 21 else
  if p.val = (false, vertices_805) then 22 else
  if p.val = (false, vertices_625) then 25 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (false, vertices_417) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_106) then 18 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
cert_nodeAtPriority_21 0 401 1 417 26 138 522 546 642 140 268 388 644 88 152 328 392 896 179 106 589 341 805 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_4 1 0 4 6 7 8 930 162 3
cert_row_2 2 0 2 4 5 106
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 4 26 122 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 618
cert_cover_5 3 2 0 2 4 8 106 618 3
cert_coverFacet 4 930
cert_cover_5 4 1 0 4 6 7 162 930 3
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 900
cert_cover_2 7 6 1 7 8 388 900 3
cert_coverFacet 8 472
cert_cover_5 8 3 2 3 5 6 88 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0494

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0495.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0495

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 333, 525, 709, 425, 369, 225, 782, 790, 410, 178, 562, 738, 628, 340, 432, 13, 69, 517, 137, 265, 521, 97, 161, 289, 193, 321, 641, 774, 138, 266, 522, 50, 146, 274, 530, 162, 546, 642, 268, 524, 84, 276, 532, 324, 580, 392, 112, 176, 304, 560, 336, 400, 224, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_333, vertices_525, vertices_709, vertices_425, vertices_369, vertices_225, vertices_782, vertices_790, vertices_410, vertices_178, vertices_562, vertices_738, vertices_628, vertices_340, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_193, vertices_321, vertices_641, vertices_774, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_642, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_324, vertices_580, vertices_392, vertices_112, vertices_176, vertices_304, vertices_560, vertices_336, vertices_400, vertices_224, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_333), (false, vertices_525), (false, vertices_709), (false, vertices_425), (false, vertices_369), (false, vertices_225), (true, vertices_774), (true, vertices_266), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_176), (true, vertices_560), (true, vertices_400), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 17 else
  if p.val = (false, vertices_333) then 20 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_425) then 23 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_774) then 18 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_162) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_608) then 15 else
  0
cert_priority
cert_nodeAtPriority_50 1 525 0 225 266 50 146 274 530 162 546 84 276 532 176 560 400 608 651 774 333 709 425 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 138 2
cert_row_2 1 0 1 7 8 774
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 1 3 4 5 8 628 84 2
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 774 782 2
cert_coverFacet 1 790
cert_cover_5 1 1 0 1 3 7 774 790 2
cert_coverFacet 2 410
cert_cover_5 2 0 0 2 3 6 138 410 2
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 162 738 2
cert_coverFacet 6 628
cert_cover_5 6 3 1 3 4 5 84 628 2
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0495

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0496.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0496

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 333, 213, 677, 773, 481, 782, 58, 602, 298, 690, 588, 596, 660, 440, 472, 69, 133, 261, 517, 161, 289, 545, 193, 321, 769, 26, 42, 266, 522, 50, 530, 290, 546, 770, 76, 268, 524, 84, 148, 532, 580, 644, 772, 56, 88, 408, 296, 328, 584, 176, 208, 592, 656, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_333, vertices_213, vertices_677, vertices_773, vertices_481, vertices_782, vertices_58, vertices_602, vertices_298, vertices_690, vertices_588, vertices_596, vertices_660, vertices_440, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_769, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_530, vertices_290, vertices_546, vertices_770, vertices_76, vertices_268, vertices_524, vertices_84, vertices_148, vertices_532, vertices_580, vertices_644, vertices_772, vertices_56, vertices_88, vertices_408, vertices_296, vertices_328, vertices_584, vertices_176, vertices_208, vertices_592, vertices_656, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_333), (false, vertices_213), (false, vertices_677), (false, vertices_773), (false, vertices_481), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_530), (true, vertices_524), (true, vertices_532), (true, vertices_580), (true, vertices_56), (true, vertices_88), (true, vertices_408), (true, vertices_296), (true, vertices_584), (true, vertices_176), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_333) then 20 else
  if p.val = (false, vertices_213) then 21 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_408) then 24 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_592) then 15 else
  if p.val = (true, vertices_656) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_2 1 2 3 6 7 408
cert_row_4 2 0 2 3 5 8 602 26 3
cert_row_4 3 0 3 4 6 8 690 50 3
cert_rows
cert_pivot_2 1 7 2 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 602
cert_cover_5 2 2 0 2 3 5 26 602 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 690
cert_cover_5 4 3 0 3 4 6 50 690 3
cert_coverFacet 5 588
cert_cover_2 5 2 1 5 8 76 588 3
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 440
cert_cover_5 8 1 2 3 4 6 56 440 3
cert_coverFacet 9 472
cert_cover_5 9 1 2 3 5 6 88 472 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0496

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0497.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0497

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 397, 661, 185, 345, 785, 358, 678, 618, 850, 484, 568, 600, 232, 456, 688, 133, 261, 517, 25, 137, 265, 145, 273, 529, 769, 38, 262, 518, 98, 546, 322, 578, 770, 356, 164, 388, 644, 56, 88, 536, 104, 168, 552, 200, 328, 584, 392, 176, 560, 336, 592, 656, 784, 224, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_397, vertices_661, vertices_185, vertices_345, vertices_785, vertices_358, vertices_678, vertices_618, vertices_850, vertices_484, vertices_568, vertices_600, vertices_232, vertices_456, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_769, vertices_38, vertices_262, vertices_518, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_356, vertices_164, vertices_388, vertices_644, vertices_56, vertices_88, vertices_536, vertices_104, vertices_168, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_176, vertices_560, vertices_336, vertices_592, vertices_656, vertices_784, vertices_224, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_397), (false, vertices_661), (false, vertices_185), (false, vertices_345), (false, vertices_785), (true, vertices_38), (true, vertices_98), (true, vertices_546), (true, vertices_322), (true, vertices_578), (true, vertices_356), (true, vertices_164), (true, vertices_536), (true, vertices_104), (true, vertices_552), (true, vertices_200), (true, vertices_584), (true, vertices_560), (true, vertices_592), (true, vertices_224), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 18 else
  if p.val = (false, vertices_397) then 20 else
  if p.val = (false, vertices_661) then 21 else
  if p.val = (false, vertices_185) then 24 else
  if p.val = (false, vertices_345) then 25 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_356) then 22 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_672) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_356), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 1 4 5 7 356
cert_row_4 2 0 2 4 5 8 618 98 1
cert_row_4 3 0 3 5 7 8 850 322 1
cert_rows
cert_pivot_2 6 1 2 0
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 1 0 1 4 5 38 358 3
cert_coverFacet 1 678
cert_cover_5 1 0 0 1 4 6 38 678 3
cert_coverFacet 2 618
cert_cover_5 2 2 0 2 4 5 98 618 1
cert_coverFacet 3 850
cert_cover_5 3 3 0 3 5 7 322 850 1
cert_coverFacet 4 484
cert_cover_5 4 1 1 4 5 6 356 484 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 600
cert_cover_2 6 3 2 5 8 88 600 3
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coverFacet 9 688
cert_cover_2 9 4 3 6 8 176 688 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0497

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_4353 : Certifies 4353 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0467.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4354 : Certifies 4354 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0468.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4355 : Certifies 4355 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0469.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4356 : Certifies 4356 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0470.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4357 : Certifies 4357 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0471.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4358 : Certifies 4358 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0472.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4359 : Certifies 4359 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0473.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4360 : Certifies 4360 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0474.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4361 : Certifies 4361 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0475.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4362 : Certifies 4362 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0476.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4363 : Certifies 4363 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0477.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4364 : Certifies 4364 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0478.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4365 : Certifies 4365 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0479.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4366 : Certifies 4366 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0480.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4367 : Certifies 4367 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0481.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4368 : Certifies 4368 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0482.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4369 : Certifies 4369 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0483.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4370 : Certifies 4370 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0484.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4371 : Certifies 4371 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0485.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4372 : Certifies 4372 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0486.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4373 : Certifies 4373 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0487.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4374 : Certifies 4374 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0488.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4375 : Certifies 4375 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0489.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4376 : Certifies 4376 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0490.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4377 : Certifies 4377 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0491.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4378 : Certifies 4378 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0492.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4379 : Certifies 4379 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0494.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4380 : Certifies 4380 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0495.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4381 : Certifies 4381 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0496.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4382 : Certifies 4382 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0497.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B144 (j : Fin 30) :
    Certifies (4353 + j.val) := by
  fin_cases j
  · exact projection_4353
  · exact projection_4354
  · exact projection_4355
  · exact projection_4356
  · exact projection_4357
  · exact projection_4358
  · exact projection_4359
  · exact projection_4360
  · exact projection_4361
  · exact projection_4362
  · exact projection_4363
  · exact projection_4364
  · exact projection_4365
  · exact projection_4366
  · exact projection_4367
  · exact projection_4368
  · exact projection_4369
  · exact projection_4370
  · exact projection_4371
  · exact projection_4372
  · exact projection_4373
  · exact projection_4374
  · exact projection_4375
  · exact projection_4376
  · exact projection_4377
  · exact projection_4378
  · exact projection_4379
  · exact projection_4380
  · exact projection_4381
  · exact projection_4382

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
