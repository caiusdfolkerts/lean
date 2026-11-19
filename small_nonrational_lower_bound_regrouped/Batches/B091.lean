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
/- Source: ProjectionCertificates/R_m15e10q1_0150.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0150

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 285, 525, 357, 677, 185, 305, 838, 218, 346, 778, 738, 780, 612, 496, 13, 37, 261, 517, 25, 137, 521, 49, 273, 161, 289, 641, 90, 138, 266, 522, 194, 322, 578, 642, 770, 268, 524, 100, 548, 324, 580, 772, 152, 280, 776, 176, 304, 208, 336, 224, 352, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_285, vertices_525, vertices_357, vertices_677, vertices_185, vertices_305, vertices_838, vertices_218, vertices_346, vertices_778, vertices_738, vertices_780, vertices_612, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_261, vertices_517, vertices_25, vertices_137, vertices_521, vertices_49, vertices_273, vertices_161, vertices_289, vertices_641, vertices_90, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_268, vertices_524, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_224, vertices_352, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_285), (false, vertices_525), (false, vertices_357), (false, vertices_677), (false, vertices_185), (false, vertices_305), (true, vertices_90), (true, vertices_266), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_580), (true, vertices_772), (true, vertices_776), (true, vertices_208), (true, vertices_336), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_185) then 22 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (true, vertices_90) then 16 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 525 1 305 266 194 322 578 770 580 772 776 208 336 224 608 651 90 285 357 677 185
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 6 90 218 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 7 90 346 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 194 738 1
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 176 496 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0150

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0151.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0151

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 93, 525, 837, 313, 113, 481, 30, 526, 662, 186, 426, 962, 244, 708, 13, 69, 517, 25, 265, 521, 49, 81, 97, 289, 321, 769, 14, 22, 518, 26, 170, 266, 522, 146, 386, 642, 770, 28, 524, 84, 148, 196, 580, 644, 56, 296, 112, 176, 224, 416, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_93, vertices_525, vertices_837, vertices_313, vertices_113, vertices_481, vertices_30, vertices_526, vertices_662, vertices_186, vertices_426, vertices_962, vertices_244, vertices_708] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_25, vertices_265, vertices_521, vertices_49, vertices_81, vertices_97, vertices_289, vertices_321, vertices_769, vertices_14, vertices_22, vertices_518, vertices_26, vertices_170, vertices_266, vertices_522, vertices_146, vertices_386, vertices_642, vertices_770, vertices_28, vertices_524, vertices_84, vertices_148, vertices_196, vertices_580, vertices_644, vertices_56, vertices_296, vertices_112, vertices_176, vertices_224, vertices_416, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_93), (false, vertices_525), (false, vertices_837), (false, vertices_313), (false, vertices_113), (false, vertices_481), (true, vertices_14), (true, vertices_22), (true, vertices_518), (true, vertices_26), (true, vertices_170), (true, vertices_146), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_196), (true, vertices_644), (true, vertices_176), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_113) then 1 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_22) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_170) then 16 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_53 0 525 1 113 14 22 518 26 146 386 642 148 196 644 176 704 779 170 93 837 313 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 6 170
cert_row_4 1 0 5 6 7 8 962 386 1
cert_row_4 2 0 1 3 6 8 662 22 3
cert_row_4 3 1 3 4 5 6 244 84 2
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 662
cert_cover_5 2 2 0 1 3 6 22 662 3
cert_coverFacet 3 186
cert_cover_5 3 0 0 2 3 4 26 186 3
cert_coverFacet 4 426
cert_cover_5 4 0 0 2 4 7 170 426 3
cert_coverFacet 5 962
cert_cover_5 5 1 0 5 6 7 386 962 1
cert_coverFacet 6 244
cert_cover_5 6 3 1 3 4 5 84 244 2
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0151

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0152.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0152

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 23, 659, 285, 713, 393, 433, 310, 358, 582, 626, 460, 588, 688, 992, 7, 19, 515, 13, 21, 137, 265, 521, 145, 273, 385, 641, 22, 294, 70, 518, 50, 530, 98, 578, 76, 268, 524, 276, 324, 580, 200, 584, 392, 176, 304, 560, 656, 352, 608, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_23, vertices_659, vertices_285, vertices_713, vertices_393, vertices_433, vertices_310, vertices_358, vertices_582, vertices_626, vertices_460, vertices_588, vertices_688, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_19, vertices_515, vertices_13, vertices_21, vertices_137, vertices_265, vertices_521, vertices_145, vertices_273, vertices_385, vertices_641, vertices_22, vertices_294, vertices_70, vertices_518, vertices_50, vertices_530, vertices_98, vertices_578, vertices_76, vertices_268, vertices_524, vertices_276, vertices_324, vertices_580, vertices_200, vertices_584, vertices_392, vertices_176, vertices_304, vertices_560, vertices_656, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_23), (false, vertices_659), (false, vertices_285), (false, vertices_713), (false, vertices_393), (false, vertices_433), (true, vertices_294), (true, vertices_70), (true, vertices_50), (true, vertices_98), (true, vertices_578), (true, vertices_76), (true, vertices_324), (true, vertices_580), (true, vertices_560), (true, vertices_352), (true, vertices_608), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 15 else
  if p.val = (false, vertices_23) then 0 else
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_285) then 19 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_393) then 1 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (true, vertices_294) then 17 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
cert_nodeAtPriority_23 23 393 70 50 98 578 76 324 580 560 352 608 672 448 527 659 294 285 713 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 8 626 50 3
cert_row_2 1 0 1 4 7 294
cert_row_4 2 1 2 5 6 7 460 76 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 3 0 1 4
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 1 0 1 3 4 22 310 3
cert_coverFacet 1 358
cert_cover_5 1 1 0 1 4 5 294 358 3
cert_coverFacet 2 582
cert_cover_2 2 1 0 5 8 70 582 3
cert_coverFacet 3 626
cert_cover_5 3 0 0 3 4 5 50 626 3
cert_coverFacet 4 460
cert_cover_5 4 2 1 2 5 6 76 460 3
cert_coverFacet 5 588
cert_cover_2 5 2 1 5 8 76 588 3
cert_coverFacet 6 688
cert_cover_2 6 4 3 6 8 176 688 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 352 992 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0152

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0153.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0153

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [91, 299, 547, 707, 677, 329, 481, 542, 558, 594, 284, 300, 436, 724, 472, 11, 35, 67, 515, 73, 265, 161, 289, 545, 193, 321, 641, 526, 26, 42, 82, 530, 546, 578, 28, 44, 268, 148, 276, 532, 164, 292, 548, 644, 88, 280, 296, 328, 208, 592, 400, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_91, vertices_299, vertices_547, vertices_707, vertices_677, vertices_329, vertices_481, vertices_542, vertices_558, vertices_594, vertices_284, vertices_300, vertices_436, vertices_724, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_67, vertices_515, vertices_73, vertices_265, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_526, vertices_26, vertices_42, vertices_82, vertices_530, vertices_546, vertices_578, vertices_28, vertices_44, vertices_268, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_88, vertices_280, vertices_296, vertices_328, vertices_208, vertices_592, vertices_400, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_91), (false, vertices_299), (false, vertices_547), (false, vertices_707), (false, vertices_677), (false, vertices_329), (false, vertices_481), (true, vertices_526), (true, vertices_530), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_280), (true, vertices_208), (true, vertices_592), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 21 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_91) then 18 else
  if p.val = (false, vertices_299) then 19 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_707) then 20 else
  if p.val = (false, vertices_677) then 15 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_526) then 16 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_526), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_2 0 0 1 2 8 526
cert_row_4 1 1 3 4 6 7 436 148 2
cert_row_4 2 1 3 5 6 8 724 148 2
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 526 542 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 4 526 558 3
cert_coverFacet 2 594
cert_cover_2 2 3 0 5 8 82 594 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 436
cert_cover_5 5 1 1 3 4 6 148 436 2
cert_coverFacet 6 724
cert_cover_5 6 2 1 3 5 6 148 724 2
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 88 472 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0153

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0154.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0154

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 333, 181, 597, 389, 313, 89, 454, 710, 842, 690, 802, 660, 632, 808, 21, 69, 133, 261, 25, 73, 265, 49, 81, 161, 289, 385, 198, 162, 290, 546, 322, 578, 386, 642, 770, 148, 532, 324, 580, 388, 644, 56, 88, 296, 552, 328, 584, 776, 176, 560, 592, 656, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_333, vertices_181, vertices_597, vertices_389, vertices_313, vertices_89, vertices_454, vertices_710, vertices_842, vertices_690, vertices_802, vertices_660, vertices_632, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_133, vertices_261, vertices_25, vertices_73, vertices_265, vertices_49, vertices_81, vertices_161, vertices_289, vertices_385, vertices_198, vertices_162, vertices_290, vertices_546, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_148, vertices_532, vertices_324, vertices_580, vertices_388, vertices_644, vertices_56, vertices_88, vertices_296, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_560, vertices_592, vertices_656, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_333), (false, vertices_181), (false, vertices_597), (false, vertices_389), (false, vertices_313), (false, vertices_89), (true, vertices_198), (true, vertices_546), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_644), (true, vertices_552), (true, vertices_584), (true, vertices_776), (true, vertices_560), (true, vertices_656), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 15 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_89) then 1 else
  if p.val = (true, vertices_198) then 16 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 389 1 89 546 322 578 642 770 644 552 584 776 560 656 800 419 198 333 181 597 313
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_4 1 0 2 5 7 8 842 322 1
cert_row_4 2 0 3 4 6 8 690 162 1
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 0 0 1 5 7 198 454 3
cert_coverFacet 1 710
cert_cover_5 1 0 0 1 5 8 198 710 3
cert_coverFacet 2 842
cert_cover_5 2 1 0 2 5 7 322 842 1
cert_coverFacet 3 690
cert_cover_5 3 2 0 3 4 6 162 690 1
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 660
cert_cover_2 5 3 1 6 8 148 660 3
cert_coverFacet 6 632
cert_cover_5 6 3 2 3 4 5 56 632 3
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0154

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0155.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0155

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [91, 299, 547, 579, 421, 457, 737, 542, 558, 722, 284, 300, 692, 468, 344, 11, 35, 67, 515, 73, 265, 161, 289, 545, 193, 577, 385, 526, 26, 42, 82, 530, 546, 578, 28, 44, 268, 148, 276, 532, 164, 292, 548, 388, 88, 280, 296, 328, 208, 336, 656, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_91, vertices_299, vertices_547, vertices_579, vertices_421, vertices_457, vertices_737, vertices_542, vertices_558, vertices_722, vertices_284, vertices_300, vertices_692, vertices_468, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_67, vertices_515, vertices_73, vertices_265, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_526, vertices_26, vertices_42, vertices_82, vertices_530, vertices_546, vertices_578, vertices_28, vertices_44, vertices_268, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_88, vertices_280, vertices_296, vertices_328, vertices_208, vertices_336, vertices_656, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_91), (false, vertices_299), (false, vertices_547), (false, vertices_579), (false, vertices_421), (false, vertices_457), (false, vertices_737), (true, vertices_526), (true, vertices_530), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_548), (true, vertices_280), (true, vertices_208), (true, vertices_336), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_91) then 18 else
  if p.val = (false, vertices_299) then 19 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_579) then 1 else
  if p.val = (false, vertices_421) then 15 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_526) then 16 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_656) then 13 else
  0
cert_priority
cert_nodeAtPriority_53 1 547 0 579 530 28 44 268 148 276 532 548 280 208 336 656 421 526 91 299 457 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 8 526
cert_row_4 1 0 3 5 6 8 722 82 3
cert_row_4 2 1 3 4 6 8 692 148 2
cert_row_4 3 1 3 5 6 7 468 148 2
cert_rows
cert_pivot_2 2 0 4 1
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 526 542 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 4 526 558 3
cert_coverFacet 2 722
cert_cover_5 2 1 0 3 5 6 82 722 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 692
cert_cover_5 5 2 1 3 4 6 148 692 2
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 148 468 2
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0155

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0156.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0156

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 211, 323, 771, 121, 689, 865, 398, 806, 458, 668, 364, 556, 568, 216, 67, 131, 259, 515, 49, 81, 145, 97, 545, 321, 641, 769, 134, 262, 518, 394, 194, 322, 770, 44, 140, 268, 524, 292, 548, 644, 56, 88, 152, 536, 104, 552, 200, 328, 560, 208, 656, 352, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_211, vertices_323, vertices_771, vertices_121, vertices_689, vertices_865, vertices_398, vertices_806, vertices_458, vertices_668, vertices_364, vertices_556, vertices_568, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_49, vertices_81, vertices_145, vertices_97, vertices_545, vertices_321, vertices_641, vertices_769, vertices_134, vertices_262, vertices_518, vertices_394, vertices_194, vertices_322, vertices_770, vertices_44, vertices_140, vertices_268, vertices_524, vertices_292, vertices_548, vertices_644, vertices_56, vertices_88, vertices_152, vertices_536, vertices_104, vertices_552, vertices_200, vertices_328, vertices_560, vertices_208, vertices_656, vertices_352, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_211), (false, vertices_323), (false, vertices_771), (false, vertices_121), (false, vertices_689), (false, vertices_865), (true, vertices_262), (true, vertices_394), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_292), (true, vertices_548), (true, vertices_152), (true, vertices_536), (true, vertices_552), (true, vertices_200), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 14 19 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_211) then 17 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (false, vertices_865) then 24 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_394) then 18 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_328) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 6 8 668 140 2
cert_row_2 1 0 2 6 7 394
cert_row_4 2 0 1 4 7 8 806 262 2
cert_row_4 3 1 2 4 5 7 364 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 134 398 2
cert_coverFacet 1 806
cert_cover_5 1 2 0 1 4 7 262 806 2
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 6 394 458 2
cert_coverFacet 3 668
cert_cover_5 3 0 1 2 3 6 140 668 2
cert_coverFacet 4 364
cert_cover_5 4 3 1 2 4 5 44 364 3
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0156

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0157.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0157

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 589, 397, 805, 665, 785, 110, 302, 202, 394, 370, 722, 628, 712, 816, 13, 261, 517, 137, 521, 145, 273, 529, 385, 769, 46, 74, 138, 266, 82, 146, 274, 98, 290, 194, 386, 76, 268, 100, 292, 548, 580, 200, 584, 392, 648, 112, 304, 560, 592, 656, 784, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_589, vertices_397, vertices_805, vertices_665, vertices_785, vertices_110, vertices_302, vertices_202, vertices_394, vertices_370, vertices_722, vertices_628, vertices_712, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_261, vertices_517, vertices_137, vertices_521, vertices_145, vertices_273, vertices_529, vertices_385, vertices_769, vertices_46, vertices_74, vertices_138, vertices_266, vertices_82, vertices_146, vertices_274, vertices_98, vertices_290, vertices_194, vertices_386, vertices_76, vertices_268, vertices_100, vertices_292, vertices_548, vertices_580, vertices_200, vertices_584, vertices_392, vertices_648, vertices_112, vertices_304, vertices_560, vertices_592, vertices_656, vertices_784, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_589), (false, vertices_397), (false, vertices_805), (false, vertices_665), (false, vertices_785), (true, vertices_46), (true, vertices_74), (true, vertices_138), (true, vertices_266), (true, vertices_82), (true, vertices_98), (true, vertices_290), (true, vertices_194), (true, vertices_100), (true, vertices_200), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_592), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_397) then 20 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_665) then 23 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (true, vertices_46) then 17 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_51 785 74 138 266 82 98 290 194 100 200 112 304 560 592 704 403 46 589 397 805 665
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 3 4 5 7 370 82 2
cert_row_4 2 0 3 5 6 8 722 82 3
cert_row_4 3 1 3 4 5 8 628 100 1
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 5 46 110 3
cert_coverFacet 1 302
cert_cover_5 1 0 0 1 2 7 46 302 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 370
cert_cover_5 4 1 0 3 4 5 82 370 2
cert_coverFacet 5 722
cert_cover_5 5 2 0 3 5 6 82 722 3
cert_coverFacet 6 628
cert_cover_5 6 3 1 3 4 5 100 628 1
cert_coverFacet 7 712
cert_cover_2 7 5 2 6 8 200 712 3
cert_coverFacet 8 816
cert_cover_2 8 4 3 7 8 304 816 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0157

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0158.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0158

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 421, 837, 313, 681, 777, 590, 214, 346, 538, 690, 468, 568, 840, 432, 133, 261, 517, 41, 265, 521, 161, 289, 641, 769, 70, 134, 518, 26, 74, 522, 82, 146, 530, 642, 212, 324, 580, 388, 56, 280, 536, 552, 328, 584, 776, 176, 304, 560, 336, 400, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_421, vertices_837, vertices_313, vertices_681, vertices_777, vertices_590, vertices_214, vertices_346, vertices_538, vertices_690, vertices_468, vertices_568, vertices_840, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_265, vertices_521, vertices_161, vertices_289, vertices_641, vertices_769, vertices_70, vertices_134, vertices_518, vertices_26, vertices_74, vertices_522, vertices_82, vertices_146, vertices_530, vertices_642, vertices_212, vertices_324, vertices_580, vertices_388, vertices_56, vertices_280, vertices_536, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_560, vertices_336, vertices_400, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_421), (false, vertices_837), (false, vertices_313), (false, vertices_681), (false, vertices_777), (true, vertices_70), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_212), (true, vertices_536), (true, vertices_328), (true, vertices_584), (true, vertices_176), (true, vertices_560), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_421) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_212) then 20 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 7 346 26 3
cert_row_4 1 0 1 2 5 8 590 70 2
cert_row_2 2 1 3 5 6 212
cert_row_4 3 0 3 4 6 8 690 146 2
cert_rows
cert_pivot_2 7 2 1 0
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 70 590 2
cert_coverFacet 1 214
cert_cover_5 1 2 0 1 3 5 70 214 2
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 5 26 346 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 690
cert_cover_5 4 3 0 3 4 6 146 690 2
cert_coverFacet 5 468
cert_cover_5 5 2 1 3 5 7 212 468 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 840
cert_cover_2 7 5 2 7 8 328 840 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0158

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0159.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0159

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 93, 533, 837, 409, 201, 481, 666, 682, 434, 866, 540, 236, 556, 612, 21, 69, 517, 25, 73, 137, 273, 529, 193, 321, 385, 769, 650, 146, 274, 530, 162, 290, 546, 770, 28, 44, 76, 524, 532, 100, 548, 580, 152, 536, 168, 552, 200, 400, 224, 352, 608, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_93, vertices_533, vertices_837, vertices_409, vertices_201, vertices_481, vertices_666, vertices_682, vertices_434, vertices_866, vertices_540, vertices_236, vertices_556, vertices_612] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_517, vertices_25, vertices_73, vertices_137, vertices_273, vertices_529, vertices_193, vertices_321, vertices_385, vertices_769, vertices_650, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_770, vertices_28, vertices_44, vertices_76, vertices_524, vertices_532, vertices_100, vertices_548, vertices_580, vertices_152, vertices_536, vertices_168, vertices_552, vertices_200, vertices_400, vertices_224, vertices_352, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_93), (false, vertices_533), (false, vertices_837), (false, vertices_409), (false, vertices_201), (false, vertices_481), (true, vertices_650), (true, vertices_146), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_44), (true, vertices_524), (true, vertices_100), (true, vertices_548), (true, vertices_536), (true, vertices_168), (true, vertices_552), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_650) then 16 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
cert_nodeAtPriority_53 0 533 1 201 146 162 290 546 44 524 100 548 536 168 552 608 787 650 93 837 409 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 7 434 146 2
cert_row_4 1 0 4 5 7 8 866 290 2
cert_row_2 2 0 2 6 8 650
cert_row_4 3 1 2 4 5 6 236 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 666
cert_cover_5 0 2 0 2 3 6 650 666 2
cert_coverFacet 1 682
cert_cover_5 1 2 0 2 4 6 650 682 2
cert_coverFacet 2 434
cert_cover_5 2 0 0 3 4 6 146 434 2
cert_coverFacet 3 866
cert_cover_5 3 1 0 4 5 7 290 866 2
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 236
cert_cover_5 5 3 1 2 4 5 44 236 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 612
cert_cover_2 7 4 1 5 8 100 612 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0159

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0160.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0160

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 115, 531, 451, 397, 713, 593, 310, 790, 354, 684, 780, 564, 484, 752, 19, 67, 259, 515, 137, 265, 521, 81, 529, 193, 577, 385, 278, 50, 530, 98, 290, 322, 770, 140, 268, 524, 52, 532, 164, 292, 548, 388, 772, 648, 776, 112, 560, 592, 224, 352, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_115, vertices_531, vertices_451, vertices_397, vertices_713, vertices_593, vertices_310, vertices_790, vertices_354, vertices_684, vertices_780, vertices_564, vertices_484, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_259, vertices_515, vertices_137, vertices_265, vertices_521, vertices_81, vertices_529, vertices_193, vertices_577, vertices_385, vertices_278, vertices_50, vertices_530, vertices_98, vertices_290, vertices_322, vertices_770, vertices_140, vertices_268, vertices_524, vertices_52, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_648, vertices_776, vertices_112, vertices_560, vertices_592, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_115), (false, vertices_531), (false, vertices_451), (false, vertices_397), (false, vertices_713), (false, vertices_593), (true, vertices_278), (true, vertices_290), (true, vertices_524), (true, vertices_52), (true, vertices_532), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_772), (true, vertices_560), (true, vertices_224), (true, vertices_352), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_115) then 19 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_451) then 20 else
  if p.val = (false, vertices_397) then 15 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_593) then 1 else
  if p.val = (true, vertices_278) then 16 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 1 531 0 593 290 524 52 532 164 292 548 772 560 224 352 672 397 278 779 115 451 713
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 7 278
cert_row_4 1 1 2 4 6 8 684 140 2
cert_row_4 2 1 4 5 6 7 484 164 2
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 278 310 3
cert_coverFacet 1 790
cert_cover_5 1 0 0 1 3 8 278 790 3
cert_coverFacet 2 354
cert_cover_2 2 4 0 5 7 98 354 3
cert_coverFacet 3 684
cert_cover_5 3 1 1 2 4 6 140 684 2
cert_coverFacet 4 780
cert_cover_2 4 2 1 7 8 268 780 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 484
cert_cover_5 6 2 1 4 5 6 164 484 2
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0160

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0161.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0161

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 115, 531, 323, 653, 457, 721, 310, 790, 482, 428, 780, 564, 740, 624, 19, 67, 259, 515, 137, 265, 521, 81, 529, 193, 321, 641, 278, 50, 530, 98, 290, 322, 770, 140, 268, 524, 52, 532, 164, 292, 548, 644, 772, 392, 776, 112, 560, 592, 224, 608, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_115, vertices_531, vertices_323, vertices_653, vertices_457, vertices_721, vertices_310, vertices_790, vertices_482, vertices_428, vertices_780, vertices_564, vertices_740, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_259, vertices_515, vertices_137, vertices_265, vertices_521, vertices_81, vertices_529, vertices_193, vertices_321, vertices_641, vertices_278, vertices_50, vertices_530, vertices_98, vertices_290, vertices_322, vertices_770, vertices_140, vertices_268, vertices_524, vertices_52, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_392, vertices_776, vertices_112, vertices_560, vertices_592, vertices_224, vertices_608, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_115), (false, vertices_531), (false, vertices_323), (false, vertices_653), (false, vertices_457), (false, vertices_721), (true, vertices_278), (true, vertices_290), (true, vertices_268), (true, vertices_52), (true, vertices_532), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_772), (true, vertices_560), (true, vertices_224), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_115) then 16 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_323) then 1 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_278) then 17 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
cert_nodeAtPriority_23 531 323 290 268 52 532 164 292 548 772 560 224 608 416 779 115 278 653 457 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 7 278
cert_row_4 1 0 4 5 6 7 482 98 3
cert_row_4 2 1 2 4 6 7 428 140 2
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 278 310 3
cert_coverFacet 1 790
cert_cover_5 1 0 0 1 3 8 278 790 3
cert_coverFacet 2 482
cert_cover_5 2 1 0 4 5 6 98 482 3
cert_coverFacet 3 428
cert_cover_5 3 2 1 2 4 6 140 428 2
cert_coverFacet 4 780
cert_cover_2 4 2 1 7 8 268 780 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 164 740 2
cert_coverFacet 7 624
cert_cover_2 7 4 3 5 8 112 624 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0161

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0162.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0162

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 299, 163, 771, 213, 837, 481, 570, 842, 690, 604, 660, 440, 344, 464, 35, 131, 259, 515, 69, 133, 517, 161, 289, 193, 321, 769, 42, 266, 522, 562, 162, 642, 770, 84, 148, 532, 580, 644, 56, 88, 280, 536, 296, 328, 584, 176, 208, 336, 400, 656, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_299, vertices_163, vertices_771, vertices_213, vertices_837, vertices_481, vertices_570, vertices_842, vertices_690, vertices_604, vertices_660, vertices_440, vertices_344, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_69, vertices_133, vertices_517, vertices_161, vertices_289, vertices_193, vertices_321, vertices_769, vertices_42, vertices_266, vertices_522, vertices_562, vertices_162, vertices_642, vertices_770, vertices_84, vertices_148, vertices_532, vertices_580, vertices_644, vertices_56, vertices_88, vertices_280, vertices_536, vertices_296, vertices_328, vertices_584, vertices_176, vertices_208, vertices_336, vertices_400, vertices_656, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_299), (false, vertices_163), (false, vertices_771), (false, vertices_213), (false, vertices_837), (false, vertices_481), (true, vertices_522), (true, vertices_562), (true, vertices_532), (true, vertices_56), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_328), (true, vertices_584), (true, vertices_176), (true, vertices_336), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_562) then 17 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_56) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_656) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_562), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_4 0 1 2 3 5 8 604 84 1
cert_row_4 1 0 2 5 7 8 842 266 2
cert_row_2 2 0 3 4 8 562
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 570
cert_cover_5 0 2 0 2 3 4 42 570 2
cert_coverFacet 1 842
cert_cover_5 1 1 0 2 5 7 266 842 2
cert_coverFacet 2 690
cert_cover_5 2 2 0 3 4 6 562 690 3
cert_coverFacet 3 604
cert_cover_5 3 0 1 2 3 5 84 604 1
cert_coverFacet 4 660
cert_cover_2 4 3 1 6 8 148 660 3
cert_coverFacet 5 440
cert_cover_5 5 3 2 3 4 6 56 440 3
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0162

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0163.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0163

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 93, 173, 549, 581, 457, 865, 666, 682, 818, 466, 540, 556, 852, 216, 13, 37, 69, 517, 73, 137, 161, 289, 545, 321, 577, 385, 650, 146, 274, 530, 162, 290, 546, 386, 28, 44, 524, 84, 532, 548, 580, 88, 152, 536, 168, 552, 200, 208, 336, 784, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_93, vertices_173, vertices_549, vertices_581, vertices_457, vertices_865, vertices_666, vertices_682, vertices_818, vertices_466, vertices_540, vertices_556, vertices_852, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_517, vertices_73, vertices_137, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_650, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_28, vertices_44, vertices_524, vertices_84, vertices_532, vertices_548, vertices_580, vertices_88, vertices_152, vertices_536, vertices_168, vertices_552, vertices_200, vertices_208, vertices_336, vertices_784, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_93), (false, vertices_173), (false, vertices_549), (false, vertices_581), (false, vertices_457), (false, vertices_865), (true, vertices_650), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_524), (true, vertices_532), (true, vertices_152), (true, vertices_536), (true, vertices_552), (true, vertices_208), (true, vertices_336), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_173) then 19 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_581) then 1 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_865) then 24 else
  if p.val = (true, vertices_650) then 16 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_784) then 13 else
  0
cert_priority
cert_nodeAtPriority_53 0 549 1 581 146 274 530 546 524 532 152 536 552 208 336 784 419 650 93 173 457 865
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 6 8 650
cert_row_4 1 0 3 4 7 8 818 274 2
cert_row_4 2 0 3 5 6 7 466 146 2
cert_row_4 3 1 3 5 7 8 852 84 3
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 666
cert_cover_5 0 0 0 2 3 6 650 666 2
cert_coverFacet 1 682
cert_cover_5 1 0 0 2 4 6 650 682 2
cert_coverFacet 2 818
cert_cover_5 2 1 0 3 4 7 274 818 2
cert_coverFacet 3 466
cert_cover_5 3 2 0 3 5 6 146 466 2
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 852
cert_cover_5 6 3 1 3 5 7 84 852 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0163

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0164.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0164

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 597, 405, 677, 793, 801, 206, 398, 362, 738, 92, 284, 708, 632, 808, 21, 133, 517, 273, 529, 161, 289, 545, 385, 769, 142, 74, 266, 98, 162, 290, 194, 386, 28, 76, 268, 84, 276, 196, 580, 388, 644, 88, 280, 536, 104, 296, 552, 776, 592, 608, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_597, vertices_405, vertices_677, vertices_793, vertices_801, vertices_206, vertices_398, vertices_362, vertices_738, vertices_92, vertices_284, vertices_708, vertices_632, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_385, vertices_769, vertices_142, vertices_74, vertices_266, vertices_98, vertices_162, vertices_290, vertices_194, vertices_386, vertices_28, vertices_76, vertices_268, vertices_84, vertices_276, vertices_196, vertices_580, vertices_388, vertices_644, vertices_88, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_776, vertices_592, vertices_608, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_597), (false, vertices_405), (false, vertices_677), (false, vertices_793), (false, vertices_801), (true, vertices_142), (true, vertices_74), (true, vertices_266), (true, vertices_98), (true, vertices_194), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_196), (true, vertices_88), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_793) then 23 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_142) then 17 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_51 801 74 266 98 194 28 76 268 196 88 104 296 552 608 704 419 142 597 405 677 793
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 6 142
cert_row_4 1 0 2 4 5 7 362 74 2
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 2 3 4 5 8 632 88 2
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 142 206 3
cert_coverFacet 1 398
cert_cover_5 1 0 0 1 2 7 142 398 3
cert_coverFacet 2 362
cert_cover_5 2 1 0 2 4 5 74 362 2
cert_coverFacet 3 738
cert_cover_5 3 2 0 4 5 6 98 738 3
cert_coverFacet 4 92
cert_cover_2 4 2 1 3 5 28 92 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 708
cert_cover_2 6 5 1 6 8 196 708 3
cert_coverFacet 7 632
cert_cover_5 7 3 2 3 4 5 88 632 2
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0164

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0165.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0165

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 651, 29, 301, 117, 217, 737, 806, 410, 298, 962, 284, 468, 612, 836, 523, 13, 21, 37, 25, 41, 137, 81, 97, 545, 193, 641, 42, 138, 266, 290, 546, 386, 642, 770, 28, 268, 84, 276, 100, 292, 548, 324, 580, 772, 152, 280, 296, 208, 400, 608, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_651, vertices_29, vertices_301, vertices_117, vertices_217, vertices_737, vertices_806, vertices_410, vertices_298, vertices_962, vertices_284, vertices_468, vertices_612, vertices_836] (by decide +kernel)
  polygons := literalFinset [vertices_523, vertices_13, vertices_21, vertices_37, vertices_25, vertices_41, vertices_137, vertices_81, vertices_97, vertices_545, vertices_193, vertices_641, vertices_42, vertices_138, vertices_266, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_84, vertices_276, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_296, vertices_208, vertices_400, vertices_608, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_651), (false, vertices_29), (false, vertices_301), (false, vertices_117), (false, vertices_217), (false, vertices_737), (true, vertices_266), (true, vertices_290), (true, vertices_386), (true, vertices_770), (true, vertices_276), (true, vertices_548), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_280), (true, vertices_400), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 15 else
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_117) then 19 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_448) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_29), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
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
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_4 1 0 2 3 6 7 410 138 2
cert_row_4 2 0 5 6 7 8 962 386 1
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 410
cert_cover_5 1 1 0 2 3 6 138 410 2
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 962
cert_cover_5 3 2 0 5 6 7 386 962 1
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 468
cert_cover_5 5 3 1 3 5 6 84 468 3
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 836
cert_cover_2 7 5 1 7 8 324 836 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0165

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0166.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0166

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 309, 149, 613, 645, 361, 465, 662, 410, 538, 618, 458, 812, 788, 792, 21, 37, 133, 517, 145, 273, 97, 289, 193, 321, 577, 641, 26, 74, 394, 522, 146, 530, 194, 578, 642, 148, 276, 532, 292, 548, 644, 772, 280, 536, 104, 296, 552, 328, 776, 400, 784, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_309, vertices_149, vertices_613, vertices_645, vertices_361, vertices_465, vertices_662, vertices_410, vertices_538, vertices_618, vertices_458, vertices_812, vertices_788, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_133, vertices_517, vertices_145, vertices_273, vertices_97, vertices_289, vertices_193, vertices_321, vertices_577, vertices_641, vertices_26, vertices_74, vertices_394, vertices_522, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_148, vertices_276, vertices_532, vertices_292, vertices_548, vertices_644, vertices_772, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_328, vertices_776, vertices_400, vertices_784, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_309), (false, vertices_149), (false, vertices_613), (false, vertices_645), (false, vertices_361), (false, vertices_465), (true, vertices_26), (true, vertices_74), (true, vertices_394), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_532), (true, vertices_772), (true, vertices_280), (true, vertices_536), (true, vertices_552), (true, vertices_776), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_309) then 18 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_645) then 1 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_394) then 16 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_784) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 149 1 645 26 74 522 146 530 532 772 280 536 552 776 784 707 394 309 613 361 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_2 1 0 2 6 7 394
cert_row_4 2 0 2 4 5 8 618 74 2
cert_row_4 3 1 2 4 7 8 812 292 1
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 410
cert_cover_5 1 1 0 2 3 6 26 410 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 618
cert_cover_5 3 2 0 2 4 5 74 618 2
cert_coverFacet 4 458
cert_cover_5 4 1 0 2 5 6 74 458 3
cert_coverFacet 5 812
cert_cover_5 5 3 1 2 4 7 292 812 1
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0166

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0167.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0167

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 395, 557, 117, 533, 217, 537, 481, 806, 666, 554, 962, 724, 356, 836, 267, 21, 37, 517, 25, 41, 137, 521, 81, 529, 97, 289, 193, 385, 42, 138, 522, 290, 546, 386, 642, 770, 84, 532, 100, 292, 548, 324, 580, 772, 152, 536, 552, 208, 656, 352, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_395, vertices_557, vertices_117, vertices_533, vertices_217, vertices_537, vertices_481, vertices_806, vertices_666, vertices_554, vertices_962, vertices_724, vertices_356, vertices_836] (by decide +kernel)
  polygons := literalFinset [vertices_267, vertices_21, vertices_37, vertices_517, vertices_25, vertices_41, vertices_137, vertices_521, vertices_81, vertices_529, vertices_97, vertices_289, vertices_193, vertices_385, vertices_42, vertices_138, vertices_522, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_84, vertices_532, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_152, vertices_536, vertices_552, vertices_208, vertices_656, vertices_352, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_395), (false, vertices_557), (false, vertices_117), (false, vertices_533), (false, vertices_217), (false, vertices_537), (false, vertices_481), (true, vertices_522), (true, vertices_546), (true, vertices_642), (true, vertices_770), (true, vertices_292), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_656), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 14 else
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_557) then 17 else
  if p.val = (false, vertices_117) then 18 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_217) then 20 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_4 1 0 2 3 6 8 666 138 2
cert_row_4 2 0 5 6 7 8 962 386 1
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 666
cert_cover_5 1 1 0 2 3 6 138 666 2
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 962
cert_cover_5 3 2 0 5 6 7 386 962 1
cert_coverFacet 4 724
cert_cover_5 4 3 1 3 5 6 84 724 3
cert_coverFacet 5 356
cert_cover_2 5 4 1 5 7 100 356 3
cert_coverFacet 6 836
cert_cover_2 6 5 1 7 8 324 836 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0167

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0168.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0168

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 109, 269, 709, 773, 425, 241, 782, 314, 538, 434, 722, 60, 540, 628, 13, 69, 261, 517, 41, 265, 97, 161, 193, 385, 641, 769, 26, 266, 522, 306, 146, 530, 386, 642, 770, 28, 44, 268, 524, 52, 532, 100, 580, 772, 56, 536, 296, 112, 176, 208, 592, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_109, vertices_269, vertices_709, vertices_773, vertices_425, vertices_241, vertices_782, vertices_314, vertices_538, vertices_434, vertices_722, vertices_60, vertices_540, vertices_628] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_517, vertices_41, vertices_265, vertices_97, vertices_161, vertices_193, vertices_385, vertices_641, vertices_769, vertices_26, vertices_266, vertices_522, vertices_306, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_524, vertices_52, vertices_532, vertices_100, vertices_580, vertices_772, vertices_56, vertices_536, vertices_296, vertices_112, vertices_176, vertices_208, vertices_592, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_109), (false, vertices_269), (false, vertices_709), (false, vertices_773), (false, vertices_425), (false, vertices_241), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_306), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_524), (true, vertices_52), (true, vertices_532), (true, vertices_56), (true, vertices_536), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_773) then 1 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_306) then 16 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_592) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 269 1 773 26 266 522 146 530 28 524 52 532 56 536 592 899 306 109 709 425 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_2 1 0 3 4 7 306
cert_row_4 2 0 3 5 6 8 722 146 2
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 314
cert_cover_5 1 1 0 2 3 4 26 314 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 434
cert_cover_5 3 1 0 3 4 6 306 434 3
cert_coverFacet 4 722
cert_cover_5 4 2 0 3 5 6 146 722 2
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 628
cert_cover_5 7 3 1 3 4 5 52 628 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0168

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0169.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0169

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 653, 213, 773, 457, 777, 369, 566, 774, 362, 682, 778, 306, 692, 248, 21, 133, 261, 517, 137, 265, 521, 81, 273, 193, 321, 769, 22, 262, 518, 42, 266, 522, 50, 274, 290, 546, 770, 564, 148, 644, 772, 104, 168, 200, 328, 648, 776, 112, 176, 304, 208, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_653, vertices_213, vertices_773, vertices_457, vertices_777, vertices_369, vertices_566, vertices_774, vertices_362, vertices_682, vertices_778, vertices_306, vertices_692, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_81, vertices_273, vertices_193, vertices_321, vertices_769, vertices_22, vertices_262, vertices_518, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_290, vertices_546, vertices_770, vertices_564, vertices_148, vertices_644, vertices_772, vertices_104, vertices_168, vertices_200, vertices_328, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_653), (false, vertices_213), (false, vertices_773), (false, vertices_457), (false, vertices_777), (false, vertices_369), (true, vertices_518), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_564), (true, vertices_104), (true, vertices_168), (true, vertices_176), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 15 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_50) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_564) then 19 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_54 773 777 518 42 266 522 50 290 546 770 104 168 176 672 279 653 213 564 457 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 4 8 564
cert_row_4 1 0 2 4 5 7 362 42 3
cert_row_4 2 0 2 4 6 8 682 42 3
cert_row_4 3 2 3 4 5 6 248 104 1
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 22 566 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 362
cert_cover_5 2 1 0 2 4 5 42 362 3
cert_coverFacet 3 682
cert_cover_5 3 2 0 2 4 6 42 682 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 306
cert_cover_2 5 3 0 4 7 50 306 3
cert_coverFacet 6 692
cert_cover_5 6 0 1 3 4 6 564 692 3
cert_coverFacet 7 248
cert_cover_5 7 3 2 3 4 5 104 248 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0169

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0170.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0170

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 781, 185, 537, 913, 481, 110, 270, 598, 774, 354, 962, 124, 540, 752, 25, 41, 265, 521, 145, 529, 161, 289, 385, 769, 14, 70, 262, 518, 42, 266, 98, 290, 322, 578, 770, 28, 108, 268, 524, 84, 532, 772, 56, 536, 112, 176, 592, 656, 224, 352, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_781, vertices_185, vertices_537, vertices_913, vertices_481, vertices_110, vertices_270, vertices_598, vertices_774, vertices_354, vertices_962, vertices_124, vertices_540, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_521, vertices_145, vertices_529, vertices_161, vertices_289, vertices_385, vertices_769, vertices_14, vertices_70, vertices_262, vertices_518, vertices_42, vertices_266, vertices_98, vertices_290, vertices_322, vertices_578, vertices_770, vertices_28, vertices_108, vertices_268, vertices_524, vertices_84, vertices_532, vertices_772, vertices_56, vertices_536, vertices_112, vertices_176, vertices_592, vertices_656, vertices_224, vertices_352, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_781), (false, vertices_185), (false, vertices_537), (false, vertices_913), (false, vertices_481), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_28), (true, vertices_108), (true, vertices_84), (true, vertices_532), (true, vertices_112), (true, vertices_592), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_913) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_108) then 19 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_9 0 537 1 14 70 262 518 98 322 578 770 28 84 532 112 592 704 299 781 108 185 913 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 1 3 5 8 598 70 2
cert_row_4 2 0 5 6 7 8 962 322 2
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 598
cert_cover_5 2 1 0 1 3 5 70 598 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 354
cert_cover_2 4 4 0 5 7 98 354 3
cert_coverFacet 5 962
cert_cover_5 5 2 0 5 6 7 322 962 2
cert_coverFacet 6 124
cert_cover_5 6 0 1 2 3 4 28 124 3
cert_coverFacet 7 540
cert_cover_2 7 2 1 3 8 28 540 3
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 112 752 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0170

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0172.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0172

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 155, 43, 339, 557, 653, 213, 325, 538, 810, 786, 740, 356, 728, 880, 11, 19, 35, 259, 525, 37, 69, 133, 261, 41, 137, 81, 145, 321, 26, 42, 522, 274, 530, 290, 770, 100, 292, 548, 196, 324, 644, 152, 536, 552, 648, 208, 336, 592, 784, 352, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_155, vertices_43, vertices_339, vertices_557, vertices_653, vertices_213, vertices_325, vertices_538, vertices_810, vertices_786, vertices_740, vertices_356, vertices_728, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_35, vertices_259, vertices_525, vertices_37, vertices_69, vertices_133, vertices_261, vertices_41, vertices_137, vertices_81, vertices_145, vertices_321, vertices_26, vertices_42, vertices_522, vertices_274, vertices_530, vertices_290, vertices_770, vertices_100, vertices_292, vertices_548, vertices_196, vertices_324, vertices_644, vertices_152, vertices_536, vertices_552, vertices_648, vertices_208, vertices_336, vertices_592, vertices_784, vertices_352, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_155), (false, vertices_43), (false, vertices_339), (false, vertices_557), (false, vertices_653), (false, vertices_213), (false, vertices_325), (true, vertices_522), (true, vertices_530), (true, vertices_770), (true, vertices_100), (true, vertices_536), (true, vertices_592), (true, vertices_784), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 21 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 14 else
  if p.val = (false, vertices_155) then 15 else
  if p.val = (false, vertices_43) then 0 else
  if p.val = (false, vertices_339) then 16 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_325) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_43), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_4 1 1 4 5 6 8 740 100 3
cert_row_4 2 2 3 5 6 8 728 152 2
cert_row_4 3 3 4 5 7 8 880 336 1
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 538
cert_cover_2 0 2 0 3 8 26 538 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 740
cert_cover_5 3 1 1 4 5 6 100 740 3
cert_coverFacet 4 356
cert_cover_2 4 4 1 5 7 100 356 3
cert_coverFacet 5 728
cert_cover_5 5 2 2 3 5 6 152 728 2
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 336 880 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0172

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0173.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0173

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 267, 707, 771, 901, 313, 481, 542, 270, 774, 602, 284, 436, 724, 248, 11, 67, 259, 515, 41, 265, 97, 289, 193, 385, 641, 769, 14, 262, 518, 538, 74, 266, 578, 770, 28, 268, 148, 276, 532, 388, 644, 772, 56, 88, 280, 104, 176, 304, 208, 592, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_267, vertices_707, vertices_771, vertices_901, vertices_313, vertices_481, vertices_542, vertices_270, vertices_774, vertices_602, vertices_284, vertices_436, vertices_724, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_259, vertices_515, vertices_41, vertices_265, vertices_97, vertices_289, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_262, vertices_518, vertices_538, vertices_74, vertices_266, vertices_578, vertices_770, vertices_28, vertices_268, vertices_148, vertices_276, vertices_532, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_104, vertices_176, vertices_304, vertices_208, vertices_592, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_267), (false, vertices_707), (false, vertices_771), (false, vertices_901), (false, vertices_313), (false, vertices_481), (true, vertices_14), (true, vertices_262), (true, vertices_518), (true, vertices_538), (true, vertices_28), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_88), (true, vertices_176), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 15 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_538) then 17 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_592) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_538), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
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
cert_row_2 0 0 2 3 8 538
cert_row_4 1 1 3 4 6 7 436 148 2
cert_row_4 2 1 3 5 6 8 724 148 2
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 14 542 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 602
cert_cover_5 3 0 0 2 3 5 538 602 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 436
cert_cover_5 5 1 1 3 4 6 148 436 2
cert_coverFacet 6 724
cert_cover_5 6 2 1 3 5 6 148 724 2
cert_coverFacet 7 248
cert_cover_5 7 3 2 3 4 5 56 248 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0173

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0174.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0174

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 205, 525, 357, 549, 905, 465, 30, 558, 118, 538, 370, 914, 92, 728, 13, 37, 69, 517, 137, 521, 289, 545, 193, 321, 385, 769, 14, 22, 38, 26, 522, 114, 274, 530, 290, 546, 770, 28, 76, 524, 84, 100, 548, 88, 536, 200, 648, 208, 336, 400, 656, 352, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_205, vertices_525, vertices_357, vertices_549, vertices_905, vertices_465, vertices_30, vertices_558, vertices_118, vertices_538, vertices_370, vertices_914, vertices_92, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_517, vertices_137, vertices_521, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_14, vertices_22, vertices_38, vertices_26, vertices_522, vertices_114, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_28, vertices_76, vertices_524, vertices_84, vertices_100, vertices_548, vertices_88, vertices_536, vertices_200, vertices_648, vertices_208, vertices_336, vertices_400, vertices_656, vertices_352, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_205), (false, vertices_525), (false, vertices_357), (false, vertices_549), (false, vertices_905), (false, vertices_465), (true, vertices_14), (true, vertices_22), (true, vertices_38), (true, vertices_26), (true, vertices_522), (true, vertices_114), (true, vertices_274), (true, vertices_530), (true, vertices_28), (true, vertices_84), (true, vertices_88), (true, vertices_536), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_205) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_549) then 1 else
  if p.val = (false, vertices_905) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_22) then 3 else
  if p.val = (true, vertices_38) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_114) then 16 else
  if p.val = (true, vertices_274) then 7 else
  if p.val = (true, vertices_530) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_656) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 525 1 549 14 22 38 26 522 274 530 28 84 88 536 656 803 114 205 357 905 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 14 3
cert_row_2 1 0 3 4 5 114
cert_row_4 2 0 3 6 7 8 914 274 2
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 4 14 558 3
cert_coverFacet 2 118
cert_cover_5 2 1 0 1 3 4 22 118 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 370
cert_cover_5 4 1 0 3 4 7 114 370 3
cert_coverFacet 5 914
cert_cover_5 5 2 0 3 6 7 274 914 2
cert_coverFacet 6 92
cert_cover_2 6 2 1 3 5 28 92 3
cert_coverFacet 7 728
cert_cover_5 7 3 2 3 5 6 88 728 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0174

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0175.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0175

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 93, 525, 661, 233, 553, 465, 302, 558, 774, 914, 482, 284, 788, 376, 13, 21, 517, 41, 73, 521, 81, 145, 161, 545, 193, 641, 46, 262, 518, 162, 290, 546, 386, 642, 770, 28, 268, 524, 276, 532, 772, 88, 280, 104, 296, 552, 336, 400, 656, 784, 224, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_93, vertices_525, vertices_661, vertices_233, vertices_553, vertices_465, vertices_302, vertices_558, vertices_774, vertices_914, vertices_482, vertices_284, vertices_788, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_517, vertices_41, vertices_73, vertices_521, vertices_81, vertices_145, vertices_161, vertices_545, vertices_193, vertices_641, vertices_46, vertices_262, vertices_518, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_276, vertices_532, vertices_772, vertices_88, vertices_280, vertices_104, vertices_296, vertices_552, vertices_336, vertices_400, vertices_656, vertices_784, vertices_224, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_93), (false, vertices_525), (false, vertices_661), (false, vertices_233), (false, vertices_553), (false, vertices_465), (true, vertices_46), (true, vertices_262), (true, vertices_518), (true, vertices_290), (true, vertices_386), (true, vertices_770), (true, vertices_268), (true, vertices_276), (true, vertices_772), (true, vertices_280), (true, vertices_296), (true, vertices_784), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_46) then 16 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 525 1 553 262 518 290 386 770 268 276 772 280 296 784 352 675 46 93 661 233 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 3 6 7 8 914 386 1
cert_row_4 2 0 4 5 6 7 482 162 2
cert_row_4 3 2 3 4 5 7 376 88 2
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 7 46 302 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 8 46 558 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 914
cert_cover_5 3 1 0 3 6 7 386 914 1
cert_coverFacet 4 482
cert_cover_5 4 2 0 4 5 6 162 482 2
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 376
cert_cover_5 7 3 2 3 4 5 88 376 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0175

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0176.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0176

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 653, 269, 805, 233, 329, 689, 94, 334, 790, 242, 562, 802, 540, 728, 13, 261, 517, 73, 137, 265, 97, 161, 289, 545, 321, 641, 78, 22, 262, 50, 82, 530, 98, 290, 546, 322, 770, 28, 268, 524, 532, 772, 88, 536, 200, 328, 648, 176, 560, 208, 656, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_653, vertices_269, vertices_805, vertices_233, vertices_329, vertices_689, vertices_94, vertices_334, vertices_790, vertices_242, vertices_562, vertices_802, vertices_540, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_97, vertices_161, vertices_289, vertices_545, vertices_321, vertices_641, vertices_78, vertices_22, vertices_262, vertices_50, vertices_82, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_770, vertices_28, vertices_268, vertices_524, vertices_532, vertices_772, vertices_88, vertices_536, vertices_200, vertices_328, vertices_648, vertices_176, vertices_560, vertices_208, vertices_656, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_653), (false, vertices_269), (false, vertices_805), (false, vertices_233), (false, vertices_329), (false, vertices_689), (true, vertices_78), (true, vertices_22), (true, vertices_262), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_546), (true, vertices_770), (true, vertices_28), (true, vertices_532), (true, vertices_88), (true, vertices_536), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 15 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (true, vertices_78) then 16 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_208) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 269 1 329 22 262 50 82 530 546 770 28 532 88 536 208 355 78 653 805 233 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 22 3
cert_row_2 1 0 1 2 5 78
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 7 1 0 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 3 78 94 3
cert_coverFacet 1 334
cert_cover_5 1 1 0 1 2 7 78 334 3
cert_coverFacet 2 790
cert_cover_5 2 0 0 1 3 7 22 790 3
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 50 242 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 728
cert_cover_5 7 3 2 3 5 6 88 728 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0176

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0177.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0177

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 331, 707, 661, 409, 481, 558, 362, 610, 300, 780, 436, 788, 740, 792, 11, 67, 515, 25, 265, 145, 529, 193, 321, 385, 641, 42, 330, 522, 98, 546, 578, 44, 268, 524, 148, 276, 532, 164, 292, 548, 644, 772, 280, 536, 296, 776, 400, 784, 224, 352, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_331, vertices_707, vertices_661, vertices_409, vertices_481, vertices_558, vertices_362, vertices_610, vertices_300, vertices_780, vertices_436, vertices_788, vertices_740, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_515, vertices_25, vertices_265, vertices_145, vertices_529, vertices_193, vertices_321, vertices_385, vertices_641, vertices_42, vertices_330, vertices_522, vertices_98, vertices_546, vertices_578, vertices_44, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_280, vertices_536, vertices_296, vertices_776, vertices_400, vertices_784, vertices_224, vertices_352, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_331), (false, vertices_707), (false, vertices_661), (false, vertices_409), (false, vertices_481), (true, vertices_42), (true, vertices_98), (true, vertices_546), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_772), (true, vertices_296), (true, vertices_776), (true, vertices_784), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 16 else
  if p.val = (false, vertices_331) then 17 else
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_661) then 20 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
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
cert_row_4 0 1 3 4 6 7 436 148 2
cert_row_2 1 0 2 5 7 330
cert_row_4 2 0 1 2 4 8 558 42 1
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 2 0 1 2 4 42 558 1
cert_coverFacet 1 362
cert_cover_5 1 1 0 2 4 5 42 362 3
cert_coverFacet 2 610
cert_cover_2 2 4 0 5 8 98 610 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 780
cert_cover_2 4 2 1 7 8 268 780 3
cert_coverFacet 5 436
cert_cover_5 5 0 1 3 4 6 148 436 2
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 740
cert_cover_5 7 3 1 4 5 6 164 740 2
cert_coverFacet 8 792
cert_cover_2 8 3 2 7 8 280 792 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0177

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0178.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0178

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 179, 29, 333, 421, 601, 465, 30, 526, 550, 538, 722, 930, 812, 968, 51, 13, 21, 37, 261, 25, 73, 81, 145, 161, 321, 385, 14, 22, 38, 518, 26, 522, 146, 530, 162, 546, 642, 28, 268, 524, 292, 548, 536, 328, 584, 776, 208, 592, 416, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_179, vertices_29, vertices_333, vertices_421, vertices_601, vertices_465, vertices_30, vertices_526, vertices_550, vertices_538, vertices_722, vertices_930, vertices_812, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_51, vertices_13, vertices_21, vertices_37, vertices_261, vertices_25, vertices_73, vertices_81, vertices_145, vertices_161, vertices_321, vertices_385, vertices_14, vertices_22, vertices_38, vertices_518, vertices_26, vertices_522, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_28, vertices_268, vertices_524, vertices_292, vertices_548, vertices_536, vertices_328, vertices_584, vertices_776, vertices_208, vertices_592, vertices_416, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_179), (false, vertices_29), (false, vertices_333), (false, vertices_421), (false, vertices_601), (false, vertices_465), (true, vertices_14), (true, vertices_518), (true, vertices_26), (true, vertices_522), (true, vertices_530), (true, vertices_546), (true, vertices_642), (true, vertices_524), (true, vertices_548), (true, vertices_776), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 15 else
  if p.val = (false, vertices_179) then 16 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_704) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_29), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 8 722 146 2
cert_row_4 1 0 4 6 7 8 930 162 3
cert_row_4 2 1 2 4 7 8 812 268 2
cert_row_4 3 2 5 6 7 8 968 328 2
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 722
cert_cover_5 4 0 0 3 5 6 146 722 2
cert_coverFacet 5 930
cert_cover_5 5 1 0 4 6 7 162 930 3
cert_coverFacet 6 812
cert_cover_5 6 2 1 2 4 7 268 812 2
cert_coverFacet 7 968
cert_cover_5 7 3 2 5 6 7 328 968 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0178

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0179.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0179

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 77, 837, 665, 457, 929, 94, 118, 294, 774, 538, 690, 802, 484, 248, 13, 69, 517, 73, 137, 521, 321, 385, 641, 769, 14, 86, 38, 262, 518, 26, 522, 50, 530, 290, 546, 770, 76, 100, 292, 324, 772, 88, 152, 536, 200, 112, 176, 656, 224, 416, 672, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_77, vertices_837, vertices_665, vertices_457, vertices_929, vertices_94, vertices_118, vertices_294, vertices_774, vertices_538, vertices_690, vertices_802, vertices_484, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_73, vertices_137, vertices_521, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_86, vertices_38, vertices_262, vertices_518, vertices_26, vertices_522, vertices_50, vertices_530, vertices_290, vertices_546, vertices_770, vertices_76, vertices_100, vertices_292, vertices_324, vertices_772, vertices_88, vertices_152, vertices_536, vertices_200, vertices_112, vertices_176, vertices_656, vertices_224, vertices_416, vertices_672, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_77), (false, vertices_837), (false, vertices_665), (false, vertices_457), (false, vertices_929), (true, vertices_86), (true, vertices_38), (true, vertices_262), (true, vertices_26), (true, vertices_50), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_100), (true, vertices_292), (true, vertices_88), (true, vertices_112), (true, vertices_176), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 16 else
  if p.val = (false, vertices_77) then 0 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_86) then 17 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 77 38 262 26 50 530 290 546 770 100 292 88 112 176 224 527 86 837 665 457 929
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 8 690 50 3
cert_row_2 1 0 1 3 5 86
cert_row_4 2 1 4 5 6 7 484 100 3
cert_row_4 3 2 3 4 5 6 248 88 2
cert_rows
cert_pivot_2 8 0 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 3 14 94 3
cert_coverFacet 1 118
cert_cover_5 1 1 0 1 3 4 86 118 3
cert_coverFacet 2 294
cert_cover_2 2 1 0 4 7 38 294 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 690
cert_cover_5 5 0 0 3 4 6 50 690 3
cert_coverFacet 6 802
cert_cover_2 6 4 0 7 8 290 802 3
cert_coverFacet 7 484
cert_cover_5 7 2 1 4 5 6 100 484 3
cert_coverFacet 8 248
cert_cover_5 8 3 2 3 4 5 88 248 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0179

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0180.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0180

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 661, 837, 389, 217, 361, 393, 678, 122, 186, 658, 866, 172, 812, 396, 133, 261, 517, 73, 137, 265, 81, 145, 529, 321, 577, 385, 58, 82, 146, 530, 98, 162, 546, 578, 642, 44, 140, 268, 164, 548, 388, 644, 772, 88, 152, 104, 168, 296, 392, 656, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_661, vertices_837, vertices_389, vertices_217, vertices_361, vertices_393, vertices_678, vertices_122, vertices_186, vertices_658, vertices_866, vertices_172, vertices_812, vertices_396] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_81, vertices_145, vertices_529, vertices_321, vertices_577, vertices_385, vertices_58, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_578, vertices_642, vertices_44, vertices_140, vertices_268, vertices_164, vertices_548, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_104, vertices_168, vertices_296, vertices_392, vertices_656, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_661), (false, vertices_837), (false, vertices_389), (false, vertices_217), (false, vertices_361), (false, vertices_393), (true, vertices_58), (true, vertices_146), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_642), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_164), (true, vertices_548), (true, vertices_168), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_393) then 1 else
  if p.val = (true, vertices_58) then 16 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
cert_nodeAtPriority_25 0 389 1 393 146 98 162 546 642 44 140 268 164 548 168 800 595 58 661 837 217 361
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 4 58
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 0 4 5 7 8 866 98 3
cert_row_4 3 1 2 4 7 8 812 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 5 58 122 3
cert_coverFacet 2 186
cert_cover_5 2 0 0 2 3 6 58 186 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 98 866 3
cert_coverFacet 5 172
cert_cover_2 5 2 1 4 6 44 172 3
cert_coverFacet 6 812
cert_cover_5 6 3 1 2 4 7 44 812 3
cert_coverFacet 7 396
cert_cover_2 7 2 1 6 7 140 396 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0180

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2763 : Certifies 2763 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0150.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2764 : Certifies 2764 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0151.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2765 : Certifies 2765 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0152.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2766 : Certifies 2766 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0153.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2767 : Certifies 2767 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0154.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2768 : Certifies 2768 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0155.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2769 : Certifies 2769 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0156.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2770 : Certifies 2770 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0157.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2771 : Certifies 2771 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0158.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2772 : Certifies 2772 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0159.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2773 : Certifies 2773 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0160.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2774 : Certifies 2774 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0161.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2775 : Certifies 2775 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0162.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2776 : Certifies 2776 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0163.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2777 : Certifies 2777 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0164.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2778 : Certifies 2778 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0165.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2779 : Certifies 2779 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0166.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2780 : Certifies 2780 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0167.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2781 : Certifies 2781 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0168.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2782 : Certifies 2782 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0169.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2783 : Certifies 2783 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0170.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2784 : Certifies 2784 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0172.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2785 : Certifies 2785 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0173.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2786 : Certifies 2786 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0174.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2787 : Certifies 2787 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0175.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2788 : Certifies 2788 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0176.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2789 : Certifies 2789 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0177.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2790 : Certifies 2790 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0178.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2791 : Certifies 2791 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0179.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2792 : Certifies 2792 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0180.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B091 (j : Fin 30) :
    Certifies (2763 + j.val) := by
  fin_cases j
  · exact projection_2763
  · exact projection_2764
  · exact projection_2765
  · exact projection_2766
  · exact projection_2767
  · exact projection_2768
  · exact projection_2769
  · exact projection_2770
  · exact projection_2771
  · exact projection_2772
  · exact projection_2773
  · exact projection_2774
  · exact projection_2775
  · exact projection_2776
  · exact projection_2777
  · exact projection_2778
  · exact projection_2779
  · exact projection_2780
  · exact projection_2781
  · exact projection_2782
  · exact projection_2783
  · exact projection_2784
  · exact projection_2785
  · exact projection_2786
  · exact projection_2787
  · exact projection_2788
  · exact projection_2789
  · exact projection_2790
  · exact projection_2791
  · exact projection_2792

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
