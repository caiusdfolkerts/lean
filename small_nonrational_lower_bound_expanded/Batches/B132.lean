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
/- Source: ProjectionCertificates/R_m16e10q1_0103.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0103

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 355, 707, 653, 213, 341, 314, 554, 778, 610, 188, 540, 788, 792, 744, 496, 67, 259, 515, 85, 133, 261, 517, 193, 321, 641, 42, 266, 522, 98, 290, 546, 578, 770, 28, 140, 524, 148, 276, 532, 772, 56, 280, 536, 168, 552, 648, 776, 176, 304, 208, 336, 784, 224, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_355, vertices_707, vertices_653, vertices_213, vertices_341, vertices_314, vertices_554, vertices_778, vertices_610, vertices_188, vertices_540, vertices_788, vertices_792, vertices_744, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_85, vertices_133, vertices_261, vertices_517, vertices_193, vertices_321, vertices_641, vertices_42, vertices_266, vertices_522, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_28, vertices_140, vertices_524, vertices_148, vertices_276, vertices_532, vertices_772, vertices_56, vertices_280, vertices_536, vertices_168, vertices_552, vertices_648, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_784, vertices_224, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_355), (false, vertices_707), (false, vertices_653), (false, vertices_213), (false, vertices_341), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_546), (true, vertices_28), (true, vertices_532), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_552), (true, vertices_776), (true, vertices_176), (true, vertices_304), (true, vertices_784), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 25 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 18 else
  if p.val = (false, vertices_355) then 19 else
  if p.val = (false, vertices_707) then 20 else
  if p.val = (false, vertices_653) then 22 else
  if p.val = (false, vertices_213) then 23 else
  if p.val = (false, vertices_341) then 24 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_608) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 25 => Sum.inl 2
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 7 314 42 2
cert_row_4 1 1 2 3 4 6 188 28 3
cert_row_4 2 2 4 5 6 8 744 168 2
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 314
cert_cover_5 0 0 0 2 3 4 42 314 2
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 610
cert_cover_2 3 4 0 5 8 98 610 3
cert_coverFacet 4 188
cert_cover_5 4 1 1 2 3 4 28 188 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coverFacet 8 744
cert_cover_5 8 2 2 4 5 6 168 744 2
cert_coverFacet 9 496
cert_cover_5 9 3 3 4 5 6 176 496 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0103

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0104.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0104

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 395, 227, 611, 185, 809, 598, 454, 60, 284, 556, 780, 564, 340, 472, 752, 99, 131, 259, 515, 41, 137, 265, 161, 545, 769, 70, 262, 518, 194, 578, 386, 28, 44, 268, 524, 52, 84, 276, 532, 548, 324, 772, 56, 152, 280, 552, 392, 776, 176, 560, 208, 336, 592, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_395, vertices_227, vertices_611, vertices_185, vertices_809, vertices_598, vertices_454, vertices_60, vertices_284, vertices_556, vertices_780, vertices_564, vertices_340, vertices_472, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_99, vertices_131, vertices_259, vertices_515, vertices_41, vertices_137, vertices_265, vertices_161, vertices_545, vertices_769, vertices_70, vertices_262, vertices_518, vertices_194, vertices_578, vertices_386, vertices_28, vertices_44, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_532, vertices_548, vertices_324, vertices_772, vertices_56, vertices_152, vertices_280, vertices_552, vertices_392, vertices_776, vertices_176, vertices_560, vertices_208, vertices_336, vertices_592, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_395), (false, vertices_227), (false, vertices_611), (false, vertices_185), (false, vertices_809), (true, vertices_70), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_548), (true, vertices_324), (true, vertices_280), (true, vertices_560), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 17 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 18 else
  if p.val = (false, vertices_395) then 20 else
  if p.val = (false, vertices_227) then 21 else
  if p.val = (false, vertices_611) then 22 else
  if p.val = (false, vertices_185) then 24 else
  if p.val = (false, vertices_809) then 25 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_28) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_592) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 5 6 7 472 152 2
cert_row_4 1 0 1 5 6 7 454 70 3
cert_row_4 2 0 1 3 5 8 598 70 2
cert_row_4 3 3 4 5 6 8 752 176 2
cert_rows
cert_pivot_2 2 7 0 3
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 2 0 1 3 5 70 598 2
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 6 70 454 3
cert_coverFacet 2 60
cert_cover_2 2 2 1 3 4 28 60 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 556
cert_cover_2 4 2 1 4 8 44 556 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coverFacet 8 472
cert_cover_5 8 0 2 3 5 6 152 472 2
cert_coverFacet 9 752
cert_cover_5 9 3 3 4 5 6 176 752 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0104

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0105.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0105

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 565, 357, 453, 121, 721, 398, 774, 282, 538, 714, 818, 804, 312, 600, 488, 37, 325, 133, 517, 49, 81, 529, 97, 193, 641, 134, 262, 518, 26, 138, 266, 522, 274, 530, 642, 770, 292, 548, 388, 772, 56, 88, 280, 536, 104, 296, 200, 584, 392, 304, 560, 592, 352, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_565, vertices_357, vertices_453, vertices_121, vertices_721, vertices_398, vertices_774, vertices_282, vertices_538, vertices_714, vertices_818, vertices_804, vertices_312, vertices_600, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_325, vertices_133, vertices_517, vertices_49, vertices_81, vertices_529, vertices_97, vertices_193, vertices_641, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_642, vertices_770, vertices_292, vertices_548, vertices_388, vertices_772, vertices_56, vertices_88, vertices_280, vertices_536, vertices_104, vertices_296, vertices_200, vertices_584, vertices_392, vertices_304, vertices_560, vertices_592, vertices_352, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_565), (false, vertices_357), (false, vertices_453), (false, vertices_121), (false, vertices_721), (true, vertices_262), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_770), (true, vertices_772), (true, vertices_280), (true, vertices_536), (true, vertices_296), (true, vertices_200), (true, vertices_584), (true, vertices_392), (true, vertices_304), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 18 else
  if p.val = (false, vertices_565) then 20 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_121) then 24 else
  if p.val = (false, vertices_721) then 26 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_304) then 15 else
  if p.val = (true, vertices_800) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_4 1 0 3 4 7 8 818 274 2
cert_row_4 2 0 2 5 6 8 714 138 2
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 714
cert_cover_5 4 2 0 2 5 6 138 714 2
cert_coverFacet 5 818
cert_cover_5 5 1 0 3 4 7 274 818 2
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coverFacet 9 488
cert_cover_5 9 3 2 4 5 6 104 488 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0105

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0106.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0106

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 93, 285, 229, 805, 617, 422, 602, 154, 394, 658, 674, 802, 468, 408, 752, 29, 37, 69, 261, 73, 265, 521, 97, 545, 769, 26, 138, 266, 522, 146, 530, 162, 290, 546, 386, 642, 770, 84, 276, 164, 292, 196, 388, 88, 152, 280, 584, 392, 208, 592, 400, 656, 224, 608, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_93, vertices_285, vertices_229, vertices_805, vertices_617, vertices_422, vertices_602, vertices_154, vertices_394, vertices_658, vertices_674, vertices_802, vertices_468, vertices_408, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_37, vertices_69, vertices_261, vertices_73, vertices_265, vertices_521, vertices_97, vertices_545, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_84, vertices_276, vertices_164, vertices_292, vertices_196, vertices_388, vertices_88, vertices_152, vertices_280, vertices_584, vertices_392, vertices_208, vertices_592, vertices_400, vertices_656, vertices_224, vertices_608, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_93), (false, vertices_285), (false, vertices_229), (false, vertices_805), (false, vertices_617), (true, vertices_26), (true, vertices_138), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_388), (true, vertices_152), (true, vertices_392), (true, vertices_208), (true, vertices_592), (true, vertices_400), (true, vertices_656), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 23 19 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_93) then 20 else
  if p.val = (false, vertices_285) then 21 else
  if p.val = (false, vertices_229) then 24 else
  if p.val = (false, vertices_805) then 25 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_656) then 15 else
  if p.val = (true, vertices_672) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 23 => Sum.inl 1
  | 24 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_4 1 0 1 4 6 7 422 162 1
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 3 4 5 6 8 752 208 1
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 1 0 1 4 6 162 422 1
cert_coverFacet 1 602
cert_cover_5 1 0 0 2 3 5 26 602 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 802
cert_cover_2 6 4 0 7 8 290 802 3
cert_coverFacet 7 468
cert_cover_5 7 2 1 3 5 6 84 468 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 752
cert_cover_5 9 3 3 4 5 6 208 752 1
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0106

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0107.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0107

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 109, 589, 309, 901, 625, 654, 602, 234, 210, 402, 898, 300, 396, 424, 496, 77, 37, 261, 517, 49, 273, 529, 97, 577, 769, 74, 138, 522, 82, 146, 274, 530, 194, 386, 642, 770, 44, 140, 268, 524, 292, 388, 644, 104, 168, 296, 584, 392, 112, 304, 208, 592, 400, 224, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_109, vertices_589, vertices_309, vertices_901, vertices_625, vertices_654, vertices_602, vertices_234, vertices_210, vertices_402, vertices_898, vertices_300, vertices_396, vertices_424, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_77, vertices_37, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_97, vertices_577, vertices_769, vertices_74, vertices_138, vertices_522, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_268, vertices_524, vertices_292, vertices_388, vertices_644, vertices_104, vertices_168, vertices_296, vertices_584, vertices_392, vertices_112, vertices_304, vertices_208, vertices_592, vertices_400, vertices_224, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_109), (false, vertices_589), (false, vertices_309), (false, vertices_901), (false, vertices_625), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_140), (true, vertices_268), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_208), (true, vertices_400), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 22 19 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_109) then 20 else
  if p.val = (false, vertices_589) then 21 else
  if p.val = (false, vertices_309) then 23 else
  if p.val = (false, vertices_901) then 24 else
  if p.val = (false, vertices_625) then 26 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_4 1 0 2 3 5 8 602 74 2
cert_row_4 2 0 2 4 5 6 234 74 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 8 0 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 602
cert_cover_5 1 1 0 2 3 5 74 602 2
cert_coverFacet 2 234
cert_cover_5 2 2 0 2 4 5 74 234 2
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 396
cert_cover_2 7 2 1 6 7 140 396 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coverFacet 9 496
cert_cover_5 9 3 3 4 5 6 112 496 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0107

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0108.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0108

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 355, 707, 117, 597, 313, 654, 394, 778, 450, 156, 796, 180, 740, 184, 488, 67, 259, 515, 85, 49, 273, 529, 97, 289, 577, 138, 266, 522, 194, 322, 386, 642, 770, 28, 140, 524, 52, 148, 532, 100, 164, 580, 644, 56, 152, 280, 168, 296, 392, 776, 176, 784, 224, 352, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_355, vertices_707, vertices_117, vertices_597, vertices_313, vertices_654, vertices_394, vertices_778, vertices_450, vertices_156, vertices_796, vertices_180, vertices_740, vertices_184, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_85, vertices_49, vertices_273, vertices_529, vertices_97, vertices_289, vertices_577, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_28, vertices_140, vertices_524, vertices_52, vertices_148, vertices_532, vertices_100, vertices_164, vertices_580, vertices_644, vertices_56, vertices_152, vertices_280, vertices_168, vertices_296, vertices_392, vertices_776, vertices_176, vertices_784, vertices_224, vertices_352, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_355), (false, vertices_707), (false, vertices_117), (false, vertices_597), (false, vertices_313), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_386), (true, vertices_28), (true, vertices_140), (true, vertices_524), (true, vertices_148), (true, vertices_164), (true, vertices_644), (true, vertices_152), (true, vertices_168), (true, vertices_392), (true, vertices_776), (true, vertices_176), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_355) then 19 else
  if p.val = (false, vertices_707) then 20 else
  if p.val = (false, vertices_117) then 22 else
  if p.val = (false, vertices_597) then 23 else
  if p.val = (false, vertices_313) then 25 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 24 => Sum.inl 2
  | 25 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_4 1 1 2 3 7 8 796 28 3
cert_row_4 2 1 4 5 6 8 740 100 3
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 450
cert_cover_2 3 5 0 6 7 194 450 3
cert_coverFacet 4 156
cert_cover_2 4 2 1 3 6 28 156 3
cert_coverFacet 5 796
cert_cover_5 5 1 1 2 3 7 28 796 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 740
cert_cover_5 7 2 1 4 5 6 100 740 3
cert_coverFacet 8 184
cert_cover_2 8 3 2 4 6 56 184 3
cert_coverFacet 9 488
cert_cover_5 9 3 2 4 5 6 168 488 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0108

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0109.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0109

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 535, 651, 419, 357, 677, 602, 282, 394, 620, 852, 216, 408, 232, 680, 496, 23, 131, 259, 515, 37, 261, 517, 161, 289, 641, 26, 138, 266, 522, 274, 530, 386, 276, 532, 100, 548, 324, 580, 88, 152, 280, 104, 168, 552, 200, 584, 392, 648, 208, 336, 592, 400, 224, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_535, vertices_651, vertices_419, vertices_357, vertices_677, vertices_602, vertices_282, vertices_394, vertices_620, vertices_852, vertices_216, vertices_408, vertices_232, vertices_680, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_131, vertices_259, vertices_515, vertices_37, vertices_261, vertices_517, vertices_161, vertices_289, vertices_641, vertices_26, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_386, vertices_276, vertices_532, vertices_100, vertices_548, vertices_324, vertices_580, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_552, vertices_200, vertices_584, vertices_392, vertices_648, vertices_208, vertices_336, vertices_592, vertices_400, vertices_224, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_535), (false, vertices_651), (false, vertices_419), (false, vertices_357), (false, vertices_677), (true, vertices_26), (true, vertices_266), (true, vertices_580), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_104), (true, vertices_168), (true, vertices_552), (true, vertices_200), (true, vertices_584), (true, vertices_392), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_400), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 23 17 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 20 else
  if p.val = (false, vertices_535) then 21 else
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_419) then 22 else
  if p.val = (false, vertices_357) then 24 else
  if p.val = (false, vertices_677) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_580) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_224) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 23 => Sum.inl 1
  | 24 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_4 1 1 2 4 5 8 620 100 1
cert_row_4 2 1 3 5 7 8 852 276 2
cert_row_4 3 3 4 5 6 7 496 208 1
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 602
cert_cover_5 0 0 0 2 3 5 26 602 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 620
cert_cover_5 3 1 1 2 4 5 100 620 1
cert_coverFacet 4 852
cert_cover_5 4 2 1 3 5 7 276 852 2
cert_coverFacet 5 216
cert_cover_2 5 3 2 5 6 88 216 3
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coverFacet 8 680
cert_cover_2 8 4 2 6 8 168 680 3
cert_coverFacet 9 496
cert_cover_5 9 3 3 4 5 6 208 496 1
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0109

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0110.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0110

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 397, 357, 709, 793, 833, 614, 678, 58, 602, 170, 370, 436, 184, 408, 848, 69, 133, 261, 137, 265, 521, 321, 577, 641, 769, 550, 26, 42, 138, 522, 50, 82, 98, 162, 578, 642, 100, 164, 292, 580, 388, 644, 56, 152, 280, 536, 168, 392, 176, 304, 336, 592, 400, 784, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_397, vertices_357, vertices_709, vertices_793, vertices_833, vertices_614, vertices_678, vertices_58, vertices_602, vertices_170, vertices_370, vertices_436, vertices_184, vertices_408, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_137, vertices_265, vertices_521, vertices_321, vertices_577, vertices_641, vertices_769, vertices_550, vertices_26, vertices_42, vertices_138, vertices_522, vertices_50, vertices_82, vertices_98, vertices_162, vertices_578, vertices_642, vertices_100, vertices_164, vertices_292, vertices_580, vertices_388, vertices_644, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_392, vertices_176, vertices_304, vertices_336, vertices_592, vertices_400, vertices_784, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_397), (false, vertices_357), (false, vertices_709), (false, vertices_793), (false, vertices_833), (true, vertices_550), (true, vertices_26), (true, vertices_42), (true, vertices_50), (true, vertices_82), (true, vertices_98), (true, vertices_162), (true, vertices_578), (true, vertices_164), (true, vertices_56), (true, vertices_152), (true, vertices_168), (true, vertices_176), (true, vertices_304), (true, vertices_336), (true, vertices_592), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_397) then 21 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_709) then 23 else
  if p.val = (false, vertices_793) then 25 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_550) then 19 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_592) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
cert_nodeAtPriority_63 833 26 42 50 82 98 162 578 164 56 152 168 176 304 336 592 400 651 550 397 357 709 793
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_2 1 0 1 4 8 550
cert_row_4 2 0 3 4 5 7 370 50 3
cert_row_4 3 1 3 4 6 7 436 164 1
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 1 0 1 4 5 550 614 3
cert_coverFacet 1 678
cert_cover_5 1 1 0 1 4 6 550 678 3
cert_coverFacet 2 58
cert_cover_2 2 2 0 3 4 26 58 3
cert_coverFacet 3 602
cert_cover_5 3 0 0 2 3 5 26 602 3
cert_coverFacet 4 170
cert_cover_2 4 2 0 4 6 42 170 3
cert_coverFacet 5 370
cert_cover_5 5 2 0 3 4 5 50 370 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 164 436 1
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 848
cert_cover_2 9 5 3 7 8 336 848 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0110

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0111.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0111

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 781, 405, 709, 617, 449, 182, 570, 794, 234, 210, 338, 820, 676, 464, 736, 133, 261, 517, 73, 265, 521, 193, 321, 577, 385, 538, 42, 74, 266, 50, 82, 146, 274, 162, 194, 322, 52, 148, 276, 164, 548, 644, 772, 104, 552, 776, 560, 208, 336, 400, 784, 224, 608, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_781, vertices_405, vertices_709, vertices_617, vertices_449, vertices_182, vertices_570, vertices_794, vertices_234, vertices_210, vertices_338, vertices_820, vertices_676, vertices_464, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_193, vertices_321, vertices_577, vertices_385, vertices_538, vertices_42, vertices_74, vertices_266, vertices_50, vertices_82, vertices_146, vertices_274, vertices_162, vertices_194, vertices_322, vertices_52, vertices_148, vertices_276, vertices_164, vertices_548, vertices_644, vertices_772, vertices_104, vertices_552, vertices_776, vertices_560, vertices_208, vertices_336, vertices_400, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_781), (false, vertices_405), (false, vertices_709), (false, vertices_617), (false, vertices_449), (true, vertices_538), (true, vertices_42), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_194), (true, vertices_52), (true, vertices_164), (true, vertices_548), (true, vertices_560), (true, vertices_208), (true, vertices_336), (true, vertices_784), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 18 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_405) then 22 else
  if p.val = (false, vertices_709) then 23 else
  if p.val = (false, vertices_617) then 25 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_538) then 19 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_672) then 16 else
  0
cert_priority
cert_nodeAtPriority_63 449 42 50 82 146 274 162 194 52 164 548 560 208 336 784 224 672 331 538 781 405 709 617
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 6 234 42 3
cert_row_2 1 0 2 3 8 538
cert_row_4 2 0 1 3 4 6 182 50 1
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 5 2 0 1
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 2 0 1 3 4 50 182 1
cert_coverFacet 1 570
cert_cover_5 1 1 0 2 3 4 538 570 3
cert_coverFacet 2 794
cert_cover_5 2 1 0 2 3 7 538 794 3
cert_coverFacet 3 234
cert_cover_5 3 0 0 2 4 5 42 234 3
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 820
cert_cover_5 6 3 1 3 4 7 52 820 3
cert_coverFacet 7 676
cert_cover_2 7 4 1 6 8 164 676 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coverFacet 9 736
cert_cover_2 9 5 4 6 8 224 736 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0111

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0112.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0112

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 333, 565, 789, 229, 617, 182, 154, 282, 714, 818, 674, 468, 408, 456, 736, 533, 37, 69, 261, 73, 265, 521, 97, 545, 769, 26, 138, 266, 522, 50, 146, 274, 162, 546, 642, 770, 52, 148, 276, 164, 196, 324, 152, 280, 200, 328, 584, 392, 560, 400, 784, 224, 608, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_333, vertices_565, vertices_789, vertices_229, vertices_617, vertices_182, vertices_154, vertices_282, vertices_714, vertices_818, vertices_674, vertices_468, vertices_408, vertices_456, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_533, vertices_37, vertices_69, vertices_261, vertices_73, vertices_265, vertices_521, vertices_97, vertices_545, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_162, vertices_546, vertices_642, vertices_770, vertices_52, vertices_148, vertices_276, vertices_164, vertices_196, vertices_324, vertices_152, vertices_280, vertices_200, vertices_328, vertices_584, vertices_392, vertices_560, vertices_400, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_333), (false, vertices_565), (false, vertices_789), (false, vertices_229), (false, vertices_617), (true, vertices_26), (true, vertices_138), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_546), (true, vertices_642), (true, vertices_148), (true, vertices_152), (true, vertices_280), (true, vertices_200), (true, vertices_392), (true, vertices_400), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 22 19 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_333) then 20 else
  if p.val = (false, vertices_565) then 23 else
  if p.val = (false, vertices_789) then 24 else
  if p.val = (false, vertices_229) then 25 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_672) then 14 else
  if p.val = (true, vertices_448) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 138 2
cert_row_4 1 0 3 4 7 8 818 50 3
cert_row_4 2 0 1 3 4 6 182 50 1
cert_row_4 3 1 3 5 6 7 468 148 2
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 2 0 1 3 4 50 182 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 714
cert_cover_5 3 0 0 2 5 6 138 714 2
cert_coverFacet 4 818
cert_cover_5 4 1 0 3 4 7 50 818 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 148 468 2
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coverFacet 9 736
cert_cover_2 9 5 4 6 8 224 736 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0112

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0113.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0113

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 285, 661, 357, 709, 817, 158, 538, 170, 810, 722, 226, 396, 452, 792, 488, 21, 69, 645, 261, 273, 529, 97, 289, 545, 577, 26, 42, 138, 522, 146, 530, 98, 162, 546, 194, 578, 28, 140, 268, 148, 196, 324, 388, 280, 536, 168, 296, 392, 776, 656, 784, 224, 352, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_285, vertices_661, vertices_357, vertices_709, vertices_817, vertices_158, vertices_538, vertices_170, vertices_810, vertices_722, vertices_226, vertices_396, vertices_452, vertices_792, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_645, vertices_261, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_577, vertices_26, vertices_42, vertices_138, vertices_522, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_28, vertices_140, vertices_268, vertices_148, vertices_196, vertices_324, vertices_388, vertices_280, vertices_536, vertices_168, vertices_296, vertices_392, vertices_776, vertices_656, vertices_784, vertices_224, vertices_352, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_285), (false, vertices_661), (false, vertices_357), (false, vertices_709), (false, vertices_817), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_194), (true, vertices_140), (true, vertices_388), (true, vertices_536), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_776), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 19 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 18 else
  if p.val = (false, vertices_285) then 20 else
  if p.val = (false, vertices_661) then 22 else
  if p.val = (false, vertices_357) then 23 else
  if p.val = (false, vertices_709) then 24 else
  if p.val = (false, vertices_817) then 26 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_776) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 6 158 26 1
cert_row_4 1 0 3 5 6 8 722 146 2
cert_row_4 2 0 2 4 7 8 810 42 3
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 26 158 1
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 170
cert_cover_2 2 2 0 4 6 42 170 3
cert_coverFacet 3 810
cert_cover_5 3 2 0 2 4 7 42 810 3
cert_coverFacet 4 722
cert_cover_5 4 1 0 3 5 6 146 722 2
cert_coverFacet 5 226
cert_cover_2 5 4 0 5 6 98 226 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 452
cert_cover_2 7 5 1 6 7 196 452 3
cert_coverFacet 8 792
cert_cover_2 8 3 2 7 8 280 792 3
cert_coverFacet 9 488
cert_cover_5 9 3 2 4 5 6 168 488 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0113

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0114.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0114

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 301, 781, 181, 709, 233, 662, 794, 362, 210, 338, 706, 820, 432, 464, 480, 269, 37, 133, 517, 41, 73, 521, 161, 193, 577, 74, 266, 522, 82, 146, 274, 530, 194, 322, 578, 642, 52, 148, 532, 292, 644, 772, 104, 296, 776, 176, 304, 208, 336, 400, 784, 224, 352, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_301, vertices_781, vertices_181, vertices_709, vertices_233, vertices_662, vertices_794, vertices_362, vertices_210, vertices_338, vertices_706, vertices_820, vertices_432, vertices_464, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_269, vertices_37, vertices_133, vertices_517, vertices_41, vertices_73, vertices_521, vertices_161, vertices_193, vertices_577, vertices_74, vertices_266, vertices_522, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_52, vertices_148, vertices_532, vertices_292, vertices_644, vertices_772, vertices_104, vertices_296, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_400, vertices_784, vertices_224, vertices_352, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_301), (false, vertices_781), (false, vertices_181), (false, vertices_709), (false, vertices_233), (true, vertices_266), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_642), (true, vertices_532), (true, vertices_304), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_784), (true, vertices_352), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 23 19 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 18 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_181) then 24 else
  if p.val = (false, vertices_709) then 25 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_416) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 23 => Sum.inl 1
  | 24 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_4 1 0 2 4 5 7 362 74 2
cert_row_4 2 0 2 3 7 8 794 266 2
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 6 5 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 794
cert_cover_5 1 2 0 2 3 7 266 794 2
cert_coverFacet 2 362
cert_cover_5 2 1 0 2 4 5 74 362 2
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 820
cert_cover_5 6 3 1 3 4 7 52 820 3
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coverFacet 9 480
cert_cover_2 9 5 4 6 7 224 480 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0114

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0115.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0115

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 589, 213, 405, 805, 457, 310, 154, 282, 682, 242, 802, 628, 408, 712, 736, 149, 69, 261, 517, 73, 265, 521, 193, 385, 769, 26, 138, 266, 522, 50, 146, 274, 162, 290, 546, 770, 52, 84, 276, 292, 548, 580, 152, 280, 200, 584, 392, 648, 112, 208, 400, 224, 608, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_589, vertices_213, vertices_405, vertices_805, vertices_457, vertices_310, vertices_154, vertices_282, vertices_682, vertices_242, vertices_802, vertices_628, vertices_408, vertices_712, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_149, vertices_69, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_193, vertices_385, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_770, vertices_52, vertices_84, vertices_276, vertices_292, vertices_548, vertices_580, vertices_152, vertices_280, vertices_200, vertices_584, vertices_392, vertices_648, vertices_112, vertices_208, vertices_400, vertices_224, vertices_608, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_589), (false, vertices_213), (false, vertices_405), (false, vertices_805), (false, vertices_457), (true, vertices_26), (true, vertices_138), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_52), (true, vertices_152), (true, vertices_280), (true, vertices_648), (true, vertices_112), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 22 19 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_589) then 20 else
  if p.val = (false, vertices_213) then 23 else
  if p.val = (false, vertices_405) then 24 else
  if p.val = (false, vertices_805) then 25 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_608) then 14 else
  if p.val = (true, vertices_672) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 50 1
cert_row_4 1 0 2 4 6 8 682 138 2
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 50 310 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 682
cert_cover_5 3 1 0 2 4 6 138 682 2
cert_coverFacet 4 242
cert_cover_5 4 2 0 3 4 5 50 242 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 628
cert_cover_5 6 3 1 3 4 5 52 628 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 712
cert_cover_2 8 5 2 6 8 200 712 3
cert_coverFacet 9 736
cert_cover_2 9 5 4 6 8 224 736 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0115

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0116.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0116

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 781, 677, 453, 409, 657, 358, 218, 810, 458, 594, 610, 244, 804, 624, 688, 133, 261, 517, 25, 265, 521, 145, 529, 385, 641, 26, 202, 266, 522, 82, 530, 98, 290, 546, 322, 578, 100, 164, 292, 548, 196, 324, 772, 152, 392, 776, 112, 176, 560, 208, 592, 656, 608, 672, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_781, vertices_677, vertices_453, vertices_409, vertices_657, vertices_358, vertices_218, vertices_810, vertices_458, vertices_594, vertices_610, vertices_244, vertices_804, vertices_624, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_265, vertices_521, vertices_145, vertices_529, vertices_385, vertices_641, vertices_26, vertices_202, vertices_266, vertices_522, vertices_82, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_100, vertices_164, vertices_292, vertices_548, vertices_196, vertices_324, vertices_772, vertices_152, vertices_392, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_592, vertices_656, vertices_608, vertices_672, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_781), (false, vertices_677), (false, vertices_453), (false, vertices_409), (false, vertices_657), (true, vertices_202), (true, vertices_266), (true, vertices_82), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_578), (true, vertices_100), (true, vertices_292), (true, vertices_112), (true, vertices_176), (true, vertices_560), (true, vertices_208), (true, vertices_592), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 18 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_453) then 23 else
  if p.val = (false, vertices_409) then 25 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_202) then 19 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_608) then 15 else
  if p.val = (true, vertices_800) then 16 else
  0
cert_priority
cert_nodeAtPriority_63 657 266 82 98 290 546 322 578 100 292 112 176 560 208 592 608 800 539 202 781 677 453 409
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 266 2
cert_row_2 1 0 2 5 6 202
cert_row_4 2 0 1 4 5 7 358 98 1
cert_row_4 3 1 3 4 5 6 244 100 1
cert_rows
cert_pivot_2 8 2 0 1
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 2 0 1 4 5 98 358 1
cert_coverFacet 1 218
cert_cover_5 1 1 0 2 3 5 26 218 3
cert_coverFacet 2 810
cert_cover_5 2 0 0 2 4 7 266 810 2
cert_coverFacet 3 458
cert_cover_5 3 1 0 2 5 7 202 458 3
cert_coverFacet 4 594
cert_cover_2 4 3 0 5 8 82 594 3
cert_coverFacet 5 610
cert_cover_2 5 4 0 5 8 98 610 3
cert_coverFacet 6 244
cert_cover_5 6 3 1 3 4 5 100 244 1
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coverFacet 8 624
cert_cover_2 8 4 3 5 8 112 624 3
cert_coverFacet 9 688
cert_cover_2 9 4 3 6 8 176 688 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0116

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0117.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0117

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 781, 341, 613, 457, 705, 310, 806, 58, 794, 170, 738, 244, 184, 408, 464, 69, 261, 517, 137, 265, 521, 193, 321, 577, 641, 294, 26, 42, 138, 522, 50, 274, 162, 546, 642, 770, 52, 84, 276, 100, 548, 772, 56, 152, 280, 168, 392, 776, 176, 208, 336, 400, 224, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_781, vertices_341, vertices_613, vertices_457, vertices_705, vertices_310, vertices_806, vertices_58, vertices_794, vertices_170, vertices_738, vertices_244, vertices_184, vertices_408, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_577, vertices_641, vertices_294, vertices_26, vertices_42, vertices_138, vertices_522, vertices_50, vertices_274, vertices_162, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_276, vertices_100, vertices_548, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_392, vertices_776, vertices_176, vertices_208, vertices_336, vertices_400, vertices_224, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_781), (false, vertices_341), (false, vertices_613), (false, vertices_457), (false, vertices_705), (true, vertices_294), (true, vertices_26), (true, vertices_42), (true, vertices_50), (true, vertices_274), (true, vertices_162), (true, vertices_546), (true, vertices_770), (true, vertices_52), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_176), (true, vertices_208), (true, vertices_400), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_341) then 22 else
  if p.val = (false, vertices_613) then 23 else
  if p.val = (false, vertices_457) then 25 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_294) then 19 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_224) then 16 else
  0
cert_priority
cert_nodeAtPriority_63 705 26 42 50 274 162 546 770 52 56 152 280 168 176 208 400 224 651 294 781 341 613 457
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 7 8 794 26 3
cert_row_2 1 0 1 4 7 294
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 1 0 1 3 4 294 310 2
cert_coverFacet 1 806
cert_cover_5 1 1 0 1 4 8 294 806 3
cert_coverFacet 2 58
cert_cover_2 2 2 0 3 4 26 58 3
cert_coverFacet 3 794
cert_cover_5 3 0 0 2 3 7 26 794 3
cert_coverFacet 4 170
cert_cover_2 4 2 0 4 6 42 170 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 162 738 2
cert_coverFacet 6 244
cert_cover_5 6 3 1 3 4 5 52 244 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0117

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0118.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0118

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 333, 789, 709, 433, 449, 206, 654, 570, 362, 114, 210, 812, 240, 816, 480, 69, 261, 517, 145, 273, 529, 193, 321, 385, 641, 142, 42, 74, 522, 50, 82, 146, 530, 98, 194, 642, 76, 268, 524, 196, 644, 772, 296, 552, 328, 112, 176, 304, 560, 208, 784, 224, 352, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_333, vertices_789, vertices_709, vertices_433, vertices_449, vertices_206, vertices_654, vertices_570, vertices_362, vertices_114, vertices_210, vertices_812, vertices_240, vertices_816, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_385, vertices_641, vertices_142, vertices_42, vertices_74, vertices_522, vertices_50, vertices_82, vertices_146, vertices_530, vertices_98, vertices_194, vertices_642, vertices_76, vertices_268, vertices_524, vertices_196, vertices_644, vertices_772, vertices_296, vertices_552, vertices_328, vertices_112, vertices_176, vertices_304, vertices_560, vertices_208, vertices_784, vertices_224, vertices_352, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_333), (false, vertices_789), (false, vertices_709), (false, vertices_433), (false, vertices_449), (true, vertices_142), (true, vertices_42), (true, vertices_74), (true, vertices_522), (true, vertices_50), (true, vertices_82), (true, vertices_98), (true, vertices_194), (true, vertices_524), (true, vertices_296), (true, vertices_552), (true, vertices_112), (true, vertices_560), (true, vertices_208), (true, vertices_224), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 18 else
  if p.val = (false, vertices_333) then 21 else
  if p.val = (false, vertices_789) then 22 else
  if p.val = (false, vertices_709) then 23 else
  if p.val = (false, vertices_433) then 26 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_142) then 19 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_352) then 15 else
  if p.val = (true, vertices_800) then 16 else
  0
cert_priority
cert_nodeAtPriority_45 449 42 74 522 50 82 98 194 524 296 552 112 560 208 224 352 800 659 142 333 789 709 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 6 142
cert_row_4 1 0 2 3 4 8 570 42 2
cert_row_4 2 0 2 4 5 7 362 42 3
cert_row_4 3 1 2 4 7 8 812 268 2
cert_rows
cert_pivot_2 6 3 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 142 206 3
cert_coverFacet 1 654
cert_cover_5 1 0 0 1 2 8 142 654 3
cert_coverFacet 2 570
cert_cover_5 2 1 0 2 3 4 42 570 2
cert_coverFacet 3 362
cert_cover_5 3 2 0 2 4 5 42 362 3
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 210
cert_cover_2 5 3 0 5 6 82 210 3
cert_coverFacet 6 812
cert_cover_5 6 3 1 2 4 7 268 812 2
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coverFacet 8 816
cert_cover_2 8 4 3 7 8 304 816 3
cert_coverFacet 9 480
cert_cover_2 9 5 4 6 7 224 480 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0118

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0119.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0119

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 301, 557, 341, 709, 457, 598, 570, 426, 178, 210, 706, 788, 804, 496, 816, 45, 69, 261, 517, 137, 265, 521, 193, 321, 641, 42, 138, 522, 50, 82, 146, 530, 162, 194, 578, 642, 84, 276, 532, 292, 548, 580, 772, 296, 552, 392, 176, 304, 560, 208, 336, 784, 416, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_301, vertices_557, vertices_341, vertices_709, vertices_457, vertices_598, vertices_570, vertices_426, vertices_178, vertices_210, vertices_706, vertices_788, vertices_804, vertices_496, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_45, vertices_69, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_641, vertices_42, vertices_138, vertices_522, vertices_50, vertices_82, vertices_146, vertices_530, vertices_162, vertices_194, vertices_578, vertices_642, vertices_84, vertices_276, vertices_532, vertices_292, vertices_548, vertices_580, vertices_772, vertices_296, vertices_552, vertices_392, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_784, vertices_416, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_301), (false, vertices_557), (false, vertices_341), (false, vertices_709), (false, vertices_457), (true, vertices_42), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_194), (true, vertices_578), (true, vertices_532), (true, vertices_772), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_208), (true, vertices_784), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 23 19 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_557) then 21 else
  if p.val = (false, vertices_341) then 24 else
  if p.val = (false, vertices_709) then 25 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_416) then 15 else
  if p.val = (true, vertices_800) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 23 => Sum.inl 1
  | 24 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 82 1
cert_row_4 1 0 2 3 4 8 570 42 2
cert_row_4 2 0 2 4 6 7 426 42 3
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 1 8 0 3
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 82 598 1
cert_coverFacet 1 570
cert_cover_5 1 1 0 2 3 4 42 570 2
cert_coverFacet 2 426
cert_cover_5 2 2 0 2 4 6 42 426 3
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 176 496 2
cert_coverFacet 9 816
cert_cover_2 9 4 3 7 8 304 816 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0119

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0120.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0120

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 659, 419, 569, 241, 801, 334, 582, 450, 706, 220, 668, 812, 708, 376, 480, 131, 259, 515, 49, 145, 529, 161, 289, 545, 769, 70, 262, 518, 194, 322, 578, 386, 642, 156, 76, 268, 524, 196, 580, 644, 772, 56, 88, 536, 296, 552, 328, 112, 208, 656, 224, 352, 416, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_659, vertices_419, vertices_569, vertices_241, vertices_801, vertices_334, vertices_582, vertices_450, vertices_706, vertices_220, vertices_668, vertices_812, vertices_708, vertices_376, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_49, vertices_145, vertices_529, vertices_161, vertices_289, vertices_545, vertices_769, vertices_70, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_156, vertices_76, vertices_268, vertices_524, vertices_196, vertices_580, vertices_644, vertices_772, vertices_56, vertices_88, vertices_536, vertices_296, vertices_552, vertices_328, vertices_112, vertices_208, vertices_656, vertices_224, vertices_352, vertices_416, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_659), (false, vertices_419), (false, vertices_569), (false, vertices_241), (false, vertices_801), (true, vertices_70), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_156), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_196), (true, vertices_580), (true, vertices_644), (true, vertices_88), (true, vertices_296), (true, vertices_328), (true, vertices_352), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 18 else
  if p.val = (false, vertices_659) then 19 else
  if p.val = (false, vertices_419) then 20 else
  if p.val = (false, vertices_569) then 24 else
  if p.val = (false, vertices_241) then 26 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_156) then 22 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_448) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 6 156
cert_row_4 1 0 1 2 5 7 334 70 2
cert_row_4 2 1 2 4 7 8 812 268 2
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 1 0 1 2 5 70 334 2
cert_coverFacet 1 582
cert_cover_2 1 1 0 5 8 70 582 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 706
cert_cover_2 3 5 0 6 8 194 706 3
cert_coverFacet 4 220
cert_cover_5 4 0 1 2 3 5 156 220 3
cert_coverFacet 5 668
cert_cover_5 5 0 1 2 3 8 156 668 3
cert_coverFacet 6 812
cert_cover_5 6 2 1 2 4 7 268 812 2
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coverFacet 8 376
cert_cover_5 8 3 2 3 4 5 56 376 3
cert_coverFacet 9 480
cert_cover_2 9 5 4 6 7 224 480 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0120

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0121.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0121

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 589, 805, 325, 625, 465, 417, 654, 122, 154, 618, 930, 348, 396, 900, 408, 69, 261, 517, 49, 81, 145, 161, 289, 545, 321, 577, 385, 26, 106, 138, 522, 50, 146, 162, 546, 642, 76, 140, 268, 524, 324, 388, 644, 772, 88, 152, 280, 584, 392, 112, 336, 400, 608, 416, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_589, vertices_805, vertices_325, vertices_625, vertices_465, vertices_417, vertices_654, vertices_122, vertices_154, vertices_618, vertices_930, vertices_348, vertices_396, vertices_900, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_49, vertices_81, vertices_145, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_26, vertices_106, vertices_138, vertices_522, vertices_50, vertices_146, vertices_162, vertices_546, vertices_642, vertices_76, vertices_140, vertices_268, vertices_524, vertices_324, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_584, vertices_392, vertices_112, vertices_336, vertices_400, vertices_608, vertices_416, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_589), (false, vertices_805), (false, vertices_325), (false, vertices_625), (false, vertices_465), (false, vertices_417), (true, vertices_26), (true, vertices_106), (true, vertices_138), (true, vertices_522), (true, vertices_546), (true, vertices_642), (true, vertices_140), (true, vertices_268), (true, vertices_388), (true, vertices_644), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_392), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 23 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 17 else
  if p.val = (false, vertices_589) then 20 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (false, vertices_465) then 25 else
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
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_106), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 5 7 348 76 2
cert_row_2 1 0 2 4 5 106
cert_row_4 2 0 1 2 6 8 654 138 1
cert_row_4 3 0 4 6 7 8 930 162 3
cert_rows
cert_pivot_2 3 5 1 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 138 654 1
cert_coverFacet 1 122
cert_cover_5 1 1 0 2 3 4 26 122 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 618
cert_cover_5 3 1 0 2 4 8 106 618 3
cert_coverFacet 4 930
cert_cover_5 4 3 0 4 6 7 162 930 3
cert_coverFacet 5 348
cert_cover_5 5 0 1 2 3 5 76 348 2
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 900
cert_cover_2 7 6 1 7 8 388 900 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0121

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0122.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0122

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 557, 57, 601, 433, 209, 865, 654, 358, 614, 390, 722, 412, 300, 312, 664, 25, 41, 521, 49, 81, 145, 289, 545, 193, 321, 577, 385, 102, 134, 262, 518, 194, 322, 578, 386, 642, 44, 140, 268, 524, 292, 548, 388, 56, 152, 280, 536, 296, 648, 304, 208, 592, 400, 656, 352, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_557, vertices_57, vertices_601, vertices_433, vertices_209, vertices_865, vertices_654, vertices_358, vertices_614, vertices_390, vertices_722, vertices_412, vertices_300, vertices_312, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_521, vertices_49, vertices_81, vertices_145, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_102, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_44, vertices_140, vertices_268, vertices_524, vertices_292, vertices_548, vertices_388, vertices_56, vertices_152, vertices_280, vertices_536, vertices_296, vertices_648, vertices_304, vertices_208, vertices_592, vertices_400, vertices_656, vertices_352, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_557), (false, vertices_57), (false, vertices_601), (false, vertices_433), (false, vertices_209), (false, vertices_865), (true, vertices_102), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_578), (true, vertices_642), (true, vertices_140), (true, vertices_268), (true, vertices_292), (true, vertices_388), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_648), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 17 else
  if p.val = (false, vertices_557) then 20 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_601) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_209) then 1 else
  if p.val = (false, vertices_865) then 26 else
  if p.val = (true, vertices_102) then 18 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_656) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_57), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 5 102
cert_row_4 1 0 3 5 6 8 722 194 1
cert_row_4 2 0 1 2 6 8 654 134 2
cert_row_4 3 1 2 3 6 7 412 140 2
cert_rows
cert_pivot_2 4 5 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 134 654 2
cert_coverFacet 1 358
cert_cover_5 1 0 0 1 4 7 102 358 3
cert_coverFacet 2 614
cert_cover_5 2 0 0 1 4 8 102 614 3
cert_coverFacet 3 390
cert_cover_2 3 1 0 6 7 134 390 3
cert_coverFacet 4 722
cert_cover_5 4 1 0 3 5 6 194 722 1
cert_coverFacet 5 412
cert_cover_5 5 3 1 2 3 6 140 412 2
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0122

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0123.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0123

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 211, 323, 643, 301, 677, 481, 842, 690, 594, 60, 604, 780, 564, 440, 472, 67, 131, 259, 515, 37, 261, 517, 161, 289, 193, 321, 641, 82, 146, 530, 322, 578, 642, 770, 28, 44, 268, 524, 52, 532, 548, 772, 56, 88, 408, 296, 328, 584, 776, 176, 560, 208, 592, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_211, vertices_323, vertices_643, vertices_301, vertices_677, vertices_481, vertices_842, vertices_690, vertices_594, vertices_60, vertices_604, vertices_780, vertices_564, vertices_440, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_37, vertices_261, vertices_517, vertices_161, vertices_289, vertices_193, vertices_321, vertices_641, vertices_82, vertices_146, vertices_530, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_56, vertices_88, vertices_408, vertices_296, vertices_328, vertices_584, vertices_776, vertices_176, vertices_560, vertices_208, vertices_592, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_211), (false, vertices_323), (false, vertices_643), (false, vertices_301), (false, vertices_677), (false, vertices_481), (true, vertices_530), (true, vertices_578), (true, vertices_28), (true, vertices_524), (true, vertices_52), (true, vertices_532), (true, vertices_56), (true, vertices_88), (true, vertices_408), (true, vertices_328), (true, vertices_584), (true, vertices_776), (true, vertices_176), (true, vertices_560), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_211) then 18 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_643) then 1 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_408) then 23 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_592) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 8 690 146 2
cert_row_2 1 2 3 6 7 408
cert_row_4 2 0 2 5 7 8 842 322 1
cert_row_4 3 1 2 3 5 8 604 28 3
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 842
cert_cover_5 0 2 0 2 5 7 322 842 1
cert_coverFacet 1 690
cert_cover_5 1 0 0 3 4 6 146 690 2
cert_coverFacet 2 594
cert_cover_2 2 3 0 5 8 82 594 3
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 604
cert_cover_5 4 3 1 2 3 5 28 604 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 440
cert_cover_5 7 1 2 3 4 6 56 440 3
cert_coverFacet 8 472
cert_cover_5 8 1 2 3 5 6 88 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0123

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0124.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0124

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 587, 211, 771, 345, 777, 433, 230, 614, 774, 572, 428, 780, 312, 600, 752, 67, 131, 259, 515, 73, 265, 521, 81, 145, 273, 385, 769, 102, 134, 262, 518, 194, 578, 770, 44, 268, 524, 164, 548, 388, 772, 56, 88, 280, 536, 296, 584, 776, 176, 304, 560, 208, 592, 224, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_587, vertices_211, vertices_771, vertices_345, vertices_777, vertices_433, vertices_230, vertices_614, vertices_774, vertices_572, vertices_428, vertices_780, vertices_312, vertices_600, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_73, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_385, vertices_769, vertices_102, vertices_134, vertices_262, vertices_518, vertices_194, vertices_578, vertices_770, vertices_44, vertices_268, vertices_524, vertices_164, vertices_548, vertices_388, vertices_772, vertices_56, vertices_88, vertices_280, vertices_536, vertices_296, vertices_584, vertices_776, vertices_176, vertices_304, vertices_560, vertices_208, vertices_592, vertices_224, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_587), (false, vertices_211), (false, vertices_771), (false, vertices_345), (false, vertices_777), (false, vertices_433), (true, vertices_102), (true, vertices_518), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_164), (true, vertices_548), (true, vertices_772), (true, vertices_56), (true, vertices_536), (true, vertices_296), (true, vertices_560), (true, vertices_592), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 16 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 17 else
  if p.val = (false, vertices_587) then 20 else
  if p.val = (false, vertices_211) then 21 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_345) then 23 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (false, vertices_433) then 25 else
  if p.val = (true, vertices_102) then 18 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_608) then 15 else
  0
cert_priority
cert_nodeAtPriority_50 0 771 1 777 518 44 268 524 164 548 772 56 536 296 560 592 224 608 391 102 587 211 345 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 5 102
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 1 2 3 4 8 572 44 2
cert_row_4 3 3 4 5 6 8 752 176 2
cert_rows
cert_pivot_2 0 7 1 3
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 0 0 1 4 6 102 230 3
cert_coverFacet 1 614
cert_cover_5 1 0 0 1 4 8 102 614 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 572
cert_cover_5 3 2 1 2 3 4 44 572 2
cert_coverFacet 4 428
cert_cover_5 4 1 1 2 4 6 44 428 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 176 752 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0124

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0125.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0125

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 781, 185, 281, 817, 737, 94, 526, 358, 774, 218, 962, 284, 244, 308, 864, 25, 137, 265, 521, 49, 273, 161, 545, 641, 769, 14, 70, 262, 518, 90, 138, 522, 194, 322, 642, 770, 28, 268, 524, 52, 84, 276, 100, 292, 772, 152, 280, 176, 304, 208, 224, 352, 608, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_781, vertices_185, vertices_281, vertices_817, vertices_737, vertices_94, vertices_526, vertices_358, vertices_774, vertices_218, vertices_962, vertices_284, vertices_244, vertices_308, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_521, vertices_49, vertices_273, vertices_161, vertices_545, vertices_641, vertices_769, vertices_14, vertices_70, vertices_262, vertices_518, vertices_90, vertices_138, vertices_522, vertices_194, vertices_322, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_100, vertices_292, vertices_772, vertices_152, vertices_280, vertices_176, vertices_304, vertices_208, vertices_224, vertices_352, vertices_608, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_781), (false, vertices_185), (false, vertices_281), (false, vertices_817), (false, vertices_737), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_90), (true, vertices_194), (true, vertices_322), (true, vertices_770), (true, vertices_28), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_100), (true, vertices_292), (true, vertices_208), (true, vertices_352), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_185) then 23 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_817) then 25 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_90) then 19 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_100) then 12 else
  if p.val = (true, vertices_292) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_352) then 15 else
  if p.val = (true, vertices_832) then 16 else
  0
cert_priority
cert_nodeAtPriority_66 281 14 70 262 518 194 322 770 28 52 84 276 100 292 208 352 832 651 90 781 185 817 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 0 1 4 5 7 358 70 2
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 14 94 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 358
cert_cover_5 2 2 0 1 4 5 70 358 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 218
cert_cover_5 4 0 0 2 3 6 90 218 3
cert_coverFacet 5 962
cert_cover_5 5 1 0 5 6 7 194 962 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 244
cert_cover_5 7 3 1 3 4 5 52 244 3
cert_coverFacet 8 308
cert_cover_2 8 3 1 4 7 52 308 3
cert_coverFacet 9 864
cert_cover_2 9 5 4 7 8 352 864 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0125

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0126.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0126

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 333, 141, 421, 665, 585, 737, 790, 842, 242, 306, 722, 188, 540, 780, 308, 13, 133, 261, 73, 137, 521, 97, 161, 289, 321, 577, 641, 50, 210, 274, 530, 98, 290, 322, 578, 770, 28, 140, 268, 524, 52, 276, 532, 164, 292, 772, 152, 536, 328, 584, 776, 176, 304, 656, 224, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_333, vertices_141, vertices_421, vertices_665, vertices_585, vertices_737, vertices_790, vertices_842, vertices_242, vertices_306, vertices_722, vertices_188, vertices_540, vertices_780, vertices_308] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_73, vertices_137, vertices_521, vertices_97, vertices_161, vertices_289, vertices_321, vertices_577, vertices_641, vertices_50, vertices_210, vertices_274, vertices_530, vertices_98, vertices_290, vertices_322, vertices_578, vertices_770, vertices_28, vertices_140, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_164, vertices_292, vertices_772, vertices_152, vertices_536, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_656, vertices_224, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_333), (false, vertices_141), (false, vertices_421), (false, vertices_665), (false, vertices_585), (false, vertices_737), (true, vertices_50), (true, vertices_210), (true, vertices_274), (true, vertices_530), (true, vertices_578), (true, vertices_770), (true, vertices_28), (true, vertices_524), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_772), (true, vertices_776), (true, vertices_176), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 17 else
  if p.val = (false, vertices_333) then 20 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_665) then 23 else
  if p.val = (false, vertices_585) then 1 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_210) then 18 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_304) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 1 141 0 585 50 274 530 578 770 28 524 52 276 532 772 776 176 304 355 210 333 421 665 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 4 6 188 28 3
cert_row_2 1 0 3 5 6 210
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 0 2 5 7 8 842 322 1
cert_rows
cert_pivot_2 4 6 1 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 842
cert_cover_5 1 3 0 2 5 7 322 842 1
cert_coverFacet 2 242
cert_cover_5 2 1 0 3 4 5 50 242 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 722
cert_cover_5 4 1 0 3 5 8 210 722 3
cert_coverFacet 5 188
cert_cover_5 5 0 1 2 3 4 28 188 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 308
cert_cover_2 8 3 1 4 7 52 308 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0126

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0127.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0127

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 211, 675, 323, 301, 549, 481, 602, 658, 834, 60, 540, 844, 692, 440, 472, 67, 131, 259, 515, 37, 261, 517, 161, 289, 545, 193, 321, 82, 146, 530, 322, 578, 642, 770, 28, 44, 268, 524, 52, 532, 548, 772, 56, 88, 408, 536, 296, 328, 584, 176, 208, 656, 416, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_211, vertices_675, vertices_323, vertices_301, vertices_549, vertices_481, vertices_602, vertices_658, vertices_834, vertices_60, vertices_540, vertices_844, vertices_692, vertices_440, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_37, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_82, vertices_146, vertices_530, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_56, vertices_88, vertices_408, vertices_536, vertices_296, vertices_328, vertices_584, vertices_176, vertices_208, vertices_656, vertices_416, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_211), (false, vertices_675), (false, vertices_323), (false, vertices_301), (false, vertices_549), (false, vertices_481), (true, vertices_530), (true, vertices_578), (true, vertices_28), (true, vertices_524), (true, vertices_52), (true, vertices_532), (true, vertices_56), (true, vertices_88), (true, vertices_408), (true, vertices_536), (true, vertices_328), (true, vertices_584), (true, vertices_176), (true, vertices_656), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_211) then 18 else
  if p.val = (false, vertices_675) then 19 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_301) then 21 else
  if p.val = (false, vertices_549) then 1 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_408) then 23 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_832) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_549), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 82 1
cert_row_4 1 1 2 5 7 8 844 268 2
cert_row_2 2 2 3 6 7 408
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 0 5 2 1
cert_heightProof 4
cert_coverFacet 0 602
cert_cover_5 0 0 0 2 3 5 82 602 1
cert_coverFacet 1 658
cert_cover_2 1 3 0 6 8 146 658 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 844
cert_cover_5 5 1 1 2 5 7 268 844 2
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 52 692 3
cert_coverFacet 7 440
cert_cover_5 7 2 2 3 4 6 56 440 3
cert_coverFacet 8 472
cert_cover_5 8 2 2 3 5 6 88 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0127

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0128.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0128

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 597, 421, 453, 217, 689, 302, 838, 666, 282, 554, 786, 344, 488, 680, 848, 37, 69, 389, 517, 81, 145, 529, 161, 545, 193, 38, 262, 518, 26, 42, 266, 522, 274, 530, 546, 770, 292, 324, 580, 88, 152, 280, 168, 296, 552, 200, 328, 648, 336, 592, 656, 784, 416, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_597, vertices_421, vertices_453, vertices_217, vertices_689, vertices_302, vertices_838, vertices_666, vertices_282, vertices_554, vertices_786, vertices_344, vertices_488, vertices_680, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_389, vertices_517, vertices_81, vertices_145, vertices_529, vertices_161, vertices_545, vertices_193, vertices_38, vertices_262, vertices_518, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_530, vertices_546, vertices_770, vertices_292, vertices_324, vertices_580, vertices_88, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_648, vertices_336, vertices_592, vertices_656, vertices_784, vertices_416, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_597), (false, vertices_421), (false, vertices_453), (false, vertices_217), (false, vertices_689), (true, vertices_262), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_770), (true, vertices_280), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_648), (true, vertices_336), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 18 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_217) then 24 else
  if p.val = (false, vertices_689) then 26 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_784) then 15 else
  if p.val = (true, vertices_832) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 26 3
cert_row_4 1 0 1 5 7 8 838 262 2
cert_row_4 2 0 1 2 4 7 302 38 2
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 3 8 0 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 2 0 1 2 4 38 302 2
cert_coverFacet 1 838
cert_cover_5 1 1 0 1 5 7 262 838 2
cert_coverFacet 2 666
cert_cover_5 2 0 0 2 3 6 26 666 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 554
cert_cover_2 4 2 0 4 8 42 554 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 168 488 2
cert_coverFacet 8 680
cert_cover_2 8 4 2 6 8 168 680 3
cert_coverFacet 9 848
cert_cover_2 9 5 3 7 8 336 848 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0128

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0129.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0129

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [211, 301, 341, 677, 709, 433, 558, 154, 538, 170, 850, 738, 844, 408, 792, 424, 37, 69, 645, 261, 81, 145, 273, 161, 289, 193, 26, 42, 138, 522, 82, 146, 530, 162, 546, 194, 578, 44, 268, 524, 548, 324, 580, 152, 280, 536, 168, 296, 392, 776, 336, 400, 784, 416, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_301, vertices_341, vertices_677, vertices_709, vertices_433, vertices_558, vertices_154, vertices_538, vertices_170, vertices_850, vertices_738, vertices_844, vertices_408, vertices_792, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_645, vertices_261, vertices_81, vertices_145, vertices_273, vertices_161, vertices_289, vertices_193, vertices_26, vertices_42, vertices_138, vertices_522, vertices_82, vertices_146, vertices_530, vertices_162, vertices_546, vertices_194, vertices_578, vertices_44, vertices_268, vertices_524, vertices_548, vertices_324, vertices_580, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_392, vertices_776, vertices_336, vertices_400, vertices_784, vertices_416, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_301), (false, vertices_341), (false, vertices_677), (false, vertices_709), (false, vertices_433), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_578), (true, vertices_524), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_392), (true, vertices_776), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 19 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 18 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_341) then 22 else
  if p.val = (false, vertices_677) then 23 else
  if p.val = (false, vertices_709) then 24 else
  if p.val = (false, vertices_433) then 26 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_776) then 14 else
  if p.val = (true, vertices_784) then 15 else
  if p.val = (true, vertices_832) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 7 8 850 82 3
cert_row_4 1 0 4 5 6 8 738 162 2
cert_row_4 2 0 1 2 4 8 558 42 1
cert_row_4 3 1 2 5 7 8 844 268 2
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 2 0 1 2 4 42 558 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 170
cert_cover_2 3 2 0 4 6 42 170 3
cert_coverFacet 4 850
cert_cover_5 4 0 0 3 5 7 82 850 3
cert_coverFacet 5 738
cert_cover_5 5 1 0 4 5 6 162 738 2
cert_coverFacet 6 844
cert_cover_5 6 3 1 2 5 7 268 844 2
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 792
cert_cover_2 8 3 2 7 8 280 792 3
cert_coverFacet 9 424
cert_cover_2 9 4 2 6 7 168 424 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0129

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0130.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0130

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 179, 659, 835, 713, 481, 62, 534, 774, 92, 300, 460, 852, 696, 600, 424, 147, 35, 259, 515, 161, 289, 193, 321, 577, 641, 22, 38, 262, 518, 50, 530, 770, 28, 44, 76, 268, 84, 532, 292, 324, 772, 56, 88, 536, 168, 296, 200, 584, 392, 648, 176, 592, 656, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_179, vertices_659, vertices_835, vertices_713, vertices_481, vertices_62, vertices_534, vertices_774, vertices_92, vertices_300, vertices_460, vertices_852, vertices_696, vertices_600, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_147, vertices_35, vertices_259, vertices_515, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_641, vertices_22, vertices_38, vertices_262, vertices_518, vertices_50, vertices_530, vertices_770, vertices_28, vertices_44, vertices_76, vertices_268, vertices_84, vertices_532, vertices_292, vertices_324, vertices_772, vertices_56, vertices_88, vertices_536, vertices_168, vertices_296, vertices_200, vertices_584, vertices_392, vertices_648, vertices_176, vertices_592, vertices_656, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_179), (false, vertices_659), (false, vertices_835), (false, vertices_713), (false, vertices_481), (true, vertices_22), (true, vertices_518), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_84), (true, vertices_532), (true, vertices_324), (true, vertices_772), (true, vertices_56), (true, vertices_88), (true, vertices_536), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 17 23 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 18 else
  if p.val = (false, vertices_179) then 20 else
  if p.val = (false, vertices_659) then 21 else
  if p.val = (false, vertices_835) then 22 else
  if p.val = (false, vertices_713) then 24 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_296) then 14 else
  if p.val = (true, vertices_392) then 15 else
  if p.val = (true, vertices_592) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
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
cert_row_4 0 0 1 2 3 4 62 22 2
cert_row_4 1 2 3 4 6 8 696 56 3
cert_row_4 2 1 2 5 6 7 460 76 3
cert_row_4 3 1 3 5 7 8 852 84 3
cert_rows
cert_pivot_2 0 4 2 1
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 22 62 2
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 92
cert_cover_2 3 2 1 3 5 28 92 3
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 460
cert_cover_5 5 2 1 2 5 6 76 460 3
cert_coverFacet 6 852
cert_cover_5 6 3 1 3 5 7 84 852 3
cert_coverFacet 7 696
cert_cover_5 7 1 2 3 4 6 56 696 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coverFacet 9 424
cert_cover_2 9 4 2 6 7 168 424 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0130

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0131.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0131

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 301, 597, 789, 229, 617, 214, 154, 282, 650, 850, 738, 404, 420, 440, 680, 533, 37, 69, 261, 41, 265, 521, 97, 577, 769, 26, 138, 266, 522, 82, 146, 274, 194, 578, 642, 770, 84, 148, 276, 164, 292, 196, 388, 152, 280, 168, 296, 552, 648, 592, 400, 784, 224, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_301, vertices_597, vertices_789, vertices_229, vertices_617, vertices_214, vertices_154, vertices_282, vertices_650, vertices_850, vertices_738, vertices_404, vertices_420, vertices_440, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_533, vertices_37, vertices_69, vertices_261, vertices_41, vertices_265, vertices_521, vertices_97, vertices_577, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_82, vertices_146, vertices_274, vertices_194, vertices_578, vertices_642, vertices_770, vertices_84, vertices_148, vertices_276, vertices_164, vertices_292, vertices_196, vertices_388, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_648, vertices_592, vertices_400, vertices_784, vertices_224, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_301), (false, vertices_597), (false, vertices_789), (false, vertices_229), (false, vertices_617), (true, vertices_26), (true, vertices_138), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_148), (true, vertices_388), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_648), (true, vertices_400), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 22 19 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_597) then 23 else
  if p.val = (false, vertices_789) then 24 else
  if p.val = (false, vertices_229) then 25 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_416) then 15 else
  if p.val = (true, vertices_672) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 82 1
cert_row_4 1 2 3 4 6 7 440 152 2
cert_row_4 2 0 3 5 7 8 850 82 3
cert_row_4 3 0 4 5 6 8 738 194 1
cert_rows
cert_pivot_2 1 2 3 0
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 82 214 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 850
cert_cover_5 4 2 0 3 5 7 82 850 3
cert_coverFacet 5 738
cert_cover_5 5 3 0 4 5 6 194 738 1
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coverFacet 8 440
cert_cover_5 8 1 2 3 4 6 152 440 2
cert_coverFacet 9 680
cert_cover_2 9 4 2 6 8 168 680 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0131

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0132.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0132

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 307, 451, 643, 333, 281, 713, 422, 178, 658, 796, 620, 820, 228, 452, 752, 19, 131, 259, 515, 25, 73, 265, 521, 273, 193, 321, 641, 50, 146, 530, 162, 290, 386, 642, 76, 268, 524, 788, 100, 164, 292, 548, 196, 324, 388, 280, 536, 584, 176, 304, 560, 656, 224, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_307, vertices_451, vertices_643, vertices_333, vertices_281, vertices_713, vertices_422, vertices_178, vertices_658, vertices_796, vertices_620, vertices_820, vertices_228, vertices_452, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_25, vertices_73, vertices_265, vertices_521, vertices_273, vertices_193, vertices_321, vertices_641, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_386, vertices_642, vertices_76, vertices_268, vertices_524, vertices_788, vertices_100, vertices_164, vertices_292, vertices_548, vertices_196, vertices_324, vertices_388, vertices_280, vertices_536, vertices_584, vertices_176, vertices_304, vertices_560, vertices_656, vertices_224, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_307), (false, vertices_451), (false, vertices_643), (false, vertices_333), (false, vertices_281), (false, vertices_713), (true, vertices_146), (true, vertices_162), (true, vertices_524), (true, vertices_788), (true, vertices_100), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_196), (true, vertices_388), (true, vertices_176), (true, vertices_560), (true, vertices_656), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 17 else
  if p.val = (false, vertices_307) then 18 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_333) then 21 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_713) then 24 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_788) then 22 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_608) then 15 else
  0
cert_priority
cert_nodeAtPriority_60 643 281 146 162 524 100 164 292 548 196 388 176 560 656 224 608 539 307 451 333 788 713
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 7 422 162 1
cert_row_2 1 1 3 7 8 788
cert_row_4 2 1 2 4 5 8 620 76 2
cert_row_4 3 3 4 5 6 8 752 176 2
cert_rows
cert_pivot_2 0 7 1 3
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 162 422 1
cert_coverFacet 1 178
cert_cover_2 1 3 0 4 6 50 178 3
cert_coverFacet 2 658
cert_cover_2 2 3 0 6 8 146 658 3
cert_coverFacet 3 796
cert_cover_5 3 1 1 2 3 7 268 796 2
cert_coverFacet 4 620
cert_cover_5 4 2 1 2 4 5 76 620 2
cert_coverFacet 5 820
cert_cover_5 5 1 1 3 4 7 788 820 2
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 452
cert_cover_2 7 5 1 6 7 196 452 3
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 176 752 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0132

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3993 : Certifies 3993 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0103.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3994 : Certifies 3994 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0104.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3995 : Certifies 3995 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0105.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3996 : Certifies 3996 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0106.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3997 : Certifies 3997 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0107.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3998 : Certifies 3998 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0108.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3999 : Certifies 3999 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0109.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4000 : Certifies 4000 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0110.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4001 : Certifies 4001 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0111.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4002 : Certifies 4002 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0112.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4003 : Certifies 4003 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0113.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4004 : Certifies 4004 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0114.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4005 : Certifies 4005 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0115.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4006 : Certifies 4006 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0116.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4007 : Certifies 4007 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0117.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4008 : Certifies 4008 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0118.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4009 : Certifies 4009 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0119.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4010 : Certifies 4010 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0120.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4011 : Certifies 4011 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0121.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4012 : Certifies 4012 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0122.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4013 : Certifies 4013 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0123.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4014 : Certifies 4014 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0124.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4015 : Certifies 4015 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0125.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4016 : Certifies 4016 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0126.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4017 : Certifies 4017 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0127.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4018 : Certifies 4018 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0128.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4019 : Certifies 4019 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0129.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4020 : Certifies 4020 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0130.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4021 : Certifies 4021 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0131.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4022 : Certifies 4022 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0132.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B132 (j : Fin 30) :
    Certifies (3993 + j.val) := by
  fin_cases j
  · exact projection_3993
  · exact projection_3994
  · exact projection_3995
  · exact projection_3996
  · exact projection_3997
  · exact projection_3998
  · exact projection_3999
  · exact projection_4000
  · exact projection_4001
  · exact projection_4002
  · exact projection_4003
  · exact projection_4004
  · exact projection_4005
  · exact projection_4006
  · exact projection_4007
  · exact projection_4008
  · exact projection_4009
  · exact projection_4010
  · exact projection_4011
  · exact projection_4012
  · exact projection_4013
  · exact projection_4014
  · exact projection_4015
  · exact projection_4016
  · exact projection_4017
  · exact projection_4018
  · exact projection_4019
  · exact projection_4020
  · exact projection_4021
  · exact projection_4022

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
