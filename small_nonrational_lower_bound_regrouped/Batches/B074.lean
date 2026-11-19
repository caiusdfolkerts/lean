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
/- Source: ProjectionCertificates/R_m14e10q1_0006.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0006

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 789, 185, 809, 561, 465, 598, 454, 774, 234, 618, 778, 340, 752, 41, 137, 265, 49, 145, 273, 529, 545, 385, 769, 70, 262, 518, 106, 138, 266, 522, 194, 578, 386, 770, 84, 276, 532, 324, 772, 168, 552, 776, 176, 560, 208, 336, 592, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_789, vertices_185, vertices_809, vertices_561, vertices_465, vertices_598, vertices_454, vertices_774, vertices_234, vertices_618, vertices_778, vertices_340, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_265, vertices_49, vertices_145, vertices_273, vertices_529, vertices_545, vertices_385, vertices_769, vertices_70, vertices_262, vertices_518, vertices_106, vertices_138, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_770, vertices_84, vertices_276, vertices_532, vertices_324, vertices_772, vertices_168, vertices_552, vertices_776, vertices_176, vertices_560, vertices_208, vertices_336, vertices_592, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_789), (false, vertices_185), (false, vertices_809), (false, vertices_561), (false, vertices_465), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_106), (true, vertices_522), (true, vertices_194), (true, vertices_578), (true, vertices_770), (true, vertices_84), (true, vertices_324), (true, vertices_592), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_185) then 19 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_106) then 15 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
cert_nodeAtPriority_37 561 70 262 518 522 194 578 770 84 324 592 224 608 395 106 789 185 809 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
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
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 234
cert_cover_5 3 0 0 2 4 6 106 234 3
cert_coverFacet 4 618
cert_cover_5 4 0 0 2 4 8 106 618 3
cert_coverFacet 5 778
cert_cover_2 5 2 0 7 8 266 778 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 176 752 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0006

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m14e10q1_0011.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0011

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 405, 837, 645, 681, 585, 481, 790, 554, 842, 242, 562, 466, 692, 133, 261, 517, 41, 73, 521, 97, 161, 321, 577, 385, 641, 42, 74, 522, 50, 210, 274, 530, 98, 546, 322, 770, 148, 276, 532, 644, 772, 552, 584, 176, 560, 400, 224, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_405, vertices_837, vertices_645, vertices_681, vertices_585, vertices_481, vertices_790, vertices_554, vertices_842, vertices_242, vertices_562, vertices_466, vertices_692] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_73, vertices_521, vertices_97, vertices_161, vertices_321, vertices_577, vertices_385, vertices_641, vertices_42, vertices_74, vertices_522, vertices_50, vertices_210, vertices_274, vertices_530, vertices_98, vertices_546, vertices_322, vertices_770, vertices_148, vertices_276, vertices_532, vertices_644, vertices_772, vertices_552, vertices_584, vertices_176, vertices_560, vertices_400, vertices_224, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_405), (false, vertices_837), (false, vertices_645), (false, vertices_681), (false, vertices_585), (false, vertices_481), (true, vertices_522), (true, vertices_50), (true, vertices_210), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_322), (true, vertices_770), (true, vertices_532), (true, vertices_176), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 13 else
  if p.val = (false, vertices_405) then 16 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (false, vertices_585) then 1 else
  if p.val = (false, vertices_481) then 22 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_210) then 14 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_560) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_645), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 74 3
cert_row_2 1 0 3 5 6 210
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 1 3 4 6 8 692 148 2
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 842
cert_cover_5 2 0 0 2 5 7 74 842 3
cert_coverFacet 3 242
cert_cover_5 3 1 0 3 4 5 50 242 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 466
cert_cover_5 5 1 0 3 5 7 210 466 3
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 148 692 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0011

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m14e10q1_0012.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0012

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 341, 533, 805, 665, 425, 401, 838, 234, 714, 354, 802, 724, 496, 21, 261, 517, 41, 137, 521, 145, 273, 529, 289, 545, 385, 42, 202, 522, 98, 290, 546, 322, 578, 770, 84, 532, 324, 580, 772, 168, 648, 208, 336, 400, 656, 224, 352, 416, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_341, vertices_533, vertices_805, vertices_665, vertices_425, vertices_401, vertices_838, vertices_234, vertices_714, vertices_354, vertices_802, vertices_724, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_261, vertices_517, vertices_41, vertices_137, vertices_521, vertices_145, vertices_273, vertices_529, vertices_289, vertices_545, vertices_385, vertices_42, vertices_202, vertices_522, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_84, vertices_532, vertices_324, vertices_580, vertices_772, vertices_168, vertices_648, vertices_208, vertices_336, vertices_400, vertices_656, vertices_224, vertices_352, vertices_416, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_341), (false, vertices_533), (false, vertices_805), (false, vertices_665), (false, vertices_425), (false, vertices_401), (true, vertices_202), (true, vertices_98), (true, vertices_290), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_580), (true, vertices_208), (true, vertices_224), (true, vertices_352), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 13 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_665) then 19 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (true, vertices_202) then 14 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_704) then 11 else
  0
cert_priority
cert_nodeAtPriority_10 0 533 1 401 98 290 322 578 770 580 208 224 352 704 555 202 341 805 665 425
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 3 4 5 6 7 496 208 1
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 234
cert_cover_5 1 0 0 2 4 5 42 234 3
cert_coverFacet 2 714
cert_cover_5 2 0 0 2 5 8 202 714 3
cert_coverFacet 3 354
cert_cover_2 3 4 0 5 7 98 354 3
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 724
cert_cover_5 5 2 1 3 5 6 84 724 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 208 496 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0012

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m14e10q1_0013.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0013

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 203, 331, 659, 357, 709, 186, 538, 778, 812, 612, 568, 488, 752, 75, 131, 259, 515, 69, 261, 517, 193, 321, 641, 26, 138, 266, 522, 146, 530, 770, 100, 292, 548, 580, 772, 56, 536, 168, 296, 552, 200, 328, 776, 176, 560, 656, 224, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_203, vertices_331, vertices_659, vertices_357, vertices_709, vertices_186, vertices_538, vertices_778, vertices_812, vertices_612, vertices_568, vertices_488, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_75, vertices_131, vertices_259, vertices_515, vertices_69, vertices_261, vertices_517, vertices_193, vertices_321, vertices_641, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_770, vertices_100, vertices_292, vertices_548, vertices_580, vertices_772, vertices_56, vertices_536, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_776, vertices_176, vertices_560, vertices_656, vertices_224, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_203), (false, vertices_331), (false, vertices_659), (false, vertices_357), (false, vertices_709), (true, vertices_26), (true, vertices_522), (true, vertices_548), (true, vertices_56), (true, vertices_536), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_176), (true, vertices_560), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 13 21 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_203) then 18 else
  if p.val = (false, vertices_331) then 19 else
  if p.val = (false, vertices_659) then 20 else
  if p.val = (false, vertices_357) then 15 else
  if p.val = (false, vertices_709) then 16 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_56) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
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
cert_row_4 0 0 2 3 4 6 186 26 3
cert_row_4 1 1 2 4 7 8 812 292 1
cert_row_4 2 2 4 5 6 7 488 168 2
cert_row_4 3 3 4 5 6 8 752 176 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 186
cert_cover_5 0 0 0 2 3 4 26 186 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 812
cert_cover_5 3 1 1 2 4 7 292 812 1
cert_coverFacet 4 612
cert_cover_2 4 4 1 5 8 100 612 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 488
cert_cover_5 6 2 2 4 5 6 168 488 2
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 176 752 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0013

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m14e10q1_0018.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0018

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 653, 341, 597, 421, 457, 678, 362, 394, 650, 626, 418, 820, 368, 85, 133, 261, 517, 73, 137, 521, 321, 577, 385, 74, 138, 266, 522, 98, 162, 290, 546, 578, 386, 642, 276, 532, 164, 292, 548, 644, 328, 392, 648, 112, 304, 560, 336, 592, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_653, vertices_341, vertices_597, vertices_421, vertices_457, vertices_678, vertices_362, vertices_394, vertices_650, vertices_626, vertices_418, vertices_820, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_85, vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_321, vertices_577, vertices_385, vertices_74, vertices_138, vertices_266, vertices_522, vertices_98, vertices_162, vertices_290, vertices_546, vertices_578, vertices_386, vertices_642, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_328, vertices_392, vertices_648, vertices_112, vertices_304, vertices_560, vertices_336, vertices_592, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_653), (false, vertices_341), (false, vertices_597), (false, vertices_421), (false, vertices_457), (true, vertices_138), (true, vertices_266), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_548), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 18 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 162 1
cert_row_4 1 0 2 4 5 7 362 74 2
cert_row_4 2 0 3 4 5 8 626 98 1
cert_row_4 3 1 3 4 7 8 820 276 2
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 162 678 1
cert_coverFacet 1 362
cert_cover_5 1 1 0 2 4 5 74 362 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 626
cert_cover_5 4 2 0 3 4 5 98 626 1
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 820
cert_cover_5 6 3 1 3 4 7 276 820 2
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0018

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m14e10q1_0019.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0019

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 77, 613, 901, 409, 713, 94, 118, 294, 282, 434, 804, 248, 992, 13, 69, 261, 517, 73, 137, 265, 577, 385, 641, 14, 86, 38, 262, 26, 266, 50, 274, 290, 76, 100, 292, 548, 772, 88, 152, 280, 200, 112, 176, 400, 224, 608, 416, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_77, vertices_613, vertices_901, vertices_409, vertices_713, vertices_94, vertices_118, vertices_294, vertices_282, vertices_434, vertices_804, vertices_248, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_577, vertices_385, vertices_641, vertices_14, vertices_86, vertices_38, vertices_262, vertices_26, vertices_266, vertices_50, vertices_274, vertices_290, vertices_76, vertices_100, vertices_292, vertices_548, vertices_772, vertices_88, vertices_152, vertices_280, vertices_200, vertices_112, vertices_176, vertices_400, vertices_224, vertices_608, vertices_416, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_77), (false, vertices_613), (false, vertices_901), (false, vertices_409), (false, vertices_713), (true, vertices_86), (true, vertices_38), (true, vertices_26), (true, vertices_50), (true, vertices_274), (true, vertices_290), (true, vertices_292), (true, vertices_88), (true, vertices_112), (true, vertices_176), (true, vertices_224), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 14 else
  if p.val = (false, vertices_77) then 0 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_901) then 18 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (true, vertices_86) then 15 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_77), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 3 4 6 7 434 50 3
cert_row_4 2 2 3 4 5 6 248 88 2
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 1 0 2 4
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 14 94 3
cert_coverFacet 1 118
cert_cover_5 1 0 0 1 3 4 86 118 3
cert_coverFacet 2 294
cert_cover_2 2 1 0 4 7 38 294 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 434
cert_cover_5 4 1 0 3 4 6 50 434 3
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coverFacet 6 248
cert_cover_5 6 2 2 3 4 5 88 248 2
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0019

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m14e10q1_0022.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0022

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 653, 217, 281, 849, 737, 270, 526, 678, 294, 866, 188, 316, 496, 25, 137, 265, 521, 81, 273, 193, 577, 641, 769, 14, 38, 262, 518, 266, 522, 290, 546, 770, 60, 140, 268, 524, 164, 292, 644, 152, 280, 176, 304, 208, 336, 224, 352, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_653, vertices_217, vertices_281, vertices_849, vertices_737, vertices_270, vertices_526, vertices_678, vertices_294, vertices_866, vertices_188, vertices_316, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_521, vertices_81, vertices_273, vertices_193, vertices_577, vertices_641, vertices_769, vertices_14, vertices_38, vertices_262, vertices_518, vertices_266, vertices_522, vertices_290, vertices_546, vertices_770, vertices_60, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_644, vertices_152, vertices_280, vertices_176, vertices_304, vertices_208, vertices_336, vertices_224, vertices_352, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_653), (false, vertices_217), (false, vertices_281), (false, vertices_849), (false, vertices_737), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_290), (true, vertices_546), (true, vertices_60), (true, vertices_268), (true, vertices_164), (true, vertices_292), (true, vertices_176), (true, vertices_304), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_217) then 19 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_849) then 21 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_60) then 17 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 1 4 6 8 678 38 3
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 678
cert_cover_5 2 1 0 1 4 6 38 678 3
cert_coverFacet 3 294
cert_cover_2 3 1 0 4 7 38 294 3
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 290 866 2
cert_coverFacet 5 188
cert_cover_5 5 0 1 2 3 6 60 188 3
cert_coverFacet 6 316
cert_cover_5 6 0 1 2 3 7 60 316 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 176 496 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0022

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m14e10q1_0024.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0024

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 397, 341, 661, 681, 777, 593, 358, 618, 426, 778, 244, 420, 752, 21, 133, 261, 137, 265, 521, 81, 529, 321, 577, 641, 769, 42, 266, 522, 98, 290, 322, 578, 770, 84, 148, 100, 164, 292, 324, 388, 168, 552, 392, 776, 240, 592, 656, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_397, vertices_341, vertices_661, vertices_681, vertices_777, vertices_593, vertices_358, vertices_618, vertices_426, vertices_778, vertices_244, vertices_420, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_137, vertices_265, vertices_521, vertices_81, vertices_529, vertices_321, vertices_577, vertices_641, vertices_769, vertices_42, vertices_266, vertices_522, vertices_98, vertices_290, vertices_322, vertices_578, vertices_770, vertices_84, vertices_148, vertices_100, vertices_164, vertices_292, vertices_324, vertices_388, vertices_168, vertices_552, vertices_392, vertices_776, vertices_240, vertices_592, vertices_656, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_397), (false, vertices_341), (false, vertices_661), (false, vertices_681), (false, vertices_777), (false, vertices_593), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_98), (true, vertices_290), (true, vertices_100), (true, vertices_164), (true, vertices_292), (true, vertices_240), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 13 else
  if p.val = (false, vertices_397) then 15 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_593) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_240) then 21 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 6 240
cert_row_4 1 0 1 4 5 7 358 98 1
cert_row_4 2 0 2 4 5 8 618 42 3
cert_row_4 3 0 2 4 6 7 426 42 3
cert_rows
cert_pivot_2 3 1 5 0
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 1 0 1 4 5 98 358 1
cert_coverFacet 1 618
cert_cover_5 1 2 0 2 4 5 42 618 3
cert_coverFacet 2 426
cert_cover_5 2 3 0 2 4 6 42 426 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 244
cert_cover_5 4 0 1 3 4 5 84 244 2
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 752
cert_cover_5 6 0 3 4 5 8 240 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0024

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m14e10q1_0033.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0033

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 421, 601, 361, 681, 449, 406, 346, 594, 658, 450, 796, 812, 692, 41, 73, 521, 161, 289, 193, 321, 577, 385, 641, 82, 146, 274, 530, 194, 322, 578, 386, 642, 780, 148, 276, 532, 164, 292, 548, 388, 88, 280, 536, 296, 552, 328, 592, 656, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_421, vertices_601, vertices_361, vertices_681, vertices_449, vertices_406, vertices_346, vertices_594, vertices_658, vertices_450, vertices_796, vertices_812, vertices_692] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_521, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_780, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_88, vertices_280, vertices_536, vertices_296, vertices_552, vertices_328, vertices_592, vertices_656, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_421), (false, vertices_601), (false, vertices_361), (false, vertices_681), (false, vertices_449), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_322), (true, vertices_386), (true, vertices_780), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_548), (true, vertices_280), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_421) then 16 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_780) then 17 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_656) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 7 346 82 1
cert_row_2 1 1 2 7 8 780
cert_row_4 2 0 1 3 6 7 406 146 1
cert_row_4 3 1 3 4 6 8 692 148 2
cert_rows
cert_pivot_2 5 2 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 2 0 1 3 6 146 406 1
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 5 82 346 1
cert_coverFacet 2 594
cert_cover_2 2 3 0 5 8 82 594 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 450
cert_cover_2 4 5 0 6 7 194 450 3
cert_coverFacet 5 796
cert_cover_5 5 1 1 2 3 7 780 796 2
cert_coverFacet 6 812
cert_cover_5 6 1 1 2 4 7 780 812 2
cert_coverFacet 7 692
cert_cover_5 7 3 1 3 4 6 148 692 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0033

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m14e10q1_0034.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0034

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 899, 541, 345, 713, 481, 566, 434, 738, 284, 620, 332, 308, 356, 771, 25, 73, 521, 273, 529, 193, 321, 385, 641, 50, 274, 530, 162, 546, 386, 642, 28, 76, 268, 524, 52, 276, 532, 100, 292, 548, 324, 280, 328, 584, 304, 224, 352, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_899, vertices_541, vertices_345, vertices_713, vertices_481, vertices_566, vertices_434, vertices_738, vertices_284, vertices_620, vertices_332, vertices_308, vertices_356] (by decide +kernel)
  polygons := literalFinset [vertices_771, vertices_25, vertices_73, vertices_521, vertices_273, vertices_529, vertices_193, vertices_321, vertices_385, vertices_641, vertices_50, vertices_274, vertices_530, vertices_162, vertices_546, vertices_386, vertices_642, vertices_28, vertices_76, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_324, vertices_280, vertices_328, vertices_584, vertices_304, vertices_224, vertices_352, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_899), (false, vertices_541), (false, vertices_345), (false, vertices_713), (false, vertices_481), (true, vertices_50), (true, vertices_162), (true, vertices_546), (true, vertices_76), (true, vertices_268), (true, vertices_52), (true, vertices_276), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_324), (true, vertices_304), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_541) then 17 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
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
cert_row_4 0 0 3 4 6 7 434 50 3
cert_row_4 1 0 1 3 4 8 566 50 1
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 1 2 4 5 8 620 76 2
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 1 0 1 3 4 50 566 1
cert_coverFacet 1 434
cert_cover_5 1 0 0 3 4 6 50 434 3
cert_coverFacet 2 738
cert_cover_5 2 2 0 4 5 6 162 738 2
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 620
cert_cover_5 4 3 1 2 4 5 76 620 2
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 356
cert_cover_2 7 4 1 5 7 100 356 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0034

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m14e10q1_0036.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0036

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 205, 269, 661, 841, 737, 62, 270, 534, 298, 690, 866, 188, 488, 13, 133, 261, 517, 73, 265, 193, 577, 641, 769, 14, 22, 262, 518, 42, 266, 50, 530, 290, 546, 770, 60, 140, 268, 148, 532, 168, 296, 200, 328, 176, 656, 224, 352, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_205, vertices_269, vertices_661, vertices_841, vertices_737, vertices_62, vertices_270, vertices_534, vertices_298, vertices_690, vertices_866, vertices_188, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_193, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_518, vertices_42, vertices_266, vertices_50, vertices_530, vertices_290, vertices_546, vertices_770, vertices_60, vertices_140, vertices_268, vertices_148, vertices_532, vertices_168, vertices_296, vertices_200, vertices_328, vertices_176, vertices_656, vertices_224, vertices_352, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_205), (false, vertices_269), (false, vertices_661), (false, vertices_841), (false, vertices_737), (true, vertices_14), (true, vertices_22), (true, vertices_42), (true, vertices_266), (true, vertices_50), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_60), (true, vertices_168), (true, vertices_296), (true, vertices_176), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_205) then 16 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_60) then 18 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 3 4 6 8 690 50 3
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 14 62 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 690
cert_cover_5 4 1 0 3 4 6 50 690 3
cert_coverFacet 5 866
cert_cover_5 5 2 0 4 5 7 290 866 2
cert_coverFacet 6 188
cert_cover_5 6 0 1 2 3 6 60 188 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 168 488 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0036

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m14e10q1_0037.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0037

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [47, 519, 787, 419, 525, 681, 961, 118, 534, 370, 108, 716, 852, 488, 7, 35, 259, 515, 13, 517, 41, 521, 161, 385, 641, 769, 22, 38, 518, 114, 274, 530, 290, 44, 76, 524, 84, 532, 100, 580, 104, 168, 200, 648, 336, 784, 352, 416, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_47, vertices_519, vertices_787, vertices_419, vertices_525, vertices_681, vertices_961, vertices_118, vertices_534, vertices_370, vertices_108, vertices_716, vertices_852, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_35, vertices_259, vertices_515, vertices_13, vertices_517, vertices_41, vertices_521, vertices_161, vertices_385, vertices_641, vertices_769, vertices_22, vertices_38, vertices_518, vertices_114, vertices_274, vertices_530, vertices_290, vertices_44, vertices_76, vertices_524, vertices_84, vertices_532, vertices_100, vertices_580, vertices_104, vertices_168, vertices_200, vertices_648, vertices_336, vertices_784, vertices_352, vertices_416, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_47), (false, vertices_519), (false, vertices_787), (false, vertices_419), (false, vertices_525), (false, vertices_681), (false, vertices_961), (true, vertices_22), (true, vertices_114), (true, vertices_76), (true, vertices_84), (true, vertices_532), (true, vertices_100), (true, vertices_580), (true, vertices_104), (true, vertices_200), (true, vertices_336), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 12 18 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_47) then 13 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_114) then 17 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_47), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_114), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 5 114
cert_row_4 1 1 3 5 7 8 852 84 3
cert_row_4 2 1 2 5 6 8 716 76 3
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 0 0 1 3 4 22 118 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 370
cert_cover_5 2 0 0 3 4 7 114 370 3
cert_coverFacet 3 108
cert_cover_2 3 2 1 4 5 44 108 3
cert_coverFacet 4 716
cert_cover_5 4 2 1 2 5 6 76 716 3
cert_coverFacet 5 852
cert_cover_5 5 1 1 3 5 7 84 852 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 104 488 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0037

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m14e10q1_0038.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0038

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 205, 525, 677, 345, 721, 785, 558, 362, 370, 690, 786, 108, 244, 13, 133, 517, 73, 265, 521, 81, 273, 529, 193, 641, 769, 42, 266, 522, 50, 274, 530, 354, 546, 770, 44, 76, 524, 100, 164, 548, 196, 104, 328, 112, 176, 208, 336, 656, 784, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_205, vertices_525, vertices_677, vertices_345, vertices_721, vertices_785, vertices_558, vertices_362, vertices_370, vertices_690, vertices_786, vertices_108, vertices_244] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_73, vertices_265, vertices_521, vertices_81, vertices_273, vertices_529, vertices_193, vertices_641, vertices_769, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_354, vertices_546, vertices_770, vertices_44, vertices_76, vertices_524, vertices_100, vertices_164, vertices_548, vertices_196, vertices_104, vertices_328, vertices_112, vertices_176, vertices_208, vertices_336, vertices_656, vertices_784, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_205), (false, vertices_525), (false, vertices_677), (false, vertices_345), (false, vertices_721), (false, vertices_785), (true, vertices_42), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_354), (true, vertices_546), (true, vertices_44), (true, vertices_100), (true, vertices_104), (true, vertices_112), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_205) then 16 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_721) then 21 else
  if p.val = (false, vertices_785) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_354) then 14 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  0
cert_priority
cert_nodeAtPriority_67 0 525 1 785 42 50 274 530 546 44 100 104 112 176 779 354 205 677 345 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 5 7 354
cert_row_4 1 0 1 2 4 8 558 42 1
cert_row_4 2 0 3 4 6 8 690 50 3
cert_row_4 3 1 3 4 5 6 244 100 1
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 42 558 1
cert_coverFacet 1 362
cert_cover_5 1 0 0 2 4 5 42 362 3
cert_coverFacet 2 370
cert_cover_5 2 0 0 3 4 5 50 370 3
cert_coverFacet 3 690
cert_cover_5 3 2 0 3 4 6 50 690 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 244
cert_cover_5 6 3 1 3 4 5 100 244 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0038

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m14e10q1_0039.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0039

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [15, 551, 395, 787, 45, 681, 961, 94, 534, 346, 108, 852, 740, 488, 7, 11, 259, 515, 13, 37, 41, 137, 545, 385, 641, 769, 14, 22, 518, 90, 266, 274, 530, 44, 76, 84, 532, 100, 548, 580, 104, 168, 328, 392, 336, 784, 224, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_15, vertices_551, vertices_395, vertices_787, vertices_45, vertices_681, vertices_961, vertices_94, vertices_534, vertices_346, vertices_108, vertices_852, vertices_740, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_515, vertices_13, vertices_37, vertices_41, vertices_137, vertices_545, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_518, vertices_90, vertices_266, vertices_274, vertices_530, vertices_44, vertices_76, vertices_84, vertices_532, vertices_100, vertices_548, vertices_580, vertices_104, vertices_168, vertices_328, vertices_392, vertices_336, vertices_784, vertices_224, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_15), (false, vertices_551), (false, vertices_395), (false, vertices_787), (false, vertices_45), (false, vertices_681), (false, vertices_961), (true, vertices_22), (true, vertices_90), (true, vertices_76), (true, vertices_84), (true, vertices_532), (true, vertices_100), (true, vertices_580), (true, vertices_104), (true, vertices_328), (true, vertices_336), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 12 18 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_15) then 0 else
  if p.val = (false, vertices_551) then 13 else
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_45) then 1 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_90) then 17 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_15), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 1 3 5 7 8 852 84 3
cert_row_4 2 1 4 5 6 8 740 100 3
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 14 94 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 7 90 346 3
cert_coverFacet 3 108
cert_cover_2 3 2 1 4 5 44 108 3
cert_coverFacet 4 852
cert_cover_5 4 1 1 3 5 7 84 852 3
cert_coverFacet 5 740
cert_cover_5 5 2 1 4 5 6 100 740 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 104 488 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0039

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m14e10q1_0042.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0042

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 781, 105, 713, 241, 929, 110, 270, 118, 278, 434, 604, 788, 976, 41, 73, 265, 521, 97, 161, 289, 193, 641, 769, 14, 22, 102, 262, 42, 266, 50, 274, 290, 76, 268, 524, 84, 276, 532, 772, 104, 584, 112, 176, 208, 592, 400, 784, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_781, vertices_105, vertices_713, vertices_241, vertices_929, vertices_110, vertices_270, vertices_118, vertices_278, vertices_434, vertices_604, vertices_788, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_193, vertices_641, vertices_769, vertices_14, vertices_22, vertices_102, vertices_262, vertices_42, vertices_266, vertices_50, vertices_274, vertices_290, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_772, vertices_104, vertices_584, vertices_112, vertices_176, vertices_208, vertices_592, vertices_400, vertices_784, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_781), (false, vertices_105), (false, vertices_713), (false, vertices_241), (false, vertices_929), (true, vertices_14), (true, vertices_22), (true, vertices_102), (true, vertices_262), (true, vertices_50), (true, vertices_274), (true, vertices_76), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_592), (true, vertices_400), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 14 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_105) then 0 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_102) then 15 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_784) then 12 else
  0
cert_priority
cert_nodeAtPriority_49 105 14 22 262 50 274 76 84 276 532 592 400 784 299 102 781 713 241 929
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 5 8 604 76 2
cert_row_2 1 0 1 4 5 102
cert_row_4 2 0 3 4 6 7 434 50 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 118
cert_cover_5 2 1 0 1 3 4 22 118 3
cert_coverFacet 3 278
cert_cover_2 3 1 0 3 7 22 278 3
cert_coverFacet 4 434
cert_cover_5 4 2 0 3 4 6 50 434 3
cert_coverFacet 5 604
cert_cover_5 5 0 1 2 3 5 76 604 2
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 976
cert_cover_5 7 3 3 5 6 7 208 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0042

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m14e10q1_0046.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0046

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 539, 275, 653, 421, 345, 457, 626, 338, 482, 802, 740, 804, 728, 19, 259, 515, 133, 261, 517, 25, 329, 137, 521, 273, 385, 82, 274, 530, 98, 290, 546, 322, 770, 164, 292, 548, 644, 772, 88, 536, 200, 648, 336, 592, 224, 608, 416, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_539, vertices_275, vertices_653, vertices_421, vertices_345, vertices_457, vertices_626, vertices_338, vertices_482, vertices_802, vertices_740, vertices_804, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_259, vertices_515, vertices_133, vertices_261, vertices_517, vertices_25, vertices_329, vertices_137, vertices_521, vertices_273, vertices_385, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_770, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_88, vertices_536, vertices_200, vertices_648, vertices_336, vertices_592, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_539), (false, vertices_275), (false, vertices_653), (false, vertices_421), (false, vertices_345), (false, vertices_457), (true, vertices_82), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_548), (true, vertices_592), (true, vertices_224), (true, vertices_608), (true, vertices_800), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_539) then 14 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_704) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 6 7 482 98 3
cert_row_4 1 0 3 4 5 8 626 82 2
cert_row_4 2 1 4 5 6 8 740 164 2
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 626
cert_cover_5 0 1 0 3 4 5 82 626 2
cert_coverFacet 1 338
cert_cover_2 1 3 0 5 7 82 338 3
cert_coverFacet 2 482
cert_cover_5 2 0 0 4 5 6 98 482 3
cert_coverFacet 3 802
cert_cover_2 3 4 0 7 8 290 802 3
cert_coverFacet 4 740
cert_cover_5 4 2 1 4 5 6 164 740 2
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coverFacet 6 728
cert_cover_5 6 3 2 3 5 6 88 728 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0046

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m14e10q1_0047.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0047

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [59, 283, 803, 53, 405, 677, 961, 558, 842, 60, 92, 588, 724, 472, 27, 35, 259, 21, 37, 133, 49, 273, 545, 385, 641, 769, 42, 266, 522, 546, 770, 28, 44, 76, 524, 52, 84, 148, 548, 580, 644, 56, 88, 280, 328, 584, 208, 400, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_59, vertices_283, vertices_803, vertices_53, vertices_405, vertices_677, vertices_961, vertices_558, vertices_842, vertices_60, vertices_92, vertices_588, vertices_724, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_35, vertices_259, vertices_21, vertices_37, vertices_133, vertices_49, vertices_273, vertices_545, vertices_385, vertices_641, vertices_769, vertices_42, vertices_266, vertices_522, vertices_546, vertices_770, vertices_28, vertices_44, vertices_76, vertices_524, vertices_52, vertices_84, vertices_148, vertices_548, vertices_580, vertices_644, vertices_56, vertices_88, vertices_280, vertices_328, vertices_584, vertices_208, vertices_400, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_59), (false, vertices_283), (false, vertices_803), (false, vertices_53), (false, vertices_405), (false, vertices_677), (false, vertices_961), (true, vertices_522), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_524), (true, vertices_84), (true, vertices_580), (true, vertices_88), (true, vertices_328), (true, vertices_584), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_59) then 13 else
  if p.val = (false, vertices_283) then 14 else
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_53) then 0 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_208) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_53), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 42 1
cert_row_4 1 0 2 5 7 8 842 266 2
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 4 0 1 2
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 42 558 1
cert_coverFacet 1 842
cert_cover_5 1 1 0 2 5 7 266 842 2
cert_coverFacet 2 60
cert_cover_2 2 2 1 3 4 28 60 3
cert_coverFacet 3 92
cert_cover_2 3 2 1 3 5 28 92 3
cert_coverFacet 4 588
cert_cover_2 4 2 1 5 8 76 588 3
cert_coverFacet 5 724
cert_cover_5 5 2 1 3 5 6 84 724 3
cert_coverFacet 6 472
cert_cover_5 6 3 2 3 5 6 88 472 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0047

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m14e10q1_0052.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0052

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 453, 121, 425, 329, 561, 721, 782, 422, 710, 810, 604, 332, 568, 41, 73, 265, 49, 81, 529, 161, 545, 193, 321, 385, 641, 134, 262, 518, 778, 162, 290, 546, 642, 76, 268, 524, 196, 324, 580, 388, 56, 88, 536, 296, 552, 328, 560, 592, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_453, vertices_121, vertices_425, vertices_329, vertices_561, vertices_721, vertices_782, vertices_422, vertices_710, vertices_810, vertices_604, vertices_332, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_49, vertices_81, vertices_529, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_134, vertices_262, vertices_518, vertices_778, vertices_162, vertices_290, vertices_546, vertices_642, vertices_76, vertices_268, vertices_524, vertices_196, vertices_324, vertices_580, vertices_388, vertices_56, vertices_88, vertices_536, vertices_296, vertices_552, vertices_328, vertices_560, vertices_592, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_453), (false, vertices_121), (false, vertices_425), (false, vertices_329), (false, vertices_561), (false, vertices_721), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_778), (true, vertices_290), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_580), (true, vertices_536), (true, vertices_552)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 13 else
  if p.val = (false, vertices_453) then 16 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_561) then 1 else
  if p.val = (false, vertices_721) then 21 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_778) then 14 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_552) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 7 422 134 2
cert_row_2 1 0 2 7 8 778
cert_row_4 2 0 1 5 6 8 710 134 2
cert_row_4 3 1 2 3 5 8 604 76 2
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 262 782 2
cert_coverFacet 1 422
cert_cover_5 1 0 0 1 4 6 134 422 2
cert_coverFacet 2 710
cert_cover_5 2 2 0 1 5 6 134 710 2
cert_coverFacet 3 810
cert_cover_5 3 1 0 2 4 7 778 810 2
cert_coverFacet 4 604
cert_cover_5 4 3 1 2 3 5 76 604 2
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0052

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m14e10q1_0053.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0053

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 779, 275, 117, 805, 337, 481, 666, 426, 466, 724, 740, 680, 808, 19, 259, 515, 21, 37, 517, 81, 273, 97, 289, 321, 769, 138, 266, 522, 146, 274, 530, 386, 84, 532, 100, 548, 708, 168, 296, 552, 648, 776, 208, 336, 656, 224, 416, 672, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_779, vertices_275, vertices_117, vertices_805, vertices_337, vertices_481, vertices_666, vertices_426, vertices_466, vertices_724, vertices_740, vertices_680, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_259, vertices_515, vertices_21, vertices_37, vertices_517, vertices_81, vertices_273, vertices_97, vertices_289, vertices_321, vertices_769, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_84, vertices_532, vertices_100, vertices_548, vertices_708, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_208, vertices_336, vertices_656, vertices_224, vertices_416, vertices_672, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_779), (false, vertices_275), (false, vertices_117), (false, vertices_805), (false, vertices_337), (false, vertices_481), (true, vertices_138), (true, vertices_146), (true, vertices_386), (true, vertices_708), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_648), (true, vertices_208), (true, vertices_656), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 13 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_117) then 16 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_337) then 1 else
  if p.val = (false, vertices_481) then 22 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_708) then 18 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_708), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 5 6 8 708
cert_row_4 1 0 2 3 6 8 666 138 2
cert_row_4 2 0 2 4 6 7 426 138 2
cert_row_4 3 0 3 5 6 7 466 146 2
cert_rows
cert_pivot_2 1 8 2 0
cert_heightProof 4
cert_coverFacet 0 666
cert_cover_5 0 1 0 2 3 6 138 666 2
cert_coverFacet 1 426
cert_cover_5 1 2 0 2 4 6 138 426 2
cert_coverFacet 2 466
cert_cover_5 2 3 0 3 5 6 146 466 2
cert_coverFacet 3 724
cert_cover_5 3 0 1 3 5 6 84 724 3
cert_coverFacet 4 740
cert_cover_5 4 0 1 4 5 6 100 740 3
cert_coverFacet 5 680
cert_cover_2 5 4 2 6 8 168 680 3
cert_coverFacet 6 808
cert_cover_2 6 4 2 7 8 296 808 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0053

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m14e10q1_0060.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0060

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 527, 357, 709, 809, 625, 390, 646, 570, 282, 722, 402, 468, 376, 15, 69, 261, 517, 265, 521, 97, 289, 545, 577, 134, 262, 518, 26, 266, 522, 146, 274, 530, 386, 642, 196, 324, 388, 644, 56, 280, 296, 552, 112, 560, 208, 336, 592, 400, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_527, vertices_357, vertices_709, vertices_809, vertices_625, vertices_390, vertices_646, vertices_570, vertices_282, vertices_722, vertices_402, vertices_468, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_15, vertices_69, vertices_261, vertices_517, vertices_265, vertices_521, vertices_97, vertices_289, vertices_545, vertices_577, vertices_134, vertices_262, vertices_518, vertices_26, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_196, vertices_324, vertices_388, vertices_644, vertices_56, vertices_280, vertices_296, vertices_552, vertices_112, vertices_560, vertices_208, vertices_336, vertices_592, vertices_400, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_527), (false, vertices_357), (false, vertices_709), (false, vertices_809), (false, vertices_625), (true, vertices_134), (true, vertices_26), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_388), (true, vertices_56), (true, vertices_280), (true, vertices_208), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 14 else
  if p.val = (false, vertices_527) then 15 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 5 6 7 468 196 1
cert_row_4 1 0 3 5 6 8 722 146 2
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 390
cert_cover_2 0 1 0 6 7 134 390 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 570
cert_cover_5 2 2 0 2 3 4 26 570 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 722
cert_cover_5 4 1 0 3 5 6 146 722 2
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 468
cert_cover_5 6 0 1 3 5 6 196 468 1
cert_coverFacet 7 376
cert_cover_5 7 3 2 3 4 5 56 376 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0060

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m14e10q1_0073.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0073

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 551, 781, 409, 681, 481, 598, 326, 738, 354, 468, 788, 728, 792, 39, 261, 517, 137, 265, 521, 161, 289, 545, 385, 70, 262, 518, 98, 290, 546, 322, 578, 84, 276, 532, 324, 772, 152, 280, 536, 648, 776, 208, 592, 400, 784, 224, 352, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_551, vertices_781, vertices_409, vertices_681, vertices_481, vertices_598, vertices_326, vertices_738, vertices_354, vertices_468, vertices_788, vertices_728, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_39, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_385, vertices_70, vertices_262, vertices_518, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_84, vertices_276, vertices_532, vertices_324, vertices_772, vertices_152, vertices_280, vertices_536, vertices_648, vertices_776, vertices_208, vertices_592, vertices_400, vertices_784, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_551), (false, vertices_781), (false, vertices_409), (false, vertices_681), (false, vertices_481), (true, vertices_70), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_324), (true, vertices_536), (true, vertices_208), (true, vertices_592), (true, vertices_784), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 14 else
  if p.val = (false, vertices_551) then 15 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
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
cert_row_4 0 0 4 5 6 8 738 98 3
cert_row_4 1 0 1 3 5 8 598 70 2
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 2 3 5 6 8 728 152 2
cert_rows
cert_pivot_2 4 0 1 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 1 0 1 3 5 70 598 2
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 738
cert_cover_5 2 0 0 4 5 6 98 738 3
cert_coverFacet 3 354
cert_cover_2 3 4 0 5 7 98 354 3
cert_coverFacet 4 468
cert_cover_5 4 2 1 3 5 6 84 468 3
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 728
cert_cover_5 6 3 2 3 5 6 152 728 2
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0073

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m14e10q1_0074.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0074

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 267, 675, 291, 421, 457, 721, 302, 558, 284, 540, 692, 468, 856, 11, 35, 259, 515, 73, 265, 161, 289, 193, 577, 385, 641, 46, 266, 522, 290, 546, 28, 268, 524, 148, 276, 532, 164, 292, 548, 388, 280, 536, 328, 584, 208, 336, 592, 656, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_267, vertices_675, vertices_291, vertices_421, vertices_457, vertices_721, vertices_302, vertices_558, vertices_284, vertices_540, vertices_692, vertices_468, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_515, vertices_73, vertices_265, vertices_161, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_46, vertices_266, vertices_522, vertices_290, vertices_546, vertices_28, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_280, vertices_536, vertices_328, vertices_584, vertices_208, vertices_336, vertices_592, vertices_656, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_267), (false, vertices_675), (false, vertices_291), (false, vertices_421), (false, vertices_457), (false, vertices_721), (true, vertices_46), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_548), (true, vertices_280), (true, vertices_536), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 13 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_291) then 1 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_721) then 21 else
  if p.val = (true, vertices_46) then 15 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_336) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 1 3 4 6 8 692 148 2
cert_row_4 2 1 3 5 6 7 468 148 2
cert_row_4 3 2 3 5 7 8 856 280 2
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 7 46 302 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 8 46 558 3
cert_coverFacet 2 284
cert_cover_2 2 2 1 3 7 28 284 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 692
cert_cover_5 4 1 1 3 4 6 148 692 2
cert_coverFacet 5 468
cert_cover_5 5 2 1 3 5 6 148 468 2
cert_coverFacet 6 856
cert_cover_5 6 3 2 3 5 7 280 856 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0074

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m14e10q1_0075.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0075

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 541, 173, 565, 281, 457, 241, 282, 538, 778, 626, 962, 908, 740, 13, 533, 37, 25, 137, 265, 49, 81, 273, 161, 193, 321, 26, 266, 522, 82, 274, 530, 322, 578, 770, 140, 524, 164, 548, 644, 280, 536, 392, 776, 112, 560, 224, 608, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_541, vertices_173, vertices_565, vertices_281, vertices_457, vertices_241, vertices_282, vertices_538, vertices_778, vertices_626, vertices_962, vertices_908, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_533, vertices_37, vertices_25, vertices_137, vertices_265, vertices_49, vertices_81, vertices_273, vertices_161, vertices_193, vertices_321, vertices_26, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_140, vertices_524, vertices_164, vertices_548, vertices_644, vertices_280, vertices_536, vertices_392, vertices_776, vertices_112, vertices_560, vertices_224, vertices_608, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_541), (false, vertices_173), (false, vertices_565), (false, vertices_281), (false, vertices_457), (false, vertices_241), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_530), (true, vertices_578), (true, vertices_770), (true, vertices_644), (true, vertices_776), (true, vertices_608), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 13 else
  if p.val = (false, vertices_541) then 15 else
  if p.val = (false, vertices_173) then 16 else
  if p.val = (false, vertices_565) then 17 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 8 626 82 2
cert_row_4 1 0 5 6 7 8 962 322 2
cert_row_4 2 1 2 6 7 8 908 140 3
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 282
cert_cover_2 0 2 0 3 7 26 282 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 626
cert_cover_5 3 0 0 3 4 5 82 626 2
cert_coverFacet 4 962
cert_cover_5 4 1 0 5 6 7 322 962 2
cert_coverFacet 5 908
cert_cover_5 5 2 1 2 6 7 140 908 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 164 740 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0075

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m14e10q1_0077.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0077

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 267, 451, 709, 665, 281, 433, 806, 838, 314, 554, 692, 484, 568, 11, 67, 259, 25, 265, 521, 145, 273, 193, 577, 385, 641, 774, 42, 266, 522, 290, 546, 322, 578, 164, 292, 548, 196, 324, 580, 644, 56, 280, 536, 552, 176, 304, 560, 656, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_267, vertices_451, vertices_709, vertices_665, vertices_281, vertices_433, vertices_806, vertices_838, vertices_314, vertices_554, vertices_692, vertices_484, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_259, vertices_25, vertices_265, vertices_521, vertices_145, vertices_273, vertices_193, vertices_577, vertices_385, vertices_641, vertices_774, vertices_42, vertices_266, vertices_522, vertices_290, vertices_546, vertices_322, vertices_578, vertices_164, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_644, vertices_56, vertices_280, vertices_536, vertices_552, vertices_176, vertices_304, vertices_560, vertices_656, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_267), (false, vertices_451), (false, vertices_709), (false, vertices_665), (false, vertices_281), (false, vertices_433), (true, vertices_774), (true, vertices_42), (true, vertices_290), (true, vertices_546), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_324), (true, vertices_56), (true, vertices_552), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 13 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_709) then 17 else
  if p.val = (false, vertices_665) then 19 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (true, vertices_774) then 15 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_560) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 7 314 42 2
cert_row_2 1 0 1 7 8 774
cert_row_4 2 1 3 4 6 8 692 164 1
cert_row_4 3 1 4 5 6 7 484 164 2
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 774 806 2
cert_coverFacet 1 838
cert_cover_5 1 1 0 1 5 7 774 838 2
cert_coverFacet 2 314
cert_cover_5 2 0 0 2 3 4 42 314 2
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 692
cert_cover_5 4 2 1 3 4 6 164 692 1
cert_coverFacet 5 484
cert_cover_5 5 3 1 4 5 6 164 484 2
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0077

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m14e10q1_0078.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0078

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 147, 835, 387, 613, 457, 241, 790, 402, 316, 236, 844, 564, 440, 19, 131, 259, 515, 49, 145, 97, 545, 193, 321, 577, 385, 146, 274, 530, 386, 770, 44, 76, 268, 52, 276, 532, 100, 548, 580, 772, 312, 168, 200, 328, 392, 176, 560, 400, 224, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_147, vertices_835, vertices_387, vertices_613, vertices_457, vertices_241, vertices_790, vertices_402, vertices_316, vertices_236, vertices_844, vertices_564, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_49, vertices_145, vertices_97, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_146, vertices_274, vertices_530, vertices_386, vertices_770, vertices_44, vertices_76, vertices_268, vertices_52, vertices_276, vertices_532, vertices_100, vertices_548, vertices_580, vertices_772, vertices_312, vertices_168, vertices_200, vertices_328, vertices_392, vertices_176, vertices_560, vertices_400, vertices_224, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_147), (false, vertices_835), (false, vertices_387), (false, vertices_613), (false, vertices_457), (false, vertices_241), (true, vertices_274), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_772), (true, vertices_312), (true, vertices_168), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 13 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_613) then 16 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_312) then 19 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_400) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_312), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_2 1 2 3 4 7 312
cert_row_4 2 1 2 4 5 6 236 44 3
cert_row_4 3 1 2 5 7 8 844 76 3
cert_rows
cert_pivot_2 0 3 4 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 402
cert_cover_2 1 3 0 6 7 146 402 3
cert_coverFacet 2 316
cert_cover_5 2 1 1 2 3 4 44 316 2
cert_coverFacet 3 236
cert_cover_5 3 2 1 2 4 5 44 236 3
cert_coverFacet 4 844
cert_cover_5 4 3 1 2 5 7 76 844 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 440
cert_cover_5 6 1 2 3 4 6 312 440 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0078

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m14e10q1_0084.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0084

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 595, 387, 771, 421, 841, 369, 662, 898, 572, 364, 908, 180, 632, 19, 131, 259, 515, 49, 81, 161, 289, 321, 577, 385, 769, 146, 530, 386, 642, 770, 44, 268, 524, 52, 148, 532, 164, 292, 388, 644, 568, 104, 328, 584, 776, 112, 176, 592, 352, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_595, vertices_387, vertices_771, vertices_421, vertices_841, vertices_369, vertices_662, vertices_898, vertices_572, vertices_364, vertices_908, vertices_180, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_577, vertices_385, vertices_769, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_524, vertices_52, vertices_148, vertices_532, vertices_164, vertices_292, vertices_388, vertices_644, vertices_568, vertices_104, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_592, vertices_352, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_595), (false, vertices_387), (false, vertices_771), (false, vertices_421), (false, vertices_841), (false, vertices_369), (true, vertices_642), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_148), (true, vertices_532), (true, vertices_644), (true, vertices_568), (true, vertices_104), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 13 else
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_421) then 16 else
  if p.val = (false, vertices_841) then 18 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_568) then 19 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_568), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_2 1 2 3 4 8 568
cert_row_4 2 1 2 4 5 7 364 44 3
cert_row_4 3 1 2 6 7 8 908 268 2
cert_rows
cert_pivot_2 0 3 4 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 898
cert_cover_2 1 6 0 7 8 386 898 3
cert_coverFacet 2 572
cert_cover_5 2 1 1 2 3 4 44 572 2
cert_coverFacet 3 364
cert_cover_5 3 2 1 2 4 5 44 364 3
cert_coverFacet 4 908
cert_cover_5 4 3 1 2 6 7 268 908 2
cert_coverFacet 5 180
cert_cover_2 5 3 1 4 6 52 180 3
cert_coverFacet 6 632
cert_cover_5 6 1 2 3 4 5 568 632 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0084

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m14e10q1_0086.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0086

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 45, 205, 421, 553, 841, 465, 662, 678, 434, 850, 620, 212, 596, 13, 37, 133, 41, 73, 521, 289, 545, 193, 321, 385, 769, 646, 146, 274, 530, 162, 290, 546, 770, 44, 76, 84, 148, 532, 164, 548, 196, 580, 552, 584, 208, 336, 592, 400, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_45, vertices_205, vertices_421, vertices_553, vertices_841, vertices_465, vertices_662, vertices_678, vertices_434, vertices_850, vertices_620, vertices_212, vertices_596] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_133, vertices_41, vertices_73, vertices_521, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_646, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_770, vertices_44, vertices_76, vertices_84, vertices_148, vertices_532, vertices_164, vertices_548, vertices_196, vertices_580, vertices_552, vertices_584, vertices_208, vertices_336, vertices_592, vertices_400, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_45), (false, vertices_205), (false, vertices_421), (false, vertices_553), (false, vertices_841), (false, vertices_465), (true, vertices_646), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_548), (true, vertices_580), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 13 else
  if p.val = (false, vertices_45) then 0 else
  if p.val = (false, vertices_205) then 16 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (false, vertices_465) then 21 else
  if p.val = (true, vertices_646) then 14 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_592) then 11 else
  0
cert_priority
cert_nodeAtPriority_67 0 45 1 553 146 274 530 162 84 148 532 548 580 592 803 646 205 421 841 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 5 8 620 44 3
cert_row_2 1 0 1 6 8 646
cert_row_4 2 0 3 4 6 7 434 146 2
cert_row_4 3 0 3 5 7 8 850 274 2
cert_rows
cert_pivot_2 2 1 4 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 646 662 2
cert_coverFacet 1 678
cert_cover_5 1 1 0 1 4 6 646 678 2
cert_coverFacet 2 434
cert_cover_5 2 2 0 3 4 6 146 434 2
cert_coverFacet 3 850
cert_cover_5 3 3 0 3 5 7 274 850 2
cert_coverFacet 4 620
cert_cover_5 4 0 1 2 4 5 44 620 3
cert_coverFacet 5 212
cert_cover_2 5 3 1 5 6 84 212 3
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0086

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m14e10q1_0087.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0087

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 141, 525, 709, 793, 425, 689, 346, 562, 594, 482, 738, 604, 460, 13, 133, 517, 137, 265, 521, 49, 273, 529, 161, 289, 641, 50, 82, 274, 530, 226, 290, 546, 322, 578, 76, 140, 524, 196, 580, 88, 280, 536, 328, 392, 560, 592, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_141, vertices_525, vertices_709, vertices_793, vertices_425, vertices_689, vertices_346, vertices_562, vertices_594, vertices_482, vertices_738, vertices_604, vertices_460] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_137, vertices_265, vertices_521, vertices_49, vertices_273, vertices_529, vertices_161, vertices_289, vertices_641, vertices_50, vertices_82, vertices_274, vertices_530, vertices_226, vertices_290, vertices_546, vertices_322, vertices_578, vertices_76, vertices_140, vertices_524, vertices_196, vertices_580, vertices_88, vertices_280, vertices_536, vertices_328, vertices_392, vertices_560, vertices_592, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_141), (false, vertices_525), (false, vertices_709), (false, vertices_793), (false, vertices_425), (false, vertices_689), (true, vertices_82), (true, vertices_530), (true, vertices_226), (true, vertices_546), (true, vertices_322), (true, vertices_578), (true, vertices_76), (true, vertices_88), (true, vertices_328), (true, vertices_592), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 13 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_709) then 16 else
  if p.val = (false, vertices_793) then 18 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_226) then 14 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_226), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 5 6 226
cert_row_4 1 0 2 3 5 7 346 82 1
cert_row_4 2 1 2 3 5 8 604 76 2
cert_row_4 3 1 2 5 6 7 460 76 3
cert_rows
cert_pivot_2 4 0 3 1
cert_heightProof 4
cert_coverFacet 0 346
cert_cover_5 0 1 0 2 3 5 82 346 1
cert_coverFacet 1 562
cert_cover_2 1 3 0 4 8 50 562 3
cert_coverFacet 2 594
cert_cover_2 2 3 0 5 8 82 594 3
cert_coverFacet 3 482
cert_cover_5 3 0 0 4 5 7 226 482 3
cert_coverFacet 4 738
cert_cover_5 4 0 0 4 5 8 226 738 3
cert_coverFacet 5 604
cert_cover_5 5 2 1 2 3 5 76 604 2
cert_coverFacet 6 460
cert_cover_5 6 3 1 2 5 6 76 460 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0087

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m14e10q1_0088.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0088

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 77, 837, 409, 713, 929, 94, 118, 294, 282, 434, 740, 804, 248, 13, 69, 261, 73, 137, 265, 577, 385, 641, 769, 14, 86, 38, 262, 26, 266, 50, 274, 290, 76, 100, 292, 548, 580, 772, 88, 152, 280, 200, 112, 176, 400, 224, 416, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_77, vertices_837, vertices_409, vertices_713, vertices_929, vertices_94, vertices_118, vertices_294, vertices_282, vertices_434, vertices_740, vertices_804, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_73, vertices_137, vertices_265, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_86, vertices_38, vertices_262, vertices_26, vertices_266, vertices_50, vertices_274, vertices_290, vertices_76, vertices_100, vertices_292, vertices_548, vertices_580, vertices_772, vertices_88, vertices_152, vertices_280, vertices_200, vertices_112, vertices_176, vertices_400, vertices_224, vertices_416, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_77), (false, vertices_837), (false, vertices_409), (false, vertices_713), (false, vertices_929), (true, vertices_86), (true, vertices_38), (true, vertices_26), (true, vertices_50), (true, vertices_274), (true, vertices_290), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_88), (true, vertices_112), (true, vertices_176), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 14 else
  if p.val = (false, vertices_77) then 0 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_86) then 15 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_224) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_77), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 7 434 50 3
cert_row_2 1 0 1 3 5 86
cert_row_4 2 1 4 5 6 8 740 100 3
cert_row_4 3 2 3 4 5 6 248 88 2
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 3 14 94 3
cert_coverFacet 1 118
cert_cover_5 1 1 0 1 3 4 86 118 3
cert_coverFacet 2 294
cert_cover_2 2 1 0 4 7 38 294 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 434
cert_cover_5 4 0 0 3 4 6 50 434 3
cert_coverFacet 5 740
cert_cover_5 5 2 1 4 5 6 100 740 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 248
cert_cover_5 7 3 2 3 4 5 88 248 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0088

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m14e10q1_0089.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0089

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [143, 527, 211, 835, 901, 481, 154, 538, 626, 572, 172, 868, 420, 248, 15, 67, 131, 515, 133, 517, 193, 321, 385, 769, 26, 138, 522, 82, 146, 530, 578, 44, 140, 524, 164, 292, 548, 388, 772, 56, 152, 536, 168, 112, 560, 208, 224, 352, 608, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_143, vertices_527, vertices_211, vertices_835, vertices_901, vertices_481, vertices_154, vertices_538, vertices_626, vertices_572, vertices_172, vertices_868, vertices_420, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_15, vertices_67, vertices_131, vertices_515, vertices_133, vertices_517, vertices_193, vertices_321, vertices_385, vertices_769, vertices_26, vertices_138, vertices_522, vertices_82, vertices_146, vertices_530, vertices_578, vertices_44, vertices_140, vertices_524, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_56, vertices_152, vertices_536, vertices_168, vertices_112, vertices_560, vertices_208, vertices_224, vertices_352, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_143), (false, vertices_527), (false, vertices_211), (false, vertices_835), (false, vertices_901), (false, vertices_481), (true, vertices_26), (true, vertices_530), (true, vertices_44), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_168), (true, vertices_112), (true, vertices_560), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 13 20 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_143) then 14 else
  if p.val = (false, vertices_527) then 15 else
  if p.val = (false, vertices_211) then 18 else
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_901) then 16 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_143), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 20 => Sum.inl 2
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
cert_row_4 0 0 3 4 5 8 626 82 2
cert_row_4 1 1 4 5 7 8 868 292 2
cert_row_4 2 1 2 3 4 8 572 44 2
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 154
cert_cover_2 0 2 0 3 6 26 154 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 626
cert_cover_5 2 0 0 3 4 5 82 626 2
cert_coverFacet 3 572
cert_cover_5 3 2 1 2 3 4 44 572 2
cert_coverFacet 4 172
cert_cover_2 4 2 1 4 6 44 172 3
cert_coverFacet 5 868
cert_cover_5 5 1 1 4 5 7 292 868 2
cert_coverFacet 6 420
cert_cover_2 6 4 1 6 7 164 420 3
cert_coverFacet 7 248
cert_cover_5 7 3 2 3 4 5 56 248 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0089

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2253 : Certifies 2253 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0006.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2254 : Certifies 2254 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0011.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2255 : Certifies 2255 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0012.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2256 : Certifies 2256 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0013.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2257 : Certifies 2257 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0018.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2258 : Certifies 2258 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0019.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2259 : Certifies 2259 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0022.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2260 : Certifies 2260 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0024.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2261 : Certifies 2261 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0033.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2262 : Certifies 2262 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0034.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2263 : Certifies 2263 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0036.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2264 : Certifies 2264 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0037.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2265 : Certifies 2265 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0038.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2266 : Certifies 2266 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0039.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2267 : Certifies 2267 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0042.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2268 : Certifies 2268 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0046.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2269 : Certifies 2269 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0047.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2270 : Certifies 2270 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0052.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2271 : Certifies 2271 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0053.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2272 : Certifies 2272 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0060.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2273 : Certifies 2273 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0073.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2274 : Certifies 2274 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0074.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2275 : Certifies 2275 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0075.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2276 : Certifies 2276 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0077.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2277 : Certifies 2277 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0078.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2278 : Certifies 2278 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0084.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2279 : Certifies 2279 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0086.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2280 : Certifies 2280 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0087.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2281 : Certifies 2281 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0088.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2282 : Certifies 2282 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0089.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B074 (j : Fin 30) :
    Certifies (2253 + j.val) := by
  fin_cases j
  · exact projection_2253
  · exact projection_2254
  · exact projection_2255
  · exact projection_2256
  · exact projection_2257
  · exact projection_2258
  · exact projection_2259
  · exact projection_2260
  · exact projection_2261
  · exact projection_2262
  · exact projection_2263
  · exact projection_2264
  · exact projection_2265
  · exact projection_2266
  · exact projection_2267
  · exact projection_2268
  · exact projection_2269
  · exact projection_2270
  · exact projection_2271
  · exact projection_2272
  · exact projection_2273
  · exact projection_2274
  · exact projection_2275
  · exact projection_2276
  · exact projection_2277
  · exact projection_2278
  · exact projection_2279
  · exact projection_2280
  · exact projection_2281
  · exact projection_2282

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
