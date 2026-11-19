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
/- Source: ProjectionCertificates/R_m14e10q1_0511.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0511

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 901, 841, 625, 657, 481, 142, 782, 662, 122, 602, 170, 428, 360, 49, 145, 529, 97, 161, 321, 577, 385, 641, 769, 14, 134, 518, 90, 42, 138, 522, 50, 146, 530, 162, 140, 268, 388, 644, 772, 104, 168, 296, 328, 584, 776, 112, 592, 656, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_901, vertices_841, vertices_625, vertices_657, vertices_481, vertices_142, vertices_782, vertices_662, vertices_122, vertices_602, vertices_170, vertices_428, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_529, vertices_97, vertices_161, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_134, vertices_518, vertices_90, vertices_42, vertices_138, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_140, vertices_268, vertices_388, vertices_644, vertices_772, vertices_104, vertices_168, vertices_296, vertices_328, vertices_584, vertices_776, vertices_112, vertices_592, vertices_656, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_901), (false, vertices_841), (false, vertices_625), (false, vertices_657), (false, vertices_481), (true, vertices_14), (true, vertices_134), (true, vertices_518), (true, vertices_90), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_530), (true, vertices_140), (true, vertices_268), (true, vertices_104), (true, vertices_168), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 14 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_90) then 15 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_296) then 12 else
  0
cert_priority
cert_nodeAtPriority_49 657 14 134 518 42 138 522 530 140 268 104 168 296 179 90 901 841 625 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 3 6 8 662 134 2
cert_row_4 2 0 1 2 7 8 782 14 3
cert_row_4 3 1 2 4 6 7 428 140 2
cert_rows
cert_pivot_2 5 3 0 1
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 782
cert_cover_5 1 2 0 1 2 7 14 782 3
cert_coverFacet 2 662
cert_cover_5 2 1 0 1 3 6 134 662 2
cert_coverFacet 3 122
cert_cover_5 3 0 0 2 3 4 90 122 3
cert_coverFacet 4 602
cert_cover_5 4 0 0 2 3 8 90 602 3
cert_coverFacet 5 170
cert_cover_2 5 2 0 4 6 42 170 3
cert_coverFacet 6 428
cert_cover_5 6 3 1 2 4 6 140 428 2
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0511

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m14e10q1_0512.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0512

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 341, 661, 389, 569, 89, 713, 902, 234, 682, 818, 354, 788, 376, 21, 133, 261, 25, 73, 521, 81, 529, 193, 321, 385, 641, 170, 98, 290, 546, 194, 322, 386, 642, 770, 276, 532, 388, 644, 772, 56, 88, 104, 552, 200, 648, 304, 560, 336, 784, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_341, vertices_661, vertices_389, vertices_569, vertices_89, vertices_713, vertices_902, vertices_234, vertices_682, vertices_818, vertices_354, vertices_788, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_25, vertices_73, vertices_521, vertices_81, vertices_529, vertices_193, vertices_321, vertices_385, vertices_641, vertices_170, vertices_98, vertices_290, vertices_546, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_276, vertices_532, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_104, vertices_552, vertices_200, vertices_648, vertices_304, vertices_560, vertices_336, vertices_784, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_341), (false, vertices_661), (false, vertices_389), (false, vertices_569), (false, vertices_89), (false, vertices_713), (true, vertices_170), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_770), (true, vertices_772), (true, vertices_104), (true, vertices_304), (true, vertices_784), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 13 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_89) then 1 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (true, vertices_170) then 14 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
cert_nodeAtPriority_10 0 389 1 89 98 290 546 642 770 772 104 304 784 352 451 170 341 661 569 713
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_2 1 0 2 4 6 170
cert_row_4 2 0 3 4 7 8 818 290 1
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 234
cert_cover_5 1 1 0 2 4 5 170 234 3
cert_coverFacet 2 682
cert_cover_5 2 1 0 2 4 8 170 682 3
cert_coverFacet 3 818
cert_cover_5 3 2 0 3 4 7 290 818 1
cert_coverFacet 4 354
cert_cover_2 4 4 0 5 7 98 354 3
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 56 376 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0512

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m14e10q1_0515.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0515

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 789, 425, 713, 777, 465, 118, 534, 550, 682, 482, 706, 812, 372, 137, 265, 521, 81, 273, 529, 193, 577, 385, 769, 22, 38, 518, 82, 530, 98, 162, 546, 194, 578, 642, 116, 276, 532, 292, 548, 772, 168, 296, 552, 648, 776, 336, 352, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_789, vertices_425, vertices_713, vertices_777, vertices_465, vertices_118, vertices_534, vertices_550, vertices_682, vertices_482, vertices_706, vertices_812, vertices_372] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_81, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_769, vertices_22, vertices_38, vertices_518, vertices_82, vertices_530, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_116, vertices_276, vertices_532, vertices_292, vertices_548, vertices_772, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_336, vertices_352, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_789), (false, vertices_425), (false, vertices_713), (false, vertices_777), (false, vertices_465), (true, vertices_22), (true, vertices_38), (true, vertices_518), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_642), (true, vertices_116), (true, vertices_292), (true, vertices_548), (true, vertices_552), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_789) then 16 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_116) then 17 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
cert_nodeAtPriority_2 0 777 1 22 2 38 3 518 98 162 546 194 642 292 548 552 352 595 789 116 425 713 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 4 5 116
cert_row_4 1 0 4 5 6 7 482 98 3
cert_row_4 2 0 2 4 6 8 682 162 1
cert_row_4 3 1 2 4 7 8 812 292 1
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 0 0 1 3 4 22 118 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 682
cert_cover_5 3 2 0 2 4 6 162 682 1
cert_coverFacet 4 482
cert_cover_5 4 1 0 4 5 6 98 482 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 812
cert_cover_5 6 3 1 2 4 7 292 812 1
cert_coverFacet 7 372
cert_cover_5 7 0 1 3 4 7 116 372 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0515

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m14e10q1_0518.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0518

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 405, 345, 625, 657, 481, 302, 558, 662, 390, 418, 604, 284, 872, 81, 145, 273, 529, 97, 161, 545, 321, 385, 641, 46, 134, 262, 518, 162, 290, 546, 386, 642, 28, 268, 524, 148, 276, 532, 388, 88, 280, 296, 552, 328, 584, 592, 656, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_405, vertices_345, vertices_625, vertices_657, vertices_481, vertices_302, vertices_558, vertices_662, vertices_390, vertices_418, vertices_604, vertices_284, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_321, vertices_385, vertices_641, vertices_46, vertices_134, vertices_262, vertices_518, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_28, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_388, vertices_88, vertices_280, vertices_296, vertices_552, vertices_328, vertices_584, vertices_592, vertices_656, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_405), (false, vertices_345), (false, vertices_625), (false, vertices_657), (false, vertices_481), (true, vertices_46), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_290), (true, vertices_386), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_532), (true, vertices_296), (true, vertices_552), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_46) then 15 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_584) then 12 else
  0
cert_priority
cert_nodeAtPriority_49 657 134 262 518 290 386 28 268 524 532 296 552 584 675 46 405 345 625 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 134 2
cert_row_2 1 0 1 2 4 46
cert_row_4 2 1 2 3 5 8 604 28 3
cert_row_4 3 2 4 5 7 8 872 296 2
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 1 0 1 2 7 46 302 3
cert_coverFacet 1 558
cert_cover_5 1 1 0 1 2 8 46 558 3
cert_coverFacet 2 662
cert_cover_5 2 0 0 1 3 6 134 662 2
cert_coverFacet 3 390
cert_cover_2 3 1 0 6 7 134 390 3
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 604
cert_cover_5 5 2 1 2 3 5 28 604 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 872
cert_cover_5 7 3 2 4 5 7 296 872 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0518

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m14e10q1_0519.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0519

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [87, 539, 99, 803, 533, 357, 901, 218, 234, 554, 468, 660, 696, 992, 19, 35, 67, 515, 21, 69, 261, 517, 529, 97, 289, 769, 26, 42, 202, 522, 82, 98, 546, 84, 148, 532, 324, 388, 644, 152, 536, 168, 552, 208, 656, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_87, vertices_539, vertices_99, vertices_803, vertices_533, vertices_357, vertices_901, vertices_218, vertices_234, vertices_554, vertices_468, vertices_660, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_67, vertices_515, vertices_21, vertices_69, vertices_261, vertices_517, vertices_529, vertices_97, vertices_289, vertices_769, vertices_26, vertices_42, vertices_202, vertices_522, vertices_82, vertices_98, vertices_546, vertices_84, vertices_148, vertices_532, vertices_324, vertices_388, vertices_644, vertices_152, vertices_536, vertices_168, vertices_552, vertices_208, vertices_656, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_87), (false, vertices_539), (false, vertices_99), (false, vertices_803), (false, vertices_533), (false, vertices_357), (false, vertices_901), (true, vertices_42), (true, vertices_202), (true, vertices_148), (true, vertices_152), (true, vertices_168), (true, vertices_552), (true, vertices_208), (true, vertices_656), (true, vertices_224), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 12 20 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_87) then 13 else
  if p.val = (false, vertices_539) then 17 else
  if p.val = (false, vertices_99) then 0 else
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_357) then 14 else
  if p.val = (false, vertices_901) then 15 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_202) then 19 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_99), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_87), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_4 1 1 3 5 6 7 468 84 3
cert_row_4 2 2 3 4 6 8 696 152 2
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 218
cert_cover_5 0 0 0 2 3 5 26 218 3
cert_coverFacet 1 234
cert_cover_5 1 0 0 2 4 5 42 234 3
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 468
cert_cover_5 3 1 1 3 5 6 84 468 3
cert_coverFacet 4 660
cert_cover_2 4 3 1 6 8 148 660 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 152 696 2
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0519

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m14e10q1_0520.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0520

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 51, 403, 901, 617, 777, 689, 454, 626, 722, 354, 364, 716, 780, 19, 35, 259, 41, 265, 521, 49, 145, 545, 385, 641, 769, 50, 594, 146, 98, 290, 194, 322, 386, 76, 268, 524, 196, 324, 388, 644, 772, 104, 296, 584, 776, 560, 656, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_51, vertices_403, vertices_901, vertices_617, vertices_777, vertices_689, vertices_454, vertices_626, vertices_722, vertices_354, vertices_364, vertices_716, vertices_780] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_41, vertices_265, vertices_521, vertices_49, vertices_145, vertices_545, vertices_385, vertices_641, vertices_769, vertices_50, vertices_594, vertices_146, vertices_98, vertices_290, vertices_194, vertices_322, vertices_386, vertices_76, vertices_268, vertices_524, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_104, vertices_296, vertices_584, vertices_776, vertices_560, vertices_656, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_51), (false, vertices_403), (false, vertices_901), (false, vertices_617), (false, vertices_777), (false, vertices_689), (true, vertices_594), (true, vertices_98), (true, vertices_194), (true, vertices_322), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_196), (true, vertices_324), (true, vertices_352), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 13 else
  if p.val = (false, vertices_51) then 0 else
  if p.val = (false, vertices_403) then 14 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_594) then 15 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_704) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_594), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
cert_row_2 0 0 3 5 8 594
cert_row_4 1 0 1 5 6 7 454 194 1
cert_row_4 2 1 2 4 5 7 364 76 2
cert_row_4 3 1 2 5 6 8 716 76 3
cert_rows
cert_pivot_2 3 0 4 1
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 1 0 1 5 6 194 454 1
cert_coverFacet 1 626
cert_cover_5 1 0 0 3 4 5 50 626 3
cert_coverFacet 2 722
cert_cover_5 2 0 0 3 5 6 594 722 3
cert_coverFacet 3 354
cert_cover_2 3 4 0 5 7 98 354 3
cert_coverFacet 4 364
cert_cover_5 4 2 1 2 4 5 76 364 2
cert_coverFacet 5 716
cert_cover_5 5 3 1 2 5 6 76 716 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0520

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m14e10q1_0523.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0523

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 789, 421, 645, 713, 465, 806, 618, 242, 434, 786, 236, 556, 652, 133, 261, 517, 81, 273, 529, 193, 577, 385, 641, 178, 82, 274, 530, 98, 290, 546, 578, 770, 44, 140, 524, 164, 292, 548, 644, 772, 104, 552, 200, 584, 648, 208, 400, 784, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_789, vertices_421, vertices_645, vertices_713, vertices_465, vertices_806, vertices_618, vertices_242, vertices_434, vertices_786, vertices_236, vertices_556, vertices_652] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_81, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_641, vertices_178, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_44, vertices_140, vertices_524, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_104, vertices_552, vertices_200, vertices_584, vertices_648, vertices_208, vertices_400, vertices_784, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_789), (false, vertices_421), (false, vertices_645), (false, vertices_713), (false, vertices_465), (true, vertices_178), (true, vertices_274), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_548), (true, vertices_104), (true, vertices_552), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_421) then 18 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_178) then 15 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_224) then 12 else
  0
cert_priority
cert_nodeAtPriority_17 645 274 98 290 546 770 44 140 524 548 104 552 224 595 178 789 421 713 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 6 178
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 2 4 5 8 618 98 1
cert_row_4 3 1 2 4 5 6 236 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 618
cert_cover_5 1 2 0 2 4 5 98 618 1
cert_coverFacet 2 242
cert_cover_5 2 0 0 3 4 5 178 242 3
cert_coverFacet 3 434
cert_cover_5 3 0 0 3 4 7 178 434 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 236
cert_cover_5 5 3 1 2 4 5 44 236 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0523

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m14e10q1_0524.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0524

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 781, 613, 453, 241, 417, 286, 122, 618, 778, 434, 604, 212, 404, 69, 261, 517, 97, 161, 289, 545, 193, 385, 769, 26, 106, 266, 522, 50, 274, 290, 546, 770, 28, 268, 524, 84, 148, 276, 196, 580, 388, 88, 584, 776, 112, 176, 208, 400, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_781, vertices_613, vertices_453, vertices_241, vertices_417, vertices_286, vertices_122, vertices_618, vertices_778, vertices_434, vertices_604, vertices_212, vertices_404] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_385, vertices_769, vertices_26, vertices_106, vertices_266, vertices_522, vertices_50, vertices_274, vertices_290, vertices_546, vertices_770, vertices_28, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_196, vertices_580, vertices_388, vertices_88, vertices_584, vertices_776, vertices_112, vertices_176, vertices_208, vertices_400, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_781), (false, vertices_613), (false, vertices_453), (false, vertices_241), (false, vertices_417), (true, vertices_26), (true, vertices_106), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_28), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_88), (true, vertices_584), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_106) then 15 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_106), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 7 434 50 3
cert_row_2 1 0 2 4 5 106
cert_row_4 2 0 1 2 3 7 286 26 1
cert_row_4 3 1 2 3 5 8 604 28 3
cert_rows
cert_pivot_2 6 4 0 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 2 0 1 2 3 26 286 1
cert_coverFacet 1 122
cert_cover_5 1 1 0 2 3 4 26 122 3
cert_coverFacet 2 618
cert_cover_5 2 1 0 2 4 8 106 618 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 434
cert_cover_5 4 0 0 3 4 6 50 434 3
cert_coverFacet 5 604
cert_cover_5 5 3 1 2 3 5 28 604 3
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0524

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m14e10q1_0525.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0525

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 901, 569, 361, 777, 433, 710, 370, 562, 466, 610, 620, 460, 780, 41, 265, 521, 49, 145, 529, 289, 385, 641, 769, 50, 338, 146, 530, 98, 546, 194, 578, 642, 76, 268, 524, 196, 580, 388, 644, 772, 104, 552, 328, 776, 304, 560, 400, 352, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_901, vertices_569, vertices_361, vertices_777, vertices_433, vertices_710, vertices_370, vertices_562, vertices_466, vertices_610, vertices_620, vertices_460, vertices_780] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_265, vertices_521, vertices_49, vertices_145, vertices_529, vertices_289, vertices_385, vertices_641, vertices_769, vertices_50, vertices_338, vertices_146, vertices_530, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_76, vertices_268, vertices_524, vertices_196, vertices_580, vertices_388, vertices_644, vertices_772, vertices_104, vertices_552, vertices_328, vertices_776, vertices_304, vertices_560, vertices_400, vertices_352, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_901), (false, vertices_569), (false, vertices_361), (false, vertices_777), (false, vertices_433), (true, vertices_50), (true, vertices_338), (true, vertices_98), (true, vertices_546), (true, vertices_194), (true, vertices_578), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_196), (true, vertices_580), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_338) then 15 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
cert_priority
cert_nodeAtPriority_37 777 50 98 546 194 578 76 268 524 196 580 608 448 659 338 901 569 361 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 7 338
cert_row_4 1 0 1 5 6 8 710 194 1
cert_row_4 2 1 2 4 5 8 620 76 2
cert_row_4 3 1 2 5 6 7 460 76 3
cert_rows
cert_pivot_2 3 0 4 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 1 0 1 5 6 194 710 1
cert_coverFacet 1 370
cert_cover_5 1 0 0 3 4 5 50 370 3
cert_coverFacet 2 562
cert_cover_2 2 3 0 4 8 50 562 3
cert_coverFacet 3 466
cert_cover_5 3 0 0 3 5 6 338 466 3
cert_coverFacet 4 610
cert_cover_2 4 4 0 5 8 98 610 3
cert_coverFacet 5 620
cert_cover_5 5 2 1 2 4 5 76 620 2
cert_coverFacet 6 460
cert_cover_5 6 3 1 2 5 6 76 460 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0525

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m14e10q1_0526.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0526

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 141, 525, 901, 185, 817, 481, 590, 218, 242, 562, 610, 460, 868, 13, 133, 517, 25, 137, 521, 49, 529, 161, 289, 385, 769, 26, 74, 522, 50, 210, 530, 98, 546, 578, 76, 140, 524, 324, 580, 388, 772, 152, 200, 176, 560, 224, 352, 608, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_141, vertices_525, vertices_901, vertices_185, vertices_817, vertices_481, vertices_590, vertices_218, vertices_242, vertices_562, vertices_610, vertices_460, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_25, vertices_137, vertices_521, vertices_49, vertices_529, vertices_161, vertices_289, vertices_385, vertices_769, vertices_26, vertices_74, vertices_522, vertices_50, vertices_210, vertices_530, vertices_98, vertices_546, vertices_578, vertices_76, vertices_140, vertices_524, vertices_324, vertices_580, vertices_388, vertices_772, vertices_152, vertices_200, vertices_176, vertices_560, vertices_224, vertices_352, vertices_608, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_141), (false, vertices_525), (false, vertices_901), (false, vertices_185), (false, vertices_817), (false, vertices_481), (true, vertices_74), (true, vertices_50), (true, vertices_210), (true, vertices_98), (true, vertices_546), (true, vertices_578), (true, vertices_76), (true, vertices_324), (true, vertices_580), (true, vertices_200), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 19 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 13 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_901) then 16 else
  if p.val = (false, vertices_185) then 18 else
  if p.val = (false, vertices_817) then 20 else
  if p.val = (false, vertices_481) then 22 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_210) then 14 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_608) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 6 210
cert_row_4 1 0 1 2 5 8 590 74 1
cert_row_4 2 1 2 5 6 7 460 76 3
cert_row_4 3 1 4 5 7 8 868 324 1
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 74 590 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 5 26 218 3
cert_coverFacet 2 242
cert_cover_5 2 0 0 3 4 5 50 242 3
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 610
cert_cover_2 4 4 0 5 8 98 610 3
cert_coverFacet 5 460
cert_cover_5 5 2 1 2 5 6 76 460 3
cert_coverFacet 6 868
cert_cover_5 6 3 1 4 5 7 324 868 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0526

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m14e10q1_0527.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0527

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 805, 601, 409, 361, 785, 678, 458, 714, 354, 418, 668, 436, 788, 25, 73, 265, 273, 529, 97, 289, 545, 577, 769, 202, 98, 162, 290, 546, 322, 578, 386, 642, 148, 276, 532, 164, 292, 548, 644, 772, 152, 536, 328, 584, 392, 648, 400, 784, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_805, vertices_601, vertices_409, vertices_361, vertices_785, vertices_678, vertices_458, vertices_714, vertices_354, vertices_418, vertices_668, vertices_436, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_577, vertices_769, vertices_202, vertices_98, vertices_162, vertices_290, vertices_546, vertices_322, vertices_578, vertices_386, vertices_642, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_152, vertices_536, vertices_328, vertices_584, vertices_392, vertices_648, vertices_400, vertices_784, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_805), (false, vertices_601), (false, vertices_409), (false, vertices_361), (false, vertices_785), (true, vertices_202), (true, vertices_162), (true, vertices_290), (true, vertices_322), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_644), (true, vertices_648), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 14 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (true, vertices_202) then 15 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 1 2 3 6 8 668 148 1
cert_row_4 3 1 3 4 6 7 436 148 2
cert_rows
cert_pivot_2 5 0 2 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 714
cert_cover_5 2 0 0 2 5 8 202 714 3
cert_coverFacet 3 354
cert_cover_2 3 4 0 5 7 98 354 3
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 668
cert_cover_5 5 2 1 2 3 6 148 668 1
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 148 436 2
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0527

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m14e10q1_0528.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0528

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 595, 309, 713, 689, 481, 590, 566, 278, 326, 300, 556, 460, 936, 83, 49, 273, 529, 161, 289, 193, 321, 577, 641, 22, 70, 262, 518, 274, 530, 322, 578, 44, 76, 268, 524, 52, 276, 292, 548, 324, 296, 552, 200, 584, 392, 648, 560, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_595, vertices_309, vertices_713, vertices_689, vertices_481, vertices_590, vertices_566, vertices_278, vertices_326, vertices_300, vertices_556, vertices_460, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_83, vertices_49, vertices_273, vertices_529, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_641, vertices_22, vertices_70, vertices_262, vertices_518, vertices_274, vertices_530, vertices_322, vertices_578, vertices_44, vertices_76, vertices_268, vertices_524, vertices_52, vertices_276, vertices_292, vertices_548, vertices_324, vertices_296, vertices_552, vertices_200, vertices_584, vertices_392, vertices_648, vertices_560, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_595), (false, vertices_309), (false, vertices_713), (false, vertices_689), (false, vertices_481), (true, vertices_22), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_548), (true, vertices_324), (true, vertices_296), (true, vertices_552), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 14 else
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_309) then 17 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_392) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 22 3
cert_row_4 1 0 1 2 5 8 590 70 2
cert_row_4 2 1 2 5 6 7 460 76 3
cert_row_4 3 2 4 6 7 8 936 296 2
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 70 590 2
cert_coverFacet 1 566
cert_cover_5 1 0 0 1 3 4 22 566 3
cert_coverFacet 2 278
cert_cover_2 2 1 0 3 7 22 278 3
cert_coverFacet 3 326
cert_cover_2 3 1 0 5 7 70 326 3
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 460
cert_cover_5 6 2 1 2 5 6 76 460 3
cert_coverFacet 7 936
cert_cover_5 7 3 2 4 6 7 296 936 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0528

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m14e10q1_0533.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0533

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 61, 597, 677, 89, 425, 457, 810, 850, 482, 674, 796, 556, 344, 21, 37, 517, 25, 41, 73, 393, 81, 161, 193, 577, 641, 162, 290, 546, 194, 322, 578, 642, 770, 28, 44, 524, 532, 548, 88, 280, 296, 552, 328, 776, 336, 592, 784, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_61, vertices_597, vertices_677, vertices_89, vertices_425, vertices_457, vertices_810, vertices_850, vertices_482, vertices_674, vertices_796, vertices_556, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_517, vertices_25, vertices_41, vertices_73, vertices_393, vertices_81, vertices_161, vertices_193, vertices_577, vertices_641, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_44, vertices_524, vertices_532, vertices_548, vertices_88, vertices_280, vertices_296, vertices_552, vertices_328, vertices_776, vertices_336, vertices_592, vertices_784, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_61), (false, vertices_597), (false, vertices_677), (false, vertices_89), (false, vertices_425), (false, vertices_457), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_770), (true, vertices_524), (true, vertices_280), (true, vertices_552), (true, vertices_776), (true, vertices_336), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 13 else
  if p.val = (false, vertices_61) then 15 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_89) then 0 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_784) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_89), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_4 0 0 4 5 6 7 482 162 2
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_4 2 0 3 5 7 8 850 322 1
cert_row_4 3 1 2 3 7 8 796 28 3
cert_rows
cert_pivot_2 6 4 0 1
cert_heightProof 4
cert_coverFacet 0 810
cert_cover_5 0 1 0 2 4 7 290 810 1
cert_coverFacet 1 850
cert_cover_5 1 2 0 3 5 7 322 850 1
cert_coverFacet 2 482
cert_cover_5 2 0 0 4 5 6 162 482 2
cert_coverFacet 3 674
cert_cover_2 3 4 0 6 8 162 674 3
cert_coverFacet 4 796
cert_cover_5 4 3 1 2 3 7 28 796 3
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0533

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m14e10q1_0535.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0535

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 339, 803, 643, 653, 85, 837, 682, 178, 306, 220, 620, 248, 880, 19, 131, 259, 515, 21, 69, 133, 517, 81, 321, 641, 769, 50, 146, 274, 162, 290, 546, 642, 76, 140, 524, 84, 148, 580, 216, 104, 168, 552, 648, 112, 176, 304, 336, 608, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_339, vertices_803, vertices_643, vertices_653, vertices_85, vertices_837, vertices_682, vertices_178, vertices_306, vertices_220, vertices_620, vertices_248, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_21, vertices_69, vertices_133, vertices_517, vertices_81, vertices_321, vertices_641, vertices_769, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_642, vertices_76, vertices_140, vertices_524, vertices_84, vertices_148, vertices_580, vertices_216, vertices_104, vertices_168, vertices_552, vertices_648, vertices_112, vertices_176, vertices_304, vertices_336, vertices_608, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_339), (false, vertices_803), (false, vertices_643), (false, vertices_653), (false, vertices_85), (false, vertices_837), (true, vertices_50), (true, vertices_162), (true, vertices_76), (true, vertices_216), (true, vertices_104), (true, vertices_168), (true, vertices_552), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 13 else
  if p.val = (false, vertices_339) then 14 else
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_85) then 1 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_216) then 20 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_608) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 162 1
cert_row_2 1 2 3 5 6 216
cert_row_4 2 1 2 4 5 8 620 76 2
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 6 1 3
cert_heightProof 4
cert_coverFacet 0 682
cert_cover_5 0 0 0 2 4 6 162 682 1
cert_coverFacet 1 178
cert_cover_2 1 3 0 4 6 50 178 3
cert_coverFacet 2 306
cert_cover_2 2 3 0 4 7 50 306 3
cert_coverFacet 3 220
cert_cover_5 3 1 1 2 3 5 76 220 2
cert_coverFacet 4 620
cert_cover_5 4 2 1 2 4 5 76 620 2
cert_coverFacet 5 248
cert_cover_5 5 1 2 3 4 5 216 248 2
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0535

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m14e10q1_0539.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0539

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 91, 523, 653, 117, 229, 457, 330, 906, 370, 786, 692, 816, 992, 11, 19, 515, 21, 101, 133, 517, 73, 137, 521, 81, 193, 74, 266, 522, 82, 274, 530, 322, 770, 52, 532, 164, 644, 328, 392, 648, 112, 304, 560, 784, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_91, vertices_523, vertices_653, vertices_117, vertices_229, vertices_457, vertices_330, vertices_906, vertices_370, vertices_786, vertices_692, vertices_816, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_515, vertices_21, vertices_101, vertices_133, vertices_517, vertices_73, vertices_137, vertices_521, vertices_81, vertices_193, vertices_74, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_322, vertices_770, vertices_52, vertices_532, vertices_164, vertices_644, vertices_328, vertices_392, vertices_648, vertices_112, vertices_304, vertices_560, vertices_784, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_91), (false, vertices_523), (false, vertices_653), (false, vertices_117), (false, vertices_229), (false, vertices_457), (true, vertices_266), (true, vertices_274), (true, vertices_322), (true, vertices_770), (true, vertices_304), (true, vertices_560), (true, vertices_784), (true, vertices_352), (true, vertices_672), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 13 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_117) then 17 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 19 => Sum.inl 2
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
cert_row_4 0 0 2 6 7 8 906 266 2
cert_row_4 1 0 3 4 5 7 370 82 2
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 2 0 1 4
cert_heightProof 4
cert_coverFacet 0 330
cert_cover_2 0 2 0 5 7 74 330 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 266 906 2
cert_coverFacet 2 370
cert_cover_5 2 1 0 3 4 5 82 370 2
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 692
cert_cover_5 4 2 1 3 4 6 52 692 3
cert_coverFacet 5 816
cert_cover_2 5 4 3 7 8 304 816 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0539

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m14e10q1_0540.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0540

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [147, 275, 227, 835, 613, 793, 689, 358, 422, 410, 668, 844, 396, 676, 19, 67, 131, 259, 145, 273, 529, 97, 161, 545, 577, 769, 294, 146, 274, 98, 162, 322, 386, 140, 268, 524, 100, 164, 548, 324, 580, 388, 644, 152, 280, 536, 392, 776, 656, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_147, vertices_275, vertices_227, vertices_835, vertices_613, vertices_793, vertices_689, vertices_358, vertices_422, vertices_410, vertices_668, vertices_844, vertices_396, vertices_676] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_131, vertices_259, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_577, vertices_769, vertices_294, vertices_146, vertices_274, vertices_98, vertices_162, vertices_322, vertices_386, vertices_140, vertices_268, vertices_524, vertices_100, vertices_164, vertices_548, vertices_324, vertices_580, vertices_388, vertices_644, vertices_152, vertices_280, vertices_536, vertices_392, vertices_776, vertices_656, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_147), (false, vertices_275), (false, vertices_227), (false, vertices_835), (false, vertices_613), (false, vertices_793), (false, vertices_689), (true, vertices_294), (true, vertices_386), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_164), (true, vertices_324), (true, vertices_388), (true, vertices_644), (true, vertices_152), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_275) then 1 else
  if p.val = (false, vertices_227) then 13 else
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_294) then 15 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_392) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_294), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
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
cert_row_2 0 0 1 4 7 294
cert_row_4 1 0 2 3 6 7 410 146 1
cert_row_4 2 1 2 3 6 8 668 140 2
cert_row_4 3 1 2 5 7 8 844 268 2
cert_rows
cert_pivot_2 4 0 3 1
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 0 0 1 4 5 294 358 3
cert_coverFacet 1 422
cert_cover_5 1 0 0 1 4 6 294 422 3
cert_coverFacet 2 410
cert_cover_5 2 1 0 2 3 6 146 410 1
cert_coverFacet 3 668
cert_cover_5 3 2 1 2 3 6 140 668 2
cert_coverFacet 4 844
cert_cover_5 4 3 1 2 5 7 268 844 2
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0540

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m14e10q1_0542.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0542

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 29, 301, 149, 901, 569, 865, 158, 206, 602, 962, 108, 484, 616, 13, 21, 133, 261, 25, 41, 145, 529, 289, 545, 641, 769, 142, 26, 74, 146, 530, 194, 578, 642, 28, 44, 76, 148, 100, 292, 196, 388, 536, 104, 552, 584, 352, 608, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_29, vertices_301, vertices_149, vertices_901, vertices_569, vertices_865, vertices_158, vertices_206, vertices_602, vertices_962, vertices_108, vertices_484, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_133, vertices_261, vertices_25, vertices_41, vertices_145, vertices_529, vertices_289, vertices_545, vertices_641, vertices_769, vertices_142, vertices_26, vertices_74, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_28, vertices_44, vertices_76, vertices_148, vertices_100, vertices_292, vertices_196, vertices_388, vertices_536, vertices_104, vertices_552, vertices_584, vertices_352, vertices_608, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_29), (false, vertices_301), (false, vertices_149), (false, vertices_901), (false, vertices_569), (false, vertices_865), (true, vertices_142), (true, vertices_26), (true, vertices_74), (true, vertices_194), (true, vertices_578), (true, vertices_76), (true, vertices_100), (true, vertices_196), (true, vertices_104), (true, vertices_584), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 13 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_301) then 16 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_865) then 22 else
  if p.val = (true, vertices_142) then 14 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_29), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_142), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_2 1 0 1 2 6 142
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 142 158 3
cert_coverFacet 1 206
cert_cover_5 1 1 0 1 2 5 142 206 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 5 26 602 3
cert_coverFacet 3 962
cert_cover_5 3 2 0 5 6 7 194 962 3
cert_coverFacet 4 108
cert_cover_2 4 2 1 4 5 44 108 3
cert_coverFacet 5 484
cert_cover_5 5 3 1 4 5 6 100 484 3
cert_coverFacet 6 616
cert_cover_2 6 4 2 5 8 104 616 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0542

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m14e10q1_0545.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0545

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 589, 117, 293, 901, 737, 310, 122, 410, 234, 92, 284, 780, 968, 37, 69, 261, 517, 97, 161, 289, 577, 385, 641, 26, 106, 138, 50, 274, 162, 290, 386, 28, 76, 268, 524, 52, 84, 276, 292, 772, 88, 280, 200, 584, 392, 776, 112, 224, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_589, vertices_117, vertices_293, vertices_901, vertices_737, vertices_310, vertices_122, vertices_410, vertices_234, vertices_92, vertices_284, vertices_780, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_641, vertices_26, vertices_106, vertices_138, vertices_50, vertices_274, vertices_162, vertices_290, vertices_386, vertices_28, vertices_76, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_292, vertices_772, vertices_88, vertices_280, vertices_200, vertices_584, vertices_392, vertices_776, vertices_112, vertices_224, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_589), (false, vertices_117), (false, vertices_293), (false, vertices_901), (false, vertices_737), (true, vertices_26), (true, vertices_106), (true, vertices_138), (true, vertices_50), (true, vertices_274), (true, vertices_28), (true, vertices_268), (true, vertices_276), (true, vertices_88), (true, vertices_280), (true, vertices_200), (true, vertices_392), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 14 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_117) then 18 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_106) then 15 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_776) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_106), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 20 => Sum.inl 2
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
cert_row_4 0 0 1 3 4 7 310 50 1
cert_row_2 1 0 2 4 5 106
cert_row_4 2 0 2 3 6 7 410 26 3
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 50 310 1
cert_coverFacet 1 122
cert_cover_5 1 1 0 2 3 4 26 122 3
cert_coverFacet 2 410
cert_cover_5 2 2 0 2 3 6 26 410 3
cert_coverFacet 3 234
cert_cover_5 3 1 0 2 4 6 106 234 3
cert_coverFacet 4 92
cert_cover_2 4 2 1 3 5 28 92 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 968
cert_cover_5 7 3 2 5 6 7 200 968 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0545

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m14e10q1_0554.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0554

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 661, 425, 841, 649, 465, 118, 566, 810, 482, 834, 684, 212, 228, 137, 265, 521, 81, 145, 529, 321, 577, 385, 641, 54, 82, 530, 98, 290, 546, 322, 578, 770, 84, 148, 532, 100, 164, 548, 196, 644, 168, 296, 552, 648, 776, 208, 224, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_661, vertices_425, vertices_841, vertices_649, vertices_465, vertices_118, vertices_566, vertices_810, vertices_482, vertices_834, vertices_684, vertices_212, vertices_228] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_529, vertices_321, vertices_577, vertices_385, vertices_641, vertices_54, vertices_82, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_84, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_644, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_208, vertices_224, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_661), (false, vertices_425), (false, vertices_841), (false, vertices_649), (false, vertices_465), (true, vertices_54), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_770), (true, vertices_84), (true, vertices_100), (true, vertices_164), (true, vertices_548), (true, vertices_196), (true, vertices_552), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_649) then 0 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_54) then 15 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_224) then 12 else
  0
cert_priority
cert_nodeAtPriority_37 649 98 290 546 322 770 84 100 164 548 196 552 224 595 54 661 425 841 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 0 4 5 6 7 482 98 3
cert_row_4 2 0 2 4 7 8 810 290 1
cert_row_4 3 1 2 4 6 8 684 164 1
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 0 0 1 3 5 54 118 3
cert_coverFacet 1 566
cert_cover_5 1 0 0 1 3 8 54 566 3
cert_coverFacet 2 810
cert_cover_5 2 2 0 2 4 7 290 810 1
cert_coverFacet 3 482
cert_cover_5 3 1 0 4 5 6 98 482 3
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 684
cert_cover_5 5 3 1 2 4 6 164 684 1
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0554

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m14e10q1_0555.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0555

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 275, 451, 709, 569, 345, 585, 806, 902, 314, 562, 620, 484, 360, 19, 131, 259, 25, 73, 521, 273, 529, 193, 321, 577, 641, 774, 50, 274, 530, 290, 546, 386, 642, 100, 292, 548, 196, 580, 388, 644, 56, 280, 104, 296, 552, 328, 584, 560, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_275, vertices_451, vertices_709, vertices_569, vertices_345, vertices_585, vertices_806, vertices_902, vertices_314, vertices_562, vertices_620, vertices_484, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_25, vertices_73, vertices_521, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_774, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_100, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_644, vertices_56, vertices_280, vertices_104, vertices_296, vertices_552, vertices_328, vertices_584, vertices_560, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_275), (false, vertices_451), (false, vertices_709), (false, vertices_569), (false, vertices_345), (false, vertices_585), (true, vertices_774), (true, vertices_50), (true, vertices_290), (true, vertices_546), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_388), (true, vertices_104), (true, vertices_296), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 13 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_709) then 17 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_585) then 1 else
  if p.val = (true, vertices_774) then 15 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 7 314 50 1
cert_row_2 1 0 1 7 8 774
cert_row_4 2 1 2 4 5 8 620 100 1
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 774 806 2
cert_coverFacet 1 902
cert_cover_5 1 1 0 1 6 7 774 902 2
cert_coverFacet 2 314
cert_cover_5 2 0 0 2 3 4 50 314 1
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 620
cert_cover_5 4 2 1 2 4 5 100 620 1
cert_coverFacet 5 484
cert_cover_5 5 3 1 4 5 6 100 484 3
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0555

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m14e10q1_0562.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0562

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 901, 121, 169, 713, 865, 118, 150, 358, 390, 186, 668, 852, 600, 41, 73, 137, 97, 161, 289, 577, 385, 641, 769, 22, 102, 134, 262, 50, 146, 162, 290, 386, 84, 148, 532, 324, 388, 644, 772, 56, 88, 152, 536, 168, 584, 648, 112, 592, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_901, vertices_121, vertices_169, vertices_713, vertices_865, vertices_118, vertices_150, vertices_358, vertices_390, vertices_186, vertices_668, vertices_852, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_137, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_641, vertices_769, vertices_22, vertices_102, vertices_134, vertices_262, vertices_50, vertices_146, vertices_162, vertices_290, vertices_386, vertices_84, vertices_148, vertices_532, vertices_324, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_536, vertices_168, vertices_584, vertices_648, vertices_112, vertices_592, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_901), (false, vertices_121), (false, vertices_169), (false, vertices_713), (false, vertices_865), (true, vertices_22), (true, vertices_102), (true, vertices_134), (true, vertices_262), (true, vertices_50), (true, vertices_146), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_324), (true, vertices_152), (true, vertices_536), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 14 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_865) then 23 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_102) then 15 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_592) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 5 7 8 852 84 3
cert_row_2 1 0 1 4 5 102
cert_row_4 2 0 2 3 4 6 186 50 1
cert_row_4 3 1 2 3 6 8 668 148 1
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 1 0 1 3 4 22 118 3
cert_coverFacet 1 150
cert_cover_2 1 1 0 3 6 22 150 3
cert_coverFacet 2 358
cert_cover_5 2 1 0 1 4 7 102 358 3
cert_coverFacet 3 390
cert_cover_2 3 1 0 6 7 134 390 3
cert_coverFacet 4 186
cert_cover_5 4 2 0 2 3 4 50 186 1
cert_coverFacet 5 668
cert_cover_5 5 3 1 2 3 6 148 668 1
cert_coverFacet 6 852
cert_cover_5 6 0 1 3 5 7 84 852 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0562

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m14e10q1_0563.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0563

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 299, 899, 45, 525, 709, 793, 738, 866, 92, 540, 236, 852, 376, 35, 131, 259, 13, 37, 133, 517, 41, 265, 521, 641, 769, 610, 162, 290, 642, 770, 28, 44, 76, 524, 84, 532, 164, 196, 580, 88, 280, 536, 104, 296, 336, 784, 224, 352, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_299, vertices_899, vertices_45, vertices_525, vertices_709, vertices_793, vertices_738, vertices_866, vertices_92, vertices_540, vertices_236, vertices_852, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_13, vertices_37, vertices_133, vertices_517, vertices_41, vertices_265, vertices_521, vertices_641, vertices_769, vertices_610, vertices_162, vertices_290, vertices_642, vertices_770, vertices_28, vertices_44, vertices_76, vertices_524, vertices_84, vertices_532, vertices_164, vertices_196, vertices_580, vertices_88, vertices_280, vertices_536, vertices_104, vertices_296, vertices_336, vertices_784, vertices_224, vertices_352, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_299), (false, vertices_899), (false, vertices_45), (false, vertices_525), (false, vertices_709), (false, vertices_793), (true, vertices_610), (true, vertices_28), (true, vertices_76), (true, vertices_84), (true, vertices_532), (true, vertices_88), (true, vertices_104), (true, vertices_336), (true, vertices_224), (true, vertices_352), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 13 else
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_45) then 0 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_709) then 14 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (true, vertices_610) then 18 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_167), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_610), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 5 8 610
cert_row_4 1 1 2 4 5 6 236 44 3
cert_row_4 2 1 3 5 7 8 852 84 3
cert_row_4 3 2 3 4 5 7 376 88 2
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 738
cert_cover_5 0 0 0 4 5 6 610 738 3
cert_coverFacet 1 866
cert_cover_5 1 0 0 4 5 7 610 866 3
cert_coverFacet 2 92
cert_cover_2 2 2 1 3 5 28 92 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 236
cert_cover_5 4 1 1 2 4 5 44 236 3
cert_coverFacet 5 852
cert_cover_5 5 2 1 3 5 7 84 852 3
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 88 376 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0563

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m14e10q1_0564.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0564

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 531, 291, 835, 661, 361, 737, 542, 314, 778, 124, 716, 244, 840, 19, 35, 259, 515, 145, 529, 97, 161, 289, 321, 577, 641, 26, 266, 522, 50, 530, 290, 770, 28, 76, 524, 116, 148, 532, 196, 644, 56, 104, 296, 328, 584, 776, 176, 224, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_531, vertices_291, vertices_835, vertices_661, vertices_361, vertices_737, vertices_542, vertices_314, vertices_778, vertices_124, vertices_716, vertices_244, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_515, vertices_145, vertices_529, vertices_97, vertices_161, vertices_289, vertices_321, vertices_577, vertices_641, vertices_26, vertices_266, vertices_522, vertices_50, vertices_530, vertices_290, vertices_770, vertices_28, vertices_76, vertices_524, vertices_116, vertices_148, vertices_532, vertices_196, vertices_644, vertices_56, vertices_104, vertices_296, vertices_328, vertices_584, vertices_776, vertices_176, vertices_224, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_531), (false, vertices_291), (false, vertices_835), (false, vertices_661), (false, vertices_361), (false, vertices_737), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_28), (true, vertices_76), (true, vertices_524), (true, vertices_116), (true, vertices_196), (true, vertices_56), (true, vertices_584), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 13 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_291) then 1 else
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_661) then 16 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_737) then 22 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_116) then 17 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_776) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_116), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 7 314 26 3
cert_row_2 1 1 3 4 5 116
cert_row_4 2 0 1 2 3 8 542 26 1
cert_row_4 3 1 2 5 6 8 716 76 3
cert_rows
cert_pivot_2 7 4 0 1
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 2 0 1 2 3 26 542 1
cert_coverFacet 1 314
cert_cover_5 1 0 0 2 3 4 26 314 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 124
cert_cover_5 3 1 1 2 3 4 28 124 3
cert_coverFacet 4 716
cert_cover_5 4 3 1 2 5 6 76 716 3
cert_coverFacet 5 244
cert_cover_5 5 1 1 3 4 6 116 244 3
cert_coverFacet 6 840
cert_cover_2 6 5 2 7 8 328 840 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0564

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m14e10q1_0565.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0565

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 397, 789, 677, 713, 849, 422, 618, 394, 650, 370, 674, 628, 308, 133, 261, 517, 73, 137, 265, 785, 321, 577, 641, 74, 138, 266, 522, 98, 162, 290, 546, 322, 386, 642, 52, 276, 532, 164, 292, 548, 388, 584, 392, 648, 112, 304, 336, 592, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_397, vertices_789, vertices_677, vertices_713, vertices_849, vertices_422, vertices_618, vertices_394, vertices_650, vertices_370, vertices_674, vertices_628, vertices_308] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_785, vertices_321, vertices_577, vertices_641, vertices_74, vertices_138, vertices_266, vertices_522, vertices_98, vertices_162, vertices_290, vertices_546, vertices_322, vertices_386, vertices_642, vertices_52, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_584, vertices_392, vertices_648, vertices_112, vertices_304, vertices_336, vertices_592, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_397), (false, vertices_789), (false, vertices_677), (false, vertices_713), (false, vertices_849), (true, vertices_138), (true, vertices_522), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_52), (true, vertices_292), (true, vertices_112), (true, vertices_304), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_397) then 16 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 7 422 162 1
cert_row_4 1 0 2 4 5 8 618 74 2
cert_row_4 2 0 3 4 5 7 370 98 1
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 162 422 1
cert_coverFacet 1 618
cert_cover_5 1 1 0 2 4 5 74 618 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 370
cert_cover_5 4 2 0 3 4 5 98 370 1
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 628
cert_cover_5 6 3 1 3 4 5 52 628 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0565

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m14e10q1_0566.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0566

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 301, 677, 837, 313, 625, 902, 410, 210, 738, 834, 188, 396, 240, 37, 261, 517, 297, 49, 81, 273, 545, 321, 577, 82, 146, 274, 194, 322, 578, 386, 642, 770, 44, 140, 268, 164, 388, 644, 772, 56, 152, 280, 392, 112, 176, 208, 224, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_301, vertices_677, vertices_837, vertices_313, vertices_625, vertices_902, vertices_410, vertices_210, vertices_738, vertices_834, vertices_188, vertices_396, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_297, vertices_49, vertices_81, vertices_273, vertices_545, vertices_321, vertices_577, vertices_82, vertices_146, vertices_274, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_268, vertices_164, vertices_388, vertices_644, vertices_772, vertices_56, vertices_152, vertices_280, vertices_392, vertices_112, vertices_176, vertices_208, vertices_224, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_301), (false, vertices_677), (false, vertices_837), (false, vertices_313), (false, vertices_625), (true, vertices_146), (true, vertices_194), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_140), (true, vertices_388), (true, vertices_152), (true, vertices_392), (true, vertices_176), (true, vertices_208), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 14 else
  if p.val = (false, vertices_301) then 19 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_313) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_224) then 12 else
  0
cert_priority
cert_nodeAtPriority_12 146 1 194 2 578 386 642 770 140 388 152 392 176 208 224 339 677 837 301 313 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 6 8 738 194 1
cert_row_4 1 0 1 6 7 8 902 386 1
cert_row_4 2 0 2 3 6 7 410 146 1
cert_row_4 3 1 2 3 4 6 188 44 2
cert_rows
cert_pivot_2 5 8 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 410
cert_cover_5 1 2 0 2 3 6 146 410 1
cert_coverFacet 2 210
cert_cover_2 2 3 0 5 6 82 210 3
cert_coverFacet 3 738
cert_cover_5 3 0 0 4 5 6 194 738 1
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 188
cert_cover_5 5 3 1 2 3 4 44 188 2
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0566

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m14e10q1_0567.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0567

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 899, 405, 345, 665, 617, 422, 362, 738, 284, 540, 300, 556, 692, 771, 25, 73, 521, 145, 273, 321, 577, 385, 641, 98, 162, 290, 322, 578, 386, 642, 28, 44, 268, 524, 148, 276, 532, 164, 292, 548, 388, 280, 536, 104, 296, 552, 328, 656, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_899, vertices_405, vertices_345, vertices_665, vertices_617, vertices_422, vertices_362, vertices_738, vertices_284, vertices_540, vertices_300, vertices_556, vertices_692] (by decide +kernel)
  polygons := literalFinset [vertices_771, vertices_25, vertices_73, vertices_521, vertices_145, vertices_273, vertices_321, vertices_577, vertices_385, vertices_641, vertices_98, vertices_162, vertices_290, vertices_322, vertices_578, vertices_386, vertices_642, vertices_28, vertices_44, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_328, vertices_656, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_899), (false, vertices_405), (false, vertices_345), (false, vertices_665), (false, vertices_617), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_532), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_296), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 7 362 98 1
cert_row_4 1 0 1 4 6 7 422 162 1
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 1 3 4 6 8 692 148 2
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 1 0 1 4 6 162 422 1
cert_coverFacet 1 362
cert_cover_5 1 0 0 2 4 5 98 362 1
cert_coverFacet 2 738
cert_cover_5 2 2 0 4 5 6 98 738 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 692
cert_cover_5 7 3 1 3 4 6 148 692 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0567

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m14e10q1_0568.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0568

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 557, 613, 185, 369, 721, 782, 394, 434, 658, 786, 364, 852, 424, 549, 41, 137, 521, 49, 81, 145, 97, 577, 641, 138, 266, 522, 146, 274, 530, 386, 642, 770, 44, 268, 524, 100, 324, 580, 772, 168, 296, 392, 176, 304, 336, 592, 656, 784, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_557, vertices_613, vertices_185, vertices_369, vertices_721, vertices_782, vertices_394, vertices_434, vertices_658, vertices_786, vertices_364, vertices_852, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_549, vertices_41, vertices_137, vertices_521, vertices_49, vertices_81, vertices_145, vertices_97, vertices_577, vertices_641, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_524, vertices_100, vertices_324, vertices_580, vertices_772, vertices_168, vertices_296, vertices_392, vertices_176, vertices_304, vertices_336, vertices_592, vertices_656, vertices_784, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_557), (false, vertices_613), (false, vertices_185), (false, vertices_369), (false, vertices_721), (true, vertices_266), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_770), (true, vertices_268), (true, vertices_324), (true, vertices_772), (true, vertices_296), (true, vertices_392), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_557) then 16 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_185) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 7 434 146 2
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 1 2 4 5 7 364 44 3
cert_row_4 3 1 3 5 7 8 852 324 1
cert_rows
cert_pivot_2 6 0 2 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 434
cert_cover_5 2 0 0 3 4 6 146 434 2
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 364
cert_cover_5 5 2 1 2 4 5 44 364 3
cert_coverFacet 6 852
cert_cover_5 6 3 1 3 5 7 324 852 1
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0568

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m14e10q1_0575.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0575

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 535, 275, 525, 665, 457, 433, 358, 614, 690, 306, 716, 332, 992, 7, 19, 259, 13, 517, 137, 265, 521, 145, 273, 529, 385, 102, 262, 518, 50, 274, 530, 290, 546, 76, 268, 524, 324, 580, 200, 328, 648, 176, 304, 656, 352, 608, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_535, vertices_275, vertices_525, vertices_665, vertices_457, vertices_433, vertices_358, vertices_614, vertices_690, vertices_306, vertices_716, vertices_332, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_19, vertices_259, vertices_13, vertices_517, vertices_137, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_385, vertices_102, vertices_262, vertices_518, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_76, vertices_268, vertices_524, vertices_324, vertices_580, vertices_200, vertices_328, vertices_648, vertices_176, vertices_304, vertices_656, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_535), (false, vertices_275), (false, vertices_525), (false, vertices_665), (false, vertices_457), (false, vertices_433), (true, vertices_102), (true, vertices_50), (true, vertices_290), (true, vertices_546), (true, vertices_76), (true, vertices_324), (true, vertices_580), (true, vertices_352), (true, vertices_608), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 12 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 13 else
  if p.val = (false, vertices_535) then 17 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_665) then 14 else
  if p.val = (false, vertices_457) then 15 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (true, vertices_102) then 18 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_704) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 19 => Sum.inl 1
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
cert_row_4 0 0 3 4 6 8 690 50 3
cert_row_2 1 0 1 4 5 102
cert_row_4 2 1 2 5 6 8 716 76 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 3 0 1 4
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 1 0 1 4 7 102 358 3
cert_coverFacet 1 614
cert_cover_5 1 1 0 1 4 8 102 614 3
cert_coverFacet 2 690
cert_cover_5 2 0 0 3 4 6 50 690 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 716
cert_cover_5 4 2 1 2 5 6 76 716 3
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 352 992 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0575

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m14e10q1_0576.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0576

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 155, 307, 803, 405, 837, 58, 618, 650, 716, 452, 248, 880, 464, 19, 291, 131, 515, 133, 261, 517, 145, 273, 769, 26, 42, 138, 522, 50, 546, 642, 196, 324, 580, 388, 644, 56, 152, 104, 200, 584, 648, 112, 304, 208, 336, 400, 608, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_155, vertices_307, vertices_803, vertices_405, vertices_837, vertices_58, vertices_618, vertices_650, vertices_716, vertices_452, vertices_248, vertices_880, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_291, vertices_131, vertices_515, vertices_133, vertices_261, vertices_517, vertices_145, vertices_273, vertices_769, vertices_26, vertices_42, vertices_138, vertices_522, vertices_50, vertices_546, vertices_642, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_56, vertices_152, vertices_104, vertices_200, vertices_584, vertices_648, vertices_112, vertices_304, vertices_208, vertices_336, vertices_400, vertices_608, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_155), (false, vertices_307), (false, vertices_803), (false, vertices_405), (false, vertices_837), (true, vertices_42), (true, vertices_522), (true, vertices_196), (true, vertices_56), (true, vertices_104), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_112), (true, vertices_208), (true, vertices_336), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 13 21 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_155) then 18 else
  if p.val = (false, vertices_307) then 19 else
  if p.val = (false, vertices_803) then 20 else
  if p.val = (false, vertices_405) then 15 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_196) then 2 else
  if p.val = (true, vertices_56) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
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
cert_row_4 0 0 2 4 5 8 618 42 3
cert_row_4 1 1 2 5 6 8 716 196 1
cert_row_4 2 2 3 4 5 6 248 56 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 58
cert_cover_2 0 2 0 3 4 26 58 3
cert_coverFacet 1 618
cert_cover_5 1 0 0 2 4 5 42 618 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 716
cert_cover_5 3 1 1 2 5 6 196 716 1
cert_coverFacet 4 452
cert_cover_2 4 5 1 6 7 196 452 3
cert_coverFacet 5 248
cert_cover_5 5 2 2 3 4 5 56 248 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0576

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m14e10q1_0577.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0577

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [143, 527, 211, 835, 805, 453, 154, 538, 626, 572, 172, 420, 248, 992, 15, 67, 131, 515, 133, 261, 517, 193, 321, 769, 26, 138, 522, 82, 146, 530, 578, 44, 140, 524, 164, 292, 548, 388, 56, 152, 536, 168, 112, 560, 208, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_143, vertices_527, vertices_211, vertices_835, vertices_805, vertices_453, vertices_154, vertices_538, vertices_626, vertices_572, vertices_172, vertices_420, vertices_248, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_15, vertices_67, vertices_131, vertices_515, vertices_133, vertices_261, vertices_517, vertices_193, vertices_321, vertices_769, vertices_26, vertices_138, vertices_522, vertices_82, vertices_146, vertices_530, vertices_578, vertices_44, vertices_140, vertices_524, vertices_164, vertices_292, vertices_548, vertices_388, vertices_56, vertices_152, vertices_536, vertices_168, vertices_112, vertices_560, vertices_208, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_143), (false, vertices_527), (false, vertices_211), (false, vertices_835), (false, vertices_805), (false, vertices_453), (true, vertices_26), (true, vertices_530), (true, vertices_44), (true, vertices_164), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_168), (true, vertices_112), (true, vertices_560), (true, vertices_224), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 13 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_143) then 14 else
  if p.val = (false, vertices_527) then 15 else
  if p.val = (false, vertices_211) then 17 else
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_56) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_143), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 8 626 82 2
cert_row_4 1 1 2 3 4 8 572 44 2
cert_row_4 2 2 3 4 5 6 248 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 154
cert_cover_2 0 2 0 3 6 26 154 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 626
cert_cover_5 2 0 0 3 4 5 82 626 2
cert_coverFacet 3 572
cert_cover_5 3 1 1 2 3 4 44 572 2
cert_coverFacet 4 172
cert_cover_2 4 2 1 4 6 44 172 3
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 248
cert_cover_5 6 2 2 3 4 5 56 248 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0577

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2403 : Certifies 2403 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0511.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2404 : Certifies 2404 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0512.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2405 : Certifies 2405 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0515.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2406 : Certifies 2406 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0518.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2407 : Certifies 2407 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0519.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2408 : Certifies 2408 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0520.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2409 : Certifies 2409 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0523.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2410 : Certifies 2410 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0524.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2411 : Certifies 2411 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0525.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2412 : Certifies 2412 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0526.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2413 : Certifies 2413 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0527.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2414 : Certifies 2414 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0528.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2415 : Certifies 2415 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0533.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2416 : Certifies 2416 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0535.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2417 : Certifies 2417 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0539.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2418 : Certifies 2418 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0540.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2419 : Certifies 2419 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0542.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2420 : Certifies 2420 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0545.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2421 : Certifies 2421 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0554.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2422 : Certifies 2422 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0555.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2423 : Certifies 2423 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0562.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2424 : Certifies 2424 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0563.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2425 : Certifies 2425 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0564.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2426 : Certifies 2426 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0565.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2427 : Certifies 2427 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0566.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2428 : Certifies 2428 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0567.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2429 : Certifies 2429 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0568.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2430 : Certifies 2430 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0575.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2431 : Certifies 2431 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0576.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2432 : Certifies 2432 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0577.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B079 (j : Fin 30) :
    Certifies (2403 + j.val) := by
  fin_cases j
  · exact projection_2403
  · exact projection_2404
  · exact projection_2405
  · exact projection_2406
  · exact projection_2407
  · exact projection_2408
  · exact projection_2409
  · exact projection_2410
  · exact projection_2411
  · exact projection_2412
  · exact projection_2413
  · exact projection_2414
  · exact projection_2415
  · exact projection_2416
  · exact projection_2417
  · exact projection_2418
  · exact projection_2419
  · exact projection_2420
  · exact projection_2421
  · exact projection_2422
  · exact projection_2423
  · exact projection_2424
  · exact projection_2425
  · exact projection_2426
  · exact projection_2427
  · exact projection_2428
  · exact projection_2429
  · exact projection_2430
  · exact projection_2431
  · exact projection_2432

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
