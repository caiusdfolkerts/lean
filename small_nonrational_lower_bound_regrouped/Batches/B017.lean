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
/- Source: ProjectionCertificates/R_m15e10q1_1242.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1242

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 397, 677, 837, 665, 785, 614, 602, 426, 682, 114, 306, 372, 420, 848, 133, 261, 517, 25, 137, 265, 273, 529, 641, 769, 26, 170, 266, 522, 50, 82, 274, 98, 290, 546, 578, 100, 164, 292, 548, 324, 580, 388, 536, 392, 648, 112, 304, 336, 592, 784, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_397, vertices_677, vertices_837, vertices_665, vertices_785, vertices_614, vertices_602, vertices_426, vertices_682, vertices_114, vertices_306, vertices_372, vertices_420, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_137, vertices_265, vertices_273, vertices_529, vertices_641, vertices_769, vertices_26, vertices_170, vertices_266, vertices_522, vertices_50, vertices_82, vertices_274, vertices_98, vertices_290, vertices_546, vertices_578, vertices_100, vertices_164, vertices_292, vertices_548, vertices_324, vertices_580, vertices_388, vertices_536, vertices_392, vertices_648, vertices_112, vertices_304, vertices_336, vertices_592, vertices_784, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_397), (false, vertices_677), (false, vertices_837), (false, vertices_665), (false, vertices_785), (true, vertices_170), (true, vertices_522), (true, vertices_50), (true, vertices_82), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_578), (true, vertices_100), (true, vertices_292), (true, vertices_112), (true, vertices_304), (true, vertices_336), (true, vertices_592), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 16 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_665) then 23 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (true, vertices_170) then 17 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_51 785 522 50 82 98 290 546 578 100 292 112 304 336 592 416 283 170 397 677 837 665
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 6 170
cert_row_4 1 0 2 3 5 8 602 26 3
cert_row_4 2 0 1 4 5 8 614 98 1
cert_row_4 3 1 3 4 5 7 372 100 1
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 2 0 1 4 5 98 614 1
cert_coverFacet 1 602
cert_cover_5 1 1 0 2 3 5 26 602 3
cert_coverFacet 2 426
cert_cover_5 2 0 0 2 4 7 170 426 3
cert_coverFacet 3 682
cert_cover_5 3 0 0 2 4 8 170 682 3
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 306
cert_cover_2 5 3 0 4 7 50 306 3
cert_coverFacet 6 372
cert_cover_5 6 3 1 3 4 5 100 372 1
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coverFacet 8 848
cert_cover_2 8 5 3 7 8 336 848 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1242

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_1247.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1247

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 397, 345, 665, 625, 897, 654, 614, 166, 370, 418, 898, 316, 572, 420, 25, 137, 265, 81, 529, 321, 577, 385, 641, 769, 38, 134, 518, 98, 162, 290, 322, 578, 386, 642, 770, 60, 140, 268, 524, 164, 292, 548, 388, 280, 536, 648, 112, 304, 560, 336, 608, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_397, vertices_345, vertices_665, vertices_625, vertices_897, vertices_654, vertices_614, vertices_166, vertices_370, vertices_418, vertices_898, vertices_316, vertices_572, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_81, vertices_529, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_38, vertices_134, vertices_518, vertices_98, vertices_162, vertices_290, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_60, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_388, vertices_280, vertices_536, vertices_648, vertices_112, vertices_304, vertices_560, vertices_336, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_397), (false, vertices_345), (false, vertices_665), (false, vertices_625), (false, vertices_897), (true, vertices_38), (true, vertices_134), (true, vertices_518), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_642), (true, vertices_60), (true, vertices_524), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_304), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_60) then 19 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_548) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 897 2 38 1 134 3 518 98 162 290 386 642 524 164 292 548 304 416 835 397 60 345 665 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 134 2
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 1 4 5 8 614 38 3
cert_row_4 3 0 3 4 5 7 370 98 1
cert_rows
cert_pivot_2 6 2 1 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 134 654 2
cert_coverFacet 1 614
cert_cover_5 1 2 0 1 4 5 38 614 3
cert_coverFacet 2 166
cert_cover_2 2 1 0 4 6 38 166 3
cert_coverFacet 3 370
cert_cover_5 3 3 0 3 4 5 98 370 1
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 316
cert_cover_5 6 1 1 2 3 7 60 316 3
cert_coverFacet 7 572
cert_cover_5 7 1 1 2 3 8 60 572 3
cert_coverFacet 8 420
cert_cover_2 8 4 1 6 7 164 420 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1247

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_1248.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1248

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 397, 357, 677, 849, 897, 302, 558, 602, 410, 114, 306, 668, 368, 912, 37, 133, 261, 97, 545, 321, 577, 385, 641, 769, 46, 26, 266, 522, 50, 82, 274, 98, 290, 546, 578, 140, 268, 524, 292, 548, 644, 152, 536, 392, 112, 304, 336, 592, 400, 656, 784, 352, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_397, vertices_357, vertices_677, vertices_849, vertices_897, vertices_302, vertices_558, vertices_602, vertices_410, vertices_114, vertices_306, vertices_668, vertices_368, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_97, vertices_545, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_46, vertices_26, vertices_266, vertices_522, vertices_50, vertices_82, vertices_274, vertices_98, vertices_290, vertices_546, vertices_578, vertices_140, vertices_268, vertices_524, vertices_292, vertices_548, vertices_644, vertices_152, vertices_536, vertices_392, vertices_112, vertices_304, vertices_336, vertices_592, vertices_400, vertices_656, vertices_784, vertices_352, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_397), (false, vertices_357), (false, vertices_677), (false, vertices_849), (false, vertices_897), (true, vertices_46), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_290), (true, vertices_524), (true, vertices_152), (true, vertices_536), (true, vertices_112), (true, vertices_304), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_46) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
cert_nodeAtPriority_19 0 897 1 26 266 522 50 82 274 290 524 152 536 112 304 400 656 611 46 397 357 677 849
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 2 3 5 8 602 26 3
cert_row_4 2 0 2 3 6 7 410 26 3
cert_row_4 3 1 2 3 6 8 668 140 2
cert_rows
cert_pivot_2 4 5 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 7 46 302 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 8 46 558 3
cert_coverFacet 2 602
cert_cover_5 2 1 0 2 3 5 26 602 3
cert_coverFacet 3 410
cert_cover_5 3 2 0 2 3 6 26 410 3
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 306
cert_cover_2 5 3 0 4 7 50 306 3
cert_coverFacet 6 668
cert_cover_5 6 3 1 2 3 6 140 668 2
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coverFacet 8 912
cert_cover_2 8 6 3 7 8 400 912 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1248

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_1250.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1250

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 527, 341, 661, 601, 361, 406, 678, 618, 170, 394, 424, 464, 720, 992, 15, 21, 261, 517, 73, 265, 521, 81, 529, 321, 134, 262, 518, 42, 138, 266, 522, 162, 546, 386, 148, 276, 644, 104, 168, 296, 584, 392, 208, 336, 592, 400, 656, 352, 608, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_527, vertices_341, vertices_661, vertices_601, vertices_361, vertices_406, vertices_678, vertices_618, vertices_170, vertices_394, vertices_424, vertices_464, vertices_720, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_15, vertices_21, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_81, vertices_529, vertices_321, vertices_134, vertices_262, vertices_518, vertices_42, vertices_138, vertices_266, vertices_522, vertices_162, vertices_546, vertices_386, vertices_148, vertices_276, vertices_644, vertices_104, vertices_168, vertices_296, vertices_584, vertices_392, vertices_208, vertices_336, vertices_592, vertices_400, vertices_656, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_527), (false, vertices_341), (false, vertices_661), (false, vertices_601), (false, vertices_361), (true, vertices_134), (true, vertices_42), (true, vertices_138), (true, vertices_162), (true, vertices_546), (true, vertices_386), (true, vertices_168), (true, vertices_392), (true, vertices_208), (true, vertices_400), (true, vertices_608), (true, vertices_416), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 16 else
  if p.val = (false, vertices_527) then 17 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_661) then 20 else
  if p.val = (false, vertices_601) then 22 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_448) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 7 406 134 2
cert_row_4 1 0 1 4 6 8 678 134 2
cert_row_4 2 0 2 4 5 8 618 42 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 3 1 0 4
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 134 406 2
cert_coverFacet 1 678
cert_cover_5 1 1 0 1 4 6 134 678 2
cert_coverFacet 2 618
cert_cover_5 2 2 0 2 4 5 42 618 3
cert_coverFacet 3 170
cert_cover_2 3 2 0 4 6 42 170 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 424
cert_cover_2 5 4 2 6 7 168 424 3
cert_coverFacet 6 464
cert_cover_2 6 5 3 6 7 208 464 3
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coverFacet 8 992
cert_cover_5 8 3 4 5 6 7 352 992 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1250

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e11q2_0007.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0007

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 583, 653, 421, 689, 865, 158, 526, 406, 346, 618, 120, 568, 664, 496, 71, 133, 261, 517, 161, 289, 545, 321, 577, 641, 14, 150, 262, 518, 26, 74, 522, 274, 322, 578, 140, 524, 388, 56, 88, 152, 536, 104, 552, 648, 112, 176, 560, 336, 400, 656, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_583, vertices_653, vertices_421, vertices_689, vertices_865, vertices_158, vertices_526, vertices_406, vertices_346, vertices_618, vertices_120, vertices_568, vertices_664, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_71, vertices_133, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_641, vertices_14, vertices_150, vertices_262, vertices_518, vertices_26, vertices_74, vertices_522, vertices_274, vertices_322, vertices_578, vertices_140, vertices_524, vertices_388, vertices_56, vertices_88, vertices_152, vertices_536, vertices_104, vertices_552, vertices_648, vertices_112, vertices_176, vertices_560, vertices_336, vertices_400, vertices_656, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_583), (false, vertices_653), (false, vertices_421), (false, vertices_689), (false, vertices_865), (true, vertices_14), (true, vertices_150), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_274), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_104), (true, vertices_552), (true, vertices_112), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 22 14 16 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 20 else
  if p.val = (false, vertices_583) then 21 else
  if p.val = (false, vertices_653) then 15 else
  if p.val = (false, vertices_421) then 23 else
  if p.val = (false, vertices_689) then 17 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_150) then 18 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_150), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 6 150
cert_row_4 1 0 2 4 5 8 618 74 2
cert_row_4 2 0 2 3 5 7 346 26 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 8 0 3
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 14 158 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 406
cert_cover_5 2 0 0 1 3 7 150 406 3
cert_coverFacet 3 346
cert_cover_5 3 2 0 2 3 5 26 346 3
cert_coverFacet 4 618
cert_cover_5 4 1 0 2 4 5 74 618 2
cert_coverFacet 5 120
cert_cover_2 5 3 2 4 5 56 120 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0007

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e11q2_0014.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0014

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 653, 121, 153, 585, 433, 961, 310, 566, 454, 710, 618, 412, 540, 568, 25, 73, 137, 521, 49, 145, 97, 289, 321, 577, 385, 641, 54, 198, 262, 518, 98, 290, 546, 322, 578, 28, 140, 524, 276, 532, 388, 644, 56, 152, 536, 104, 552, 584, 304, 560, 400, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_653, vertices_121, vertices_153, vertices_585, vertices_433, vertices_961, vertices_310, vertices_566, vertices_454, vertices_710, vertices_618, vertices_412, vertices_540, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_137, vertices_521, vertices_49, vertices_145, vertices_97, vertices_289, vertices_321, vertices_577, vertices_385, vertices_641, vertices_54, vertices_198, vertices_262, vertices_518, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_28, vertices_140, vertices_524, vertices_276, vertices_532, vertices_388, vertices_644, vertices_56, vertices_152, vertices_536, vertices_104, vertices_552, vertices_584, vertices_304, vertices_560, vertices_400, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_653), (false, vertices_121), (false, vertices_153), (false, vertices_585), (false, vertices_433), (false, vertices_961), (true, vertices_54), (true, vertices_198), (true, vertices_262), (true, vertices_518), (true, vertices_546), (true, vertices_578), (true, vertices_28), (true, vertices_276), (true, vertices_532), (true, vertices_388), (true, vertices_536), (true, vertices_552), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 22 13 16 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 20 else
  if p.val = (false, vertices_653) then 14 else
  if p.val = (false, vertices_121) then 15 else
  if p.val = (false, vertices_153) then 0 else
  if p.val = (false, vertices_585) then 1 else
  if p.val = (false, vertices_433) then 17 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_54) then 18 else
  if p.val = (true, vertices_198) then 21 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_560) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_153), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_198), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 8 618 98 1
cert_row_2 1 0 1 5 6 198
cert_row_2 2 0 1 3 4 54
cert_row_4 3 1 2 3 6 7 412 28 3
cert_rows
cert_pivot_2 8 5 0 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 2 0 1 3 7 54 310 3
cert_coverFacet 1 566
cert_cover_5 1 2 0 1 3 8 54 566 3
cert_coverFacet 2 454
cert_cover_5 2 1 0 1 5 7 198 454 3
cert_coverFacet 3 710
cert_cover_5 3 1 0 1 5 8 198 710 3
cert_coverFacet 4 618
cert_cover_5 4 0 0 2 4 5 98 618 1
cert_coverFacet 5 412
cert_cover_5 5 3 1 2 3 6 28 412 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0014

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e11q2_0020.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0020

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 211, 595, 419, 589, 453, 186, 306, 786, 572, 364, 804, 728, 488, 816, 83, 131, 259, 515, 69, 261, 517, 193, 577, 385, 50, 146, 274, 530, 162, 290, 770, 44, 76, 524, 292, 548, 324, 772, 56, 152, 536, 360, 168, 200, 584, 304, 560, 208, 592, 784, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_211, vertices_595, vertices_419, vertices_589, vertices_453, vertices_186, vertices_306, vertices_786, vertices_572, vertices_364, vertices_804, vertices_728, vertices_488, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_83, vertices_131, vertices_259, vertices_515, vertices_69, vertices_261, vertices_517, vertices_193, vertices_577, vertices_385, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_770, vertices_44, vertices_76, vertices_524, vertices_292, vertices_548, vertices_324, vertices_772, vertices_56, vertices_152, vertices_536, vertices_360, vertices_168, vertices_200, vertices_584, vertices_304, vertices_560, vertices_208, vertices_592, vertices_784, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_211), (false, vertices_595), (false, vertices_419), (false, vertices_589), (false, vertices_453), (true, vertices_50), (true, vertices_274), (true, vertices_44), (true, vertices_292), (true, vertices_548), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_360), (true, vertices_168), (true, vertices_200), (true, vertices_304), (true, vertices_560), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 14 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_211) then 19 else
  if p.val = (false, vertices_595) then 20 else
  if p.val = (false, vertices_419) then 21 else
  if p.val = (false, vertices_589) then 16 else
  if p.val = (false, vertices_453) then 17 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_360) then 23 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(true, vertices_360), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 5 7 360
cert_row_4 1 0 2 3 4 6 186 50 1
cert_row_4 2 1 2 3 4 8 572 44 2
cert_row_4 3 2 3 5 6 8 728 152 2
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 186
cert_cover_5 0 1 0 2 3 4 50 186 1
cert_coverFacet 1 306
cert_cover_2 1 3 0 4 7 50 306 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 572
cert_cover_5 3 2 1 2 3 4 44 572 2
cert_coverFacet 4 364
cert_cover_5 4 0 1 2 4 5 44 364 3
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coverFacet 6 728
cert_cover_5 6 3 2 3 5 6 152 728 2
cert_coverFacet 7 488
cert_cover_5 7 0 2 4 5 6 360 488 3
cert_coverFacet 8 816
cert_cover_2 8 4 3 7 8 304 816 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0020

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e11q2_0037.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0037

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 583, 653, 421, 369, 737, 158, 526, 406, 346, 618, 120, 568, 664, 944, 71, 133, 261, 517, 97, 161, 289, 321, 577, 641, 14, 150, 262, 518, 26, 74, 522, 274, 322, 578, 140, 524, 388, 56, 88, 152, 536, 104, 552, 648, 112, 304, 560, 336, 400, 656, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_583, vertices_653, vertices_421, vertices_369, vertices_737, vertices_158, vertices_526, vertices_406, vertices_346, vertices_618, vertices_120, vertices_568, vertices_664, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_71, vertices_133, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_321, vertices_577, vertices_641, vertices_14, vertices_150, vertices_262, vertices_518, vertices_26, vertices_74, vertices_522, vertices_274, vertices_322, vertices_578, vertices_140, vertices_524, vertices_388, vertices_56, vertices_88, vertices_152, vertices_536, vertices_104, vertices_552, vertices_648, vertices_112, vertices_304, vertices_560, vertices_336, vertices_400, vertices_656, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_583), (false, vertices_653), (false, vertices_421), (false, vertices_369), (false, vertices_737), (true, vertices_14), (true, vertices_150), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_274), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_104), (true, vertices_552), (true, vertices_560), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 22 14 16 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 20 else
  if p.val = (false, vertices_583) then 21 else
  if p.val = (false, vertices_653) then 15 else
  if p.val = (false, vertices_421) then 23 else
  if p.val = (false, vertices_369) then 17 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_150) then 18 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_656) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_150), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 6 150
cert_row_4 1 3 4 6 7 8 944 304 2
cert_row_4 2 0 2 3 5 7 346 26 3
cert_row_4 3 0 2 4 5 8 618 74 2
cert_rows
cert_pivot_2 1 6 3 0
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 14 158 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 406
cert_cover_5 2 0 0 1 3 7 150 406 3
cert_coverFacet 3 346
cert_cover_5 3 2 0 2 3 5 26 346 3
cert_coverFacet 4 618
cert_cover_5 4 3 0 2 4 5 74 618 2
cert_coverFacet 5 120
cert_cover_2 5 3 2 4 5 56 120 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coverFacet 8 944
cert_cover_5 8 1 3 4 6 7 304 944 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0037

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e11q2_0075.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0075

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 677, 665, 433, 849, 110, 558, 602, 482, 834, 348, 412, 652, 228, 452, 145, 273, 529, 161, 289, 545, 641, 769, 46, 74, 522, 98, 290, 546, 322, 578, 770, 284, 76, 140, 524, 100, 164, 548, 196, 324, 388, 644, 88, 152, 536, 648, 336, 592, 400, 224, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_677, vertices_665, vertices_433, vertices_849, vertices_110, vertices_558, vertices_602, vertices_482, vertices_834, vertices_348, vertices_412, vertices_652, vertices_228, vertices_452] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_46, vertices_74, vertices_522, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_284, vertices_76, vertices_140, vertices_524, vertices_100, vertices_164, vertices_548, vertices_196, vertices_324, vertices_388, vertices_644, vertices_88, vertices_152, vertices_536, vertices_648, vertices_336, vertices_592, vertices_400, vertices_224, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_677), (false, vertices_665), (false, vertices_433), (false, vertices_849), (true, vertices_46), (true, vertices_74), (true, vertices_522), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_284), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_100), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_88), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_849) then 25 else
  if p.val = (true, vertices_46) then 17 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_284) then 20 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_284), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 74 2
cert_row_2 1 1 2 3 7 284
cert_row_2 2 0 1 2 4 46
cert_row_4 3 0 4 5 6 7 482 98 3
cert_rows
cert_pivot_2 8 3 1 0
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 2 0 1 2 5 46 110 3
cert_coverFacet 1 558
cert_cover_5 1 2 0 1 2 8 46 558 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 5 74 602 2
cert_coverFacet 3 482
cert_cover_5 3 3 0 4 5 6 98 482 3
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 348
cert_cover_5 5 1 1 2 3 5 284 348 3
cert_coverFacet 6 412
cert_cover_5 6 1 1 2 3 6 284 412 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 228
cert_cover_2 8 4 1 5 6 100 228 3
cert_coverFacet 9 452
cert_cover_2 9 5 1 6 7 196 452 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0075

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0028.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0028

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 157, 565, 453, 773, 241, 801, 334, 794, 714, 738, 802, 284, 204, 788, 696, 21, 133, 261, 517, 49, 145, 97, 289, 545, 193, 321, 769, 74, 266, 522, 98, 290, 546, 706, 322, 770, 28, 76, 140, 268, 276, 532, 196, 324, 772, 152, 280, 536, 200, 648, 176, 560, 784, 224, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_157, vertices_565, vertices_453, vertices_773, vertices_241, vertices_801, vertices_334, vertices_794, vertices_714, vertices_738, vertices_802, vertices_284, vertices_204, vertices_788, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_49, vertices_145, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_769, vertices_74, vertices_266, vertices_522, vertices_98, vertices_290, vertices_546, vertices_706, vertices_322, vertices_770, vertices_28, vertices_76, vertices_140, vertices_268, vertices_276, vertices_532, vertices_196, vertices_324, vertices_772, vertices_152, vertices_280, vertices_536, vertices_200, vertices_648, vertices_176, vertices_560, vertices_784, vertices_224, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_157), (false, vertices_565), (false, vertices_453), (false, vertices_773), (false, vertices_241), (false, vertices_801), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_546), (true, vertices_706), (true, vertices_770), (true, vertices_76), (true, vertices_268), (true, vertices_276), (true, vertices_280), (true, vertices_536), (true, vertices_200), (true, vertices_648), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 17 else
  if p.val = (false, vertices_157) then 20 else
  if p.val = (false, vertices_565) then 21 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (false, vertices_801) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_706) then 18 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
cert_nodeAtPriority_21 0 773 1 801 74 266 522 546 770 76 268 276 280 536 200 648 784 672 355 706 157 565 453 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 7 334 74 1
cert_row_2 1 0 5 6 8 706
cert_row_4 2 0 2 3 7 8 794 266 2
cert_row_4 3 2 3 4 6 8 696 152 2
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 74 334 1
cert_coverFacet 1 794
cert_cover_5 1 2 0 2 3 7 266 794 2
cert_coverFacet 2 714
cert_cover_5 2 1 0 2 5 6 74 714 3
cert_coverFacet 3 738
cert_cover_5 3 1 0 4 5 6 98 738 3
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 204
cert_cover_2 6 2 1 5 6 76 204 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 696
cert_cover_5 8 3 2 3 4 6 152 696 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0028

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0047.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0047

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 789, 809, 433, 737, 30, 110, 534, 710, 346, 466, 284, 556, 780, 612, 488, 145, 273, 529, 161, 289, 545, 641, 769, 14, 22, 70, 518, 26, 74, 338, 146, 530, 194, 642, 28, 44, 268, 524, 276, 532, 100, 548, 580, 772, 280, 104, 296, 552, 328, 776, 400, 224, 608, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_789, vertices_809, vertices_433, vertices_737, vertices_30, vertices_110, vertices_534, vertices_710, vertices_346, vertices_466, vertices_284, vertices_556, vertices_780, vertices_612, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_14, vertices_22, vertices_70, vertices_518, vertices_26, vertices_74, vertices_338, vertices_146, vertices_530, vertices_194, vertices_642, vertices_28, vertices_44, vertices_268, vertices_524, vertices_276, vertices_532, vertices_100, vertices_548, vertices_580, vertices_772, vertices_280, vertices_104, vertices_296, vertices_552, vertices_328, vertices_776, vertices_400, vertices_224, vertices_608, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_789), (false, vertices_809), (false, vertices_433), (false, vertices_737), (true, vertices_14), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_26), (true, vertices_74), (true, vertices_338), (true, vertices_194), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_100), (true, vertices_548), (true, vertices_580), (true, vertices_280), (true, vertices_104), (true, vertices_328), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 21 23 25 27 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 19 else
  if p.val = (false, vertices_789) then 22 else
  if p.val = (false, vertices_809) then 24 else
  if p.val = (false, vertices_433) then 26 else
  if p.val = (false, vertices_737) then 28 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_338) then 20 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_548) then 12 else
  if p.val = (true, vertices_580) then 13 else
  if p.val = (true, vertices_280) then 14 else
  if p.val = (true, vertices_104) then 15 else
  if p.val = (true, vertices_328) then 16 else
  if p.val = (true, vertices_448) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_338), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 7 338
cert_row_4 1 0 1 5 6 8 710 70 3
cert_row_4 2 0 1 2 4 5 110 14 3
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 3 8 0 2
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 110
cert_cover_5 1 2 0 1 2 4 14 110 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 710
cert_cover_5 3 1 0 1 5 6 70 710 3
cert_coverFacet 4 346
cert_cover_5 4 0 0 2 3 5 26 346 3
cert_coverFacet 5 466
cert_cover_5 5 0 0 3 5 6 338 466 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 556
cert_cover_2 7 2 1 4 8 44 556 3
cert_coverFacet 8 780
cert_cover_2 8 2 1 7 8 268 780 3
cert_coverFacet 9 612
cert_cover_2 9 4 1 5 8 100 612 3
cert_coverFacet 10 488
cert_cover_5 10 3 2 4 5 6 104 488 3
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0047

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0224.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0224

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 595, 147, 803, 617, 369, 401, 158, 542, 774, 236, 812, 420, 728, 464, 480, 19, 131, 259, 515, 81, 145, 273, 97, 289, 545, 577, 385, 30, 134, 262, 518, 146, 530, 770, 44, 140, 524, 164, 292, 388, 772, 152, 536, 104, 552, 200, 584, 208, 336, 592, 400, 224, 352, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_595, vertices_147, vertices_803, vertices_617, vertices_369, vertices_401, vertices_158, vertices_542, vertices_774, vertices_236, vertices_812, vertices_420, vertices_728, vertices_464, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_81, vertices_145, vertices_273, vertices_97, vertices_289, vertices_545, vertices_577, vertices_385, vertices_30, vertices_134, vertices_262, vertices_518, vertices_146, vertices_530, vertices_770, vertices_44, vertices_140, vertices_524, vertices_164, vertices_292, vertices_388, vertices_772, vertices_152, vertices_536, vertices_104, vertices_552, vertices_200, vertices_584, vertices_208, vertices_336, vertices_592, vertices_400, vertices_224, vertices_352, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_595), (false, vertices_147), (false, vertices_803), (false, vertices_617), (false, vertices_369), (false, vertices_401), (true, vertices_30), (true, vertices_518), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_164), (true, vertices_292), (true, vertices_772), (true, vertices_152), (true, vertices_536), (true, vertices_200), (true, vertices_208), (true, vertices_224), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 16 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 17 else
  if p.val = (false, vertices_595) then 20 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_803) then 21 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (true, vertices_30) then 18 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_416) then 14 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
cert_nodeAtPriority_50 0 147 1 401 518 44 140 524 164 292 772 152 536 200 208 224 416 448 391 30 595 803 617 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 1 2 4 5 6 236 44 3
cert_row_4 3 2 3 5 6 8 728 152 2
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 6 30 158 3
cert_coverFacet 1 542
cert_cover_5 1 0 0 1 2 8 30 542 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 236
cert_cover_5 3 2 1 2 4 5 44 236 3
cert_coverFacet 4 812
cert_cover_5 4 1 1 2 4 7 44 812 3
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 728
cert_cover_5 6 3 2 3 5 6 152 728 2
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coverFacet 8 480
cert_cover_2 8 5 4 6 7 224 480 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0224

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0323.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0323

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 805, 709, 617, 241, 417, 206, 590, 790, 154, 538, 434, 376, 216, 792, 808, 133, 261, 517, 97, 161, 289, 545, 193, 577, 385, 78, 134, 262, 518, 26, 138, 522, 146, 274, 530, 386, 196, 580, 772, 88, 152, 280, 536, 104, 296, 552, 200, 584, 776, 112, 176, 304, 208, 784, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_805, vertices_709, vertices_617, vertices_241, vertices_417, vertices_206, vertices_590, vertices_790, vertices_154, vertices_538, vertices_434, vertices_376, vertices_216, vertices_792, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_78, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_196, vertices_580, vertices_772, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_200, vertices_584, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_784, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_805), (false, vertices_709), (false, vertices_617), (false, vertices_241), (false, vertices_417), (true, vertices_78), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_296), (true, vertices_200), (true, vertices_776), (true, vertices_304), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 18 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_617) then 24 else
  if p.val = (false, vertices_241) then 26 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_78) then 19 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_776) then 14 else
  if p.val = (true, vertices_304) then 15 else
  if p.val = (true, vertices_784) then 16 else
  0
cert_priority
cert_nodeAtPriority_14 417 518 26 138 522 146 274 530 88 152 280 536 296 200 776 304 784 391 78 805 709 617 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 262 2
cert_row_2 1 0 1 2 5 78
cert_row_4 2 0 3 4 6 7 434 146 2
cert_row_4 3 2 3 4 5 7 376 88 2
cert_rows
cert_pivot_2 8 1 0 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 6 78 206 3
cert_coverFacet 1 590
cert_cover_5 1 1 0 1 2 8 78 590 3
cert_coverFacet 2 790
cert_cover_5 2 0 0 1 3 7 262 790 2
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 434
cert_cover_5 5 2 0 3 4 6 146 434 2
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 88 376 2
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 792
cert_cover_2 8 3 2 7 8 280 792 3
cert_coverFacet 9 808
cert_cover_2 9 4 2 7 8 296 808 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0323

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0378.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0378

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 595, 195, 285, 301, 537, 233, 369, 902, 226, 866, 418, 668, 172, 852, 420, 67, 131, 515, 269, 25, 41, 137, 521, 81, 273, 529, 97, 289, 193, 98, 162, 290, 194, 578, 386, 642, 770, 28, 44, 140, 276, 532, 164, 292, 388, 644, 772, 536, 168, 648, 336, 592, 224, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_595, vertices_195, vertices_285, vertices_301, vertices_537, vertices_233, vertices_369, vertices_902, vertices_226, vertices_866, vertices_418, vertices_668, vertices_172, vertices_852, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_515, vertices_269, vertices_25, vertices_41, vertices_137, vertices_521, vertices_81, vertices_273, vertices_529, vertices_97, vertices_289, vertices_193, vertices_98, vertices_162, vertices_290, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_140, vertices_276, vertices_532, vertices_164, vertices_292, vertices_388, vertices_644, vertices_772, vertices_536, vertices_168, vertices_648, vertices_336, vertices_592, vertices_224, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_595), (false, vertices_195), (false, vertices_285), (false, vertices_301), (false, vertices_537), (false, vertices_233), (false, vertices_369), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_770), (true, vertices_140), (true, vertices_532), (true, vertices_164), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_416), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_595) then 17 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_285) then 19 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 7 8 866 98 3
cert_row_4 1 0 1 6 7 8 902 386 1
cert_row_4 2 1 2 3 6 8 668 28 3
cert_row_4 3 1 3 5 7 8 852 276 2
cert_rows
cert_pivot_2 4 0 2 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 226
cert_cover_2 1 4 0 5 6 98 226 3
cert_coverFacet 2 866
cert_cover_5 2 0 0 4 5 7 98 866 3
cert_coverFacet 3 418
cert_cover_2 3 4 0 6 7 162 418 3
cert_coverFacet 4 668
cert_cover_5 4 2 1 2 3 6 28 668 3
cert_coverFacet 5 172
cert_cover_2 5 2 1 4 6 44 172 3
cert_coverFacet 6 852
cert_cover_5 6 3 1 3 5 7 276 852 2
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0378

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0493.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0493

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 661, 421, 185, 369, 785, 206, 526, 454, 618, 850, 652, 568, 664, 488, 624, 133, 261, 517, 49, 145, 273, 529, 161, 289, 769, 14, 198, 262, 518, 74, 522, 322, 578, 770, 140, 524, 388, 644, 56, 152, 536, 104, 168, 552, 200, 648, 112, 560, 336, 592, 656, 784, 352, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_661, vertices_421, vertices_185, vertices_369, vertices_785, vertices_206, vertices_526, vertices_454, vertices_618, vertices_850, vertices_652, vertices_568, vertices_664, vertices_488, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_49, vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_769, vertices_14, vertices_198, vertices_262, vertices_518, vertices_74, vertices_522, vertices_322, vertices_578, vertices_770, vertices_140, vertices_524, vertices_388, vertices_644, vertices_56, vertices_152, vertices_536, vertices_104, vertices_168, vertices_552, vertices_200, vertices_648, vertices_112, vertices_560, vertices_336, vertices_592, vertices_656, vertices_784, vertices_352, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_661), (false, vertices_421), (false, vertices_185), (false, vertices_369), (false, vertices_785), (true, vertices_14), (true, vertices_198), (true, vertices_74), (true, vertices_522), (true, vertices_322), (true, vertices_578), (true, vertices_140), (true, vertices_524), (true, vertices_536), (true, vertices_104), (true, vertices_552), (true, vertices_200), (true, vertices_648), (true, vertices_560), (true, vertices_592), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 18 else
  if p.val = (false, vertices_661) then 21 else
  if p.val = (false, vertices_421) then 22 else
  if p.val = (false, vertices_185) then 24 else
  if p.val = (false, vertices_369) then 26 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_198) then 19 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_608) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
cert_nodeAtPriority_14 785 14 74 522 322 578 140 524 536 104 552 200 648 560 592 608 448 775 198 661 421 185 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_4 1 0 3 5 7 8 850 322 1
cert_row_4 2 0 2 4 5 8 618 74 2
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 454
cert_cover_5 2 0 0 1 5 7 198 454 3
cert_coverFacet 3 618
cert_cover_5 3 2 0 2 4 5 74 618 2
cert_coverFacet 4 850
cert_cover_5 4 1 0 3 5 7 322 850 1
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 104 488 3
cert_coverFacet 9 624
cert_cover_2 9 4 3 5 8 112 624 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0493

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0510.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0510

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 805, 233, 297, 841, 689, 94, 566, 838, 154, 202, 658, 348, 436, 408, 424, 41, 73, 265, 161, 289, 545, 193, 577, 641, 769, 22, 70, 518, 26, 74, 138, 146, 530, 194, 578, 642, 92, 52, 276, 292, 548, 324, 772, 152, 280, 168, 296, 200, 328, 392, 176, 560, 400, 656, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_805, vertices_233, vertices_297, vertices_841, vertices_689, vertices_94, vertices_566, vertices_838, vertices_154, vertices_202, vertices_658, vertices_348, vertices_436, vertices_408, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_641, vertices_769, vertices_22, vertices_70, vertices_518, vertices_26, vertices_74, vertices_138, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_92, vertices_52, vertices_276, vertices_292, vertices_548, vertices_324, vertices_772, vertices_152, vertices_280, vertices_168, vertices_296, vertices_200, vertices_328, vertices_392, vertices_176, vertices_560, vertices_400, vertices_656, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_805), (false, vertices_233), (false, vertices_297), (false, vertices_841), (false, vertices_689), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_26), (true, vertices_74), (true, vertices_138), (true, vertices_146), (true, vertices_530), (true, vertices_92), (true, vertices_52), (true, vertices_276), (true, vertices_324), (true, vertices_152), (true, vertices_280), (true, vertices_392), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_841) then 24 else
  if p.val = (false, vertices_689) then 26 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_138) then 6 else
  if p.val = (true, vertices_146) then 7 else
  if p.val = (true, vertices_530) then 8 else
  if p.val = (true, vertices_92) then 21 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
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
cert_row_2 0 1 2 3 5 92
cert_row_4 1 0 1 5 7 8 838 70 3
cert_row_4 2 0 1 3 4 8 566 22 3
cert_row_4 3 1 3 4 6 7 436 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 22 94 2
cert_coverFacet 1 566
cert_cover_5 1 2 0 1 3 4 22 566 3
cert_coverFacet 2 838
cert_cover_5 2 1 0 1 5 7 70 838 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 202
cert_cover_2 4 2 0 5 6 74 202 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 348
cert_cover_5 6 0 1 2 3 7 92 348 3
cert_coverFacet 7 436
cert_cover_5 7 3 1 3 4 6 52 436 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 424
cert_cover_2 9 4 2 6 7 168 424 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0510

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0658.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0658

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 901, 681, 625, 481, 654, 270, 774, 570, 346, 594, 60, 284, 172, 244, 468, 97, 161, 545, 321, 577, 385, 641, 769, 14, 262, 518, 26, 266, 522, 82, 530, 322, 578, 770, 28, 44, 140, 268, 52, 212, 276, 164, 388, 644, 772, 56, 280, 168, 552, 648, 112, 560, 336, 592, 224, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_901, vertices_681, vertices_625, vertices_481, vertices_654, vertices_270, vertices_774, vertices_570, vertices_346, vertices_594, vertices_60, vertices_284, vertices_172, vertices_244, vertices_468] (by decide +kernel)
  polygons := literalFinset [vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_262, vertices_518, vertices_26, vertices_266, vertices_522, vertices_82, vertices_530, vertices_322, vertices_578, vertices_770, vertices_28, vertices_44, vertices_140, vertices_268, vertices_52, vertices_212, vertices_276, vertices_164, vertices_388, vertices_644, vertices_772, vertices_56, vertices_280, vertices_168, vertices_552, vertices_648, vertices_112, vertices_560, vertices_336, vertices_592, vertices_224, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_901), (false, vertices_681), (false, vertices_625), (false, vertices_481), (true, vertices_14), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_82), (true, vertices_530), (true, vertices_28), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_52), (true, vertices_212), (true, vertices_276), (true, vertices_164), (true, vertices_56), (true, vertices_280), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 20 23 25 27 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_901) then 21 else
  if p.val = (false, vertices_681) then 24 else
  if p.val = (false, vertices_625) then 26 else
  if p.val = (false, vertices_481) then 28 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_82) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_268) then 11 else
  if p.val = (true, vertices_52) then 12 else
  if p.val = (true, vertices_212) then 22 else
  if p.val = (true, vertices_276) then 13 else
  if p.val = (true, vertices_164) then 14 else
  if p.val = (true, vertices_56) then 15 else
  if p.val = (true, vertices_280) then 16 else
  if p.val = (true, vertices_336) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 26 3
cert_row_4 1 0 1 2 6 8 654 14 3
cert_row_2 2 1 3 5 6 212
cert_row_4 3 0 2 3 5 7 346 26 3
cert_rows
cert_pivot_2 4 8 1 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 14 654 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 570
cert_cover_5 3 0 0 2 3 4 26 570 3
cert_coverFacet 4 346
cert_cover_5 4 3 0 2 3 5 26 346 3
cert_coverFacet 5 594
cert_cover_2 5 3 0 5 8 82 594 3
cert_coverFacet 6 60
cert_cover_2 6 2 1 3 4 28 60 3
cert_coverFacet 7 284
cert_cover_2 7 2 1 3 7 28 284 3
cert_coverFacet 8 172
cert_cover_2 8 2 1 4 6 44 172 3
cert_coverFacet 9 244
cert_cover_5 9 2 1 3 4 5 52 244 3
cert_coverFacet 10 468
cert_cover_5 10 2 1 3 5 7 212 468 3
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0658

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0690.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0690

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 301, 229, 837, 433, 897, 782, 602, 154, 394, 242, 898, 572, 628, 312, 408, 37, 69, 261, 161, 289, 193, 577, 385, 641, 769, 26, 138, 266, 522, 82, 146, 194, 578, 386, 642, 770, 44, 268, 524, 564, 100, 580, 772, 56, 152, 280, 536, 296, 392, 112, 176, 304, 592, 400, 224, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_301, vertices_229, vertices_837, vertices_433, vertices_897, vertices_782, vertices_602, vertices_154, vertices_394, vertices_242, vertices_898, vertices_572, vertices_628, vertices_312, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_261, vertices_161, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_82, vertices_146, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_524, vertices_564, vertices_100, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_536, vertices_296, vertices_392, vertices_112, vertices_176, vertices_304, vertices_592, vertices_400, vertices_224, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_301), (false, vertices_229), (false, vertices_837), (false, vertices_433), (false, vertices_897), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_82), (true, vertices_146), (true, vertices_386), (true, vertices_770), (true, vertices_524), (true, vertices_564), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_392), (true, vertices_112), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 19 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_837) then 23 else
  if p.val = (false, vertices_433) then 26 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_564) then 24 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_112) then 15 else
  if p.val = (true, vertices_592) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_564), by decide +kernel⟩
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
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_2 1 1 3 4 8 564
cert_row_4 2 0 2 3 5 8 602 26 3
cert_row_4 3 0 3 4 5 6 242 82 2
cert_rows
cert_pivot_2 7 1 2 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 602
cert_cover_5 1 2 0 2 3 5 26 602 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 242
cert_cover_5 4 3 0 3 4 5 82 242 2
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 572
cert_cover_5 6 1 1 2 3 4 44 572 2
cert_coverFacet 7 628
cert_cover_5 7 1 1 3 4 5 564 628 3
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coverFacet 9 408
cert_cover_2 9 3 2 6 7 152 408 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0690

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_multi_six_0000.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0000

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 653, 961, 278, 326, 794, 236, 372, 696, 1008, 7, 11, 67, 259, 13, 133, 521, 193, 321, 641, 769, 22, 70, 262, 26, 778, 274, 322, 44, 140, 52, 276, 100, 196, 324, 56, 536, 168, 648, 368, 688, 784, 224, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_653, vertices_961, vertices_278, vertices_326, vertices_794, vertices_236, vertices_372, vertices_696, vertices_1008] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_133, vertices_521, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_70, vertices_262, vertices_26, vertices_778, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_276, vertices_100, vertices_196, vertices_324, vertices_56, vertices_536, vertices_168, vertices_648, vertices_368, vertices_688, vertices_784, vertices_224, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_653), (false, vertices_961), (true, vertices_262), (true, vertices_274), (true, vertices_276), (true, vertices_100), (true, vertices_324), (true, vertices_536), (true, vertices_168), (true, vertices_368), (true, vertices_688), (true, vertices_784), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 17 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_779) then 12 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_653) then 15 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_368) then 18 else
  if p.val = (true, vertices_688) then 19 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_224) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_368), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_688), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 2 4 5 6 236 44 3
cert_row_4 2 3 4 5 6 7 1008 368 3
cert_row_4 3 3 4 5 6 8 1008 368 3
cert_rows
cert_pivot_2 0 1 7 3
cert_heightProof 4
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 794
cert_cover_5 2 0 0 2 3 7 26 794 3
cert_coverFacet 3 236
cert_cover_5 3 1 1 2 4 5 44 236 3
cert_coverFacet 4 372
cert_cover 4 4 4 1 3 3 3 5 5 52 372 368 368 1008 6
cert_coverFacet 5 696
cert_cover 5 4 4 2 3 3 3 6 5 56 696 688 368 1008 6
cert_coverFacet 6 1008
cert_cover_2 6 4 3 5 6 368 1008 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0000

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_multi_six_0001.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0001

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 341, 473, 654, 838, 706, 684, 820, 440, 992, 7, 11, 67, 21, 69, 25, 201, 337, 14, 70, 518, 138, 194, 578, 642, 44, 652, 52, 276, 548, 324, 772, 56, 408, 168, 304, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_341, vertices_473, vertices_654, vertices_838, vertices_706, vertices_684, vertices_820, vertices_440, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_25, vertices_201, vertices_337, vertices_14, vertices_70, vertices_518, vertices_138, vertices_194, vertices_578, vertices_642, vertices_44, vertices_652, vertices_52, vertices_276, vertices_548, vertices_324, vertices_772, vertices_56, vertices_408, vertices_168, vertices_304, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_341), (false, vertices_473), (true, vertices_518), (true, vertices_578), (true, vertices_642), (true, vertices_652), (true, vertices_548), (true, vertices_772), (true, vertices_168), (true, vertices_304), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 14 17 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 18 else
  if p.val = (false, vertices_341) then 20 else
  if p.val = (false, vertices_473) then 21 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_652) then 16 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_473), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 7 8 838 70 3
cert_row_4 1 4 5 6 7 8 992 416 1
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_2 3 2 3 6 7 408
cert_row_2 4 1 2 6 8 652
cert_rows_2
cert_pivot 0 5 4 3 1
cert_heightProof 5
cert_coverFacet 0 654
cert_cover_5 0 4 0 1 2 6 14 654 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 706
cert_cover_2 2 5 0 6 8 194 706 3
cert_coverFacet 3 684
cert_cover_5 3 4 1 2 4 6 44 684 3
cert_coverFacet 4 820
cert_cover_5 4 2 1 3 4 7 52 820 3
cert_coverFacet 5 440
cert_cover_5 5 3 2 3 4 6 56 440 3
cert_coverFacet 6 992
cert_cover_5 6 1 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 5 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0001

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_multi_six_0002.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0002

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 333, 150, 666, 962, 364, 244, 824, 1008, 7, 11, 67, 259, 13, 69, 265, 321, 22, 134, 26, 522, 146, 194, 322, 642, 770, 44, 332, 52, 148, 100, 196, 56, 536, 296, 776, 240, 816, 656, 352, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_333, vertices_150, vertices_666, vertices_962, vertices_364, vertices_244, vertices_824, vertices_1008] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_265, vertices_321, vertices_22, vertices_134, vertices_26, vertices_522, vertices_146, vertices_194, vertices_322, vertices_642, vertices_770, vertices_44, vertices_332, vertices_52, vertices_148, vertices_100, vertices_196, vertices_56, vertices_536, vertices_296, vertices_776, vertices_240, vertices_816, vertices_656, vertices_352, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_333), (true, vertices_146), (true, vertices_642), (true, vertices_148), (true, vertices_100), (true, vertices_536), (true, vertices_296), (true, vertices_240), (true, vertices_816), (true, vertices_656), (true, vertices_352), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 16 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 10 else
  if p.val = (false, vertices_779) then 11 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_333) then 14 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_240) then 17 else
  if p.val = (true, vertices_816) then 18 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_960) then 21 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(true, vertices_960), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 7 332
cert_row_4 1 0 2 3 6 8 666 26 3
cert_row_4 2 3 4 5 7 6 1008 240 3
cert_row_4 3 3 4 5 7 8 1008 240 3
cert_rows
cert_pivot_2 1 0 6 3
cert_heightProof 4
cert_coverFacet 0 150
cert_cover_2 0 1 0 3 6 22 150 3
cert_coverFacet 1 666
cert_cover_5 1 1 0 2 3 6 26 666 3
cert_coverFacet 2 962
cert_cover 2 6 4 0 5 3 3 7 5 194 962 960 240 1008 7
cert_coverFacet 3 364
cert_cover_5 3 0 1 2 4 5 44 364 3
cert_coverFacet 4 244
cert_cover 4 4 4 1 3 3 3 5 5 52 244 240 240 1008 7
cert_coverFacet 5 824
cert_cover 5 4 4 2 3 3 3 7 5 56 824 816 240 1008 7
cert_coverFacet 6 1008
cert_cover_2 6 4 3 5 7 240 1008 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0002

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_multi_six_0003.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0003

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 653, 961, 342, 282, 684, 244, 824, 1008, 7, 11, 67, 259, 13, 133, 521, 193, 321, 641, 769, 22, 70, 26, 266, 274, 322, 44, 652, 52, 84, 164, 196, 56, 280, 552, 776, 240, 816, 336, 672, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_653, vertices_961, vertices_342, vertices_282, vertices_684, vertices_244, vertices_824, vertices_1008] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_133, vertices_521, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_274, vertices_322, vertices_44, vertices_652, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_280, vertices_552, vertices_776, vertices_240, vertices_816, vertices_336, vertices_672, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_653), (false, vertices_961), (true, vertices_274), (true, vertices_84), (true, vertices_164), (true, vertices_280), (true, vertices_552), (true, vertices_240), (true, vertices_816), (true, vertices_336), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 15 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_779) then 10 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_653) then 13 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_240) then 16 else
  if p.val = (true, vertices_816) then 17 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_672) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 8 652
cert_row_4 1 0 1 3 5 7 342 22 3
cert_row_4 2 3 4 5 7 6 1008 240 3
cert_row_4 3 3 4 5 7 8 1008 240 3
cert_rows
cert_pivot_2 2 0 6 3
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 1 0 1 3 5 22 342 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 684
cert_cover_5 2 0 1 2 4 6 44 684 3
cert_coverFacet 3 244
cert_cover 3 4 4 1 3 3 3 5 5 52 244 240 240 1008 7
cert_coverFacet 4 824
cert_cover 4 4 4 2 3 3 3 7 5 56 824 816 240 1008 7
cert_coverFacet 5 1008
cert_cover_2 5 4 3 5 7 240 1008 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0003

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_multi_six_0004.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0004

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 653, 777, 961, 342, 282, 684, 244, 824, 1008, 7, 11, 67, 13, 133, 265, 521, 193, 321, 641, 769, 22, 70, 26, 266, 274, 322, 44, 652, 52, 84, 164, 196, 56, 280, 552, 776, 240, 816, 336, 672, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_653, vertices_777, vertices_961, vertices_342, vertices_282, vertices_684, vertices_244, vertices_824, vertices_1008] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_521, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_274, vertices_322, vertices_44, vertices_652, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_280, vertices_552, vertices_776, vertices_240, vertices_816, vertices_336, vertices_672, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_653), (false, vertices_777), (false, vertices_961), (true, vertices_274), (true, vertices_84), (true, vertices_164), (true, vertices_280), (true, vertices_552), (true, vertices_240), (true, vertices_816), (true, vertices_336), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 15 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_331) then 10 else
  if p.val = (false, vertices_653) then 13 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_240) then 16 else
  if p.val = (true, vertices_816) then 17 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_672) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 8 652
cert_row_4 1 0 1 3 5 7 342 22 3
cert_row_4 2 3 4 5 7 6 1008 240 3
cert_row_4 3 3 4 5 7 8 1008 240 3
cert_rows
cert_pivot_2 2 0 6 3
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 1 0 1 3 5 22 342 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 684
cert_cover_5 2 0 1 2 4 6 44 684 3
cert_coverFacet 3 244
cert_cover 3 4 4 1 3 3 3 5 5 52 244 240 240 1008 7
cert_coverFacet 4 824
cert_cover 4 4 4 2 3 3 3 7 5 56 824 816 240 1008 7
cert_coverFacet 5 1008
cert_cover_2 5 4 3 5 7 240 1008 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0004

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_multi_six_0005.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0005

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 781, 645, 961, 86, 346, 684, 244, 824, 1008, 7, 11, 67, 13, 133, 517, 265, 193, 321, 641, 769, 22, 70, 26, 330, 82, 44, 524, 52, 84, 164, 196, 644, 56, 280, 552, 776, 240, 816, 336, 672, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_781, vertices_645, vertices_961, vertices_86, vertices_346, vertices_684, vertices_244, vertices_824, vertices_1008] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_517, vertices_265, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_70, vertices_26, vertices_330, vertices_82, vertices_44, vertices_524, vertices_52, vertices_84, vertices_164, vertices_196, vertices_644, vertices_56, vertices_280, vertices_552, vertices_776, vertices_240, vertices_816, vertices_336, vertices_672, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_781), (false, vertices_645), (false, vertices_961), (true, vertices_82), (true, vertices_84), (true, vertices_164), (true, vertices_280), (true, vertices_552), (true, vertices_240), (true, vertices_816), (true, vertices_336), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 15 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_331) then 10 else
  if p.val = (false, vertices_781) then 13 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_240) then 16 else
  if p.val = (true, vertices_816) then 17 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_672) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_645), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 7 330
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 3 4 5 7 6 1008 240 3
cert_row_4 3 3 4 5 7 8 1008 240 3
cert_rows
cert_pivot_2 0 1 6 3
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 5 26 346 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 44 684 3
cert_coverFacet 3 244
cert_cover 3 4 4 1 3 3 3 5 5 52 244 240 240 1008 7
cert_coverFacet 4 824
cert_cover 4 4 4 2 3 3 3 7 5 56 824 816 240 1008 7
cert_coverFacet 5 1008
cert_cover_2 5 4 3 5 7 240 1008 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0005

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_multi_six_0006.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0006

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 597, 857, 398, 450, 428, 692, 708, 824, 992, 7, 11, 67, 21, 69, 25, 329, 593, 14, 134, 266, 194, 322, 386, 44, 396, 52, 532, 164, 196, 580, 644, 56, 792, 296, 560, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_597, vertices_857, vertices_398, vertices_450, vertices_428, vertices_692, vertices_708, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_25, vertices_329, vertices_593, vertices_14, vertices_134, vertices_266, vertices_194, vertices_322, vertices_386, vertices_44, vertices_396, vertices_52, vertices_532, vertices_164, vertices_196, vertices_580, vertices_644, vertices_56, vertices_792, vertices_296, vertices_560, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_597), (false, vertices_857), (true, vertices_386), (true, vertices_396), (true, vertices_164), (true, vertices_644), (true, vertices_296), (true, vertices_560), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_857) then 19 else
  if p.val = (true, vertices_386) then 0 else
  if p.val = (true, vertices_396) then 14 else
  if p.val = (true, vertices_164) then 1 else
  if p.val = (true, vertices_644) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_416) then 5 else
  if p.val = (true, vertices_672) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_857), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 4 5 6 7 8 992 416 1
cert_row_4 1 1 3 4 6 8 692 52 3
cert_row_2 2 1 2 6 7 396
cert_row_2 3 2 3 7 8 792
cert_rows
cert_pivot_2 5 4 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 2 0 1 2 6 14 398 3
cert_coverFacet 1 450
cert_cover_2 1 5 0 6 7 194 450 3
cert_coverFacet 2 428
cert_cover_5 2 2 1 2 4 6 44 428 3
cert_coverFacet 3 692
cert_cover_5 3 1 1 3 4 6 52 692 3
cert_coverFacet 4 708
cert_cover_2 4 5 1 6 8 196 708 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 992
cert_cover_5 6 0 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0006

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_multi_six_0009.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0009

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 85, 921, 721, 334, 450, 364, 628, 824, 992, 7, 11, 131, 21, 69, 25, 393, 81, 657, 193, 14, 70, 266, 194, 322, 386, 44, 332, 52, 84, 100, 56, 792, 296, 560, 592, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_85, vertices_921, vertices_721, vertices_334, vertices_450, vertices_364, vertices_628, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_69, vertices_25, vertices_393, vertices_81, vertices_657, vertices_193, vertices_14, vertices_70, vertices_266, vertices_194, vertices_322, vertices_386, vertices_44, vertices_332, vertices_52, vertices_84, vertices_100, vertices_56, vertices_792, vertices_296, vertices_560, vertices_592, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_85), (false, vertices_921), (false, vertices_721), (true, vertices_322), (true, vertices_332), (true, vertices_100), (true, vertices_296), (true, vertices_560), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 11 14 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 10 else
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_85) then 0 else
  if p.val = (false, vertices_921) then 17 else
  if p.val = (false, vertices_721) then 18 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_332) then 13 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_352) then 5 else
  if p.val = (true, vertices_608) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_448) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_921), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 4 5 6 7 8 992 352 2
cert_row_4 1 1 3 4 5 8 628 52 3
cert_row_2 2 1 2 5 7 332
cert_row_2 3 2 3 7 8 792
cert_rows
cert_pivot_2 6 4 1 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 2 0 1 2 5 14 334 3
cert_coverFacet 1 450
cert_cover_2 1 5 0 6 7 194 450 3
cert_coverFacet 2 364
cert_cover_5 2 2 1 2 4 5 44 364 3
cert_coverFacet 3 628
cert_cover_5 3 1 1 3 4 5 52 628 3
cert_coverFacet 4 824
cert_cover_5 4 3 2 3 4 7 56 824 3
cert_coverFacet 5 992
cert_cover_5 5 0 4 5 6 7 352 992 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0009

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_multi_six_0010.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0010

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 333, 961, 86, 922, 722, 300, 628, 868, 824, 7, 11, 131, 13, 69, 265, 193, 321, 385, 22, 70, 26, 394, 82, 658, 194, 44, 268, 52, 84, 612, 292, 324, 56, 792, 296, 560, 592, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_333, vertices_961, vertices_86, vertices_922, vertices_722, vertices_300, vertices_628, vertices_868, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_13, vertices_69, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_394, vertices_82, vertices_658, vertices_194, vertices_44, vertices_268, vertices_52, vertices_84, vertices_612, vertices_292, vertices_324, vertices_56, vertices_792, vertices_296, vertices_560, vertices_592, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_333), (false, vertices_961), (true, vertices_82), (true, vertices_658), (true, vertices_84), (true, vertices_612), (true, vertices_292), (true, vertices_792), (true, vertices_296), (true, vertices_560), (true, vertices_592), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 14 17 7 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_333) then 15 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_658) then 8 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_612) then 16 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_792) then 9 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_592) then 5 else
  if p.val = (true, vertices_800) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inl 3
  | 8 => Sum.inr ⟨(true, vertices_658), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 8 612
cert_row_4 1 0 2 3 6 7 922 26 3
cert_row_4 2 0 2 3 6 8 922 26 3
cert_rows_3
cert_pivot_3 7 1 0
cert_heightProof 3
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 922
cert_cover_2 1 2 0 3 6 26 922 3
cert_coverFacet 2 722
cert_cover 2 5 2 0 3 3 0 6 3 82 722 658 26 922 6
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 628
cert_cover_5 4 0 1 3 4 5 52 628 3
cert_coverFacet 5 868
cert_cover_5 5 0 1 4 5 7 612 868 3
cert_coverFacet 6 824
cert_cover 6 4 2 2 3 3 0 7 3 56 824 792 26 922 6
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0010

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_multi_six_0011.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0011

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 451, 213, 921, 782, 838, 620, 244, 696, 992, 7, 11, 67, 259, 21, 69, 25, 265, 145, 193, 385, 14, 70, 774, 266, 322, 44, 524, 52, 212, 100, 580, 56, 664, 552, 776, 176, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_451, vertices_213, vertices_921, vertices_782, vertices_838, vertices_620, vertices_244, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_265, vertices_145, vertices_193, vertices_385, vertices_14, vertices_70, vertices_774, vertices_266, vertices_322, vertices_44, vertices_524, vertices_52, vertices_212, vertices_100, vertices_580, vertices_56, vertices_664, vertices_552, vertices_776, vertices_176, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_451), (false, vertices_213), (false, vertices_921), (true, vertices_774), (true, vertices_524), (true, vertices_100), (true, vertices_580), (true, vertices_552), (true, vertices_176), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_451) then 12 else
  if p.val = (false, vertices_213) then 16 else
  if p.val = (false, vertices_921) then 19 else
  if p.val = (true, vertices_774) then 13 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_921), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 4 5 6 7 8 992 224 3
cert_row_4 2 1 2 4 5 8 620 44 3
cert_row_2 3 2 3 6 8 664
cert_row_2 4 1 3 5 6 212
cert_rows_2
cert_pivot 0 7 4 2 1
cert_heightProof 5
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 620
cert_cover_5 2 2 1 2 4 5 44 620 3
cert_coverFacet 3 244
cert_cover_5 3 4 1 3 4 5 52 244 3
cert_coverFacet 4 696
cert_cover_5 4 3 2 3 4 6 56 696 3
cert_coverFacet 5 992
cert_cover_5 5 1 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 5 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0011

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_multi_six_0012.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0012

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 451, 845, 214, 794, 914, 620, 244, 696, 992, 7, 11, 67, 259, 13, 69, 265, 321, 22, 70, 26, 266, 146, 786, 194, 386, 44, 588, 52, 212, 100, 56, 536, 552, 776, 176, 656, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_451, vertices_845, vertices_214, vertices_794, vertices_914, vertices_620, vertices_244, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_265, vertices_321, vertices_22, vertices_70, vertices_26, vertices_266, vertices_146, vertices_786, vertices_194, vertices_386, vertices_44, vertices_588, vertices_52, vertices_212, vertices_100, vertices_56, vertices_536, vertices_552, vertices_776, vertices_176, vertices_656, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_451), (false, vertices_845), (true, vertices_146), (true, vertices_786), (true, vertices_212), (true, vertices_100), (true, vertices_536), (true, vertices_552), (true, vertices_176), (true, vertices_656), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_451) then 13 else
  if p.val = (false, vertices_845) then 19 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_786) then 14 else
  if p.val = (true, vertices_212) then 17 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_786), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_845), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 7 8 786
cert_row_4 1 4 5 6 7 8 992 224 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_2 3 1 2 5 8 588
cert_row_2 4 1 3 5 6 212
cert_rows_2
cert_pivot 0 7 4 2 1
cert_heightProof 5
cert_coverFacet 0 214
cert_cover_5 0 4 0 1 3 5 22 214 3
cert_coverFacet 1 794
cert_cover_5 1 0 0 2 3 7 26 794 3
cert_coverFacet 2 914
cert_cover_5 2 0 0 3 6 7 146 914 3
cert_coverFacet 3 620
cert_cover_5 3 3 1 2 4 5 44 620 3
cert_coverFacet 4 244
cert_cover_5 4 4 1 3 4 5 52 244 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 992
cert_cover_5 6 1 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 5 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0012

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_multi_six_0013.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0013

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 587, 213, 809, 753, 782, 454, 962, 412, 440, 928, 7, 11, 67, 21, 69, 41, 521, 49, 209, 545, 577, 14, 70, 262, 522, 450, 578, 770, 28, 268, 148, 196, 388, 56, 408, 296, 776, 176, 416, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_587, vertices_213, vertices_809, vertices_753, vertices_782, vertices_454, vertices_962, vertices_412, vertices_440, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_209, vertices_545, vertices_577, vertices_14, vertices_70, vertices_262, vertices_522, vertices_450, vertices_578, vertices_770, vertices_28, vertices_268, vertices_148, vertices_196, vertices_388, vertices_56, vertices_408, vertices_296, vertices_776, vertices_176, vertices_416, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_587), (false, vertices_213), (false, vertices_809), (false, vertices_753), (true, vertices_262), (true, vertices_450), (true, vertices_770), (true, vertices_268), (true, vertices_388), (true, vertices_408), (true, vertices_416), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 7 10 12 15 17 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_587) then 8 else
  if p.val = (false, vertices_213) then 16 else
  if p.val = (false, vertices_809) then 13 else
  if p.val = (false, vertices_753) then 18 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_450) then 9 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_408) then 14 else
  if p.val = (true, vertices_416) then 5 else
  if p.val = (true, vertices_896) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_450), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(false, vertices_753), by decide +kernel⟩
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 6 7 408
cert_row_2 1 0 5 6 7 450
cert_row_4 2 0 1 2 7 8 782 14 3
cert_rows_3
cert_pivot_3 5 3 0
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 14 782 3
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 6 70 454 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 8 450 962 3
cert_coverFacet 3 412
cert_cover_5 3 0 1 2 3 6 28 412 3
cert_coverFacet 4 440
cert_cover_5 4 0 2 3 4 6 56 440 3
cert_coverFacet 5 928
cert_cover_2 5 6 4 7 8 416 928 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0013

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0510 : Certifies 510 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1242.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0511 : Certifies 511 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1247.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0512 : Certifies 512 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1248.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0513 : Certifies 513 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1250.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0514 : Certifies 514 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0007.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0515 : Certifies 515 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0014.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0516 : Certifies 516 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0020.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0517 : Certifies 517 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0037.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0518 : Certifies 518 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0075.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0519 : Certifies 519 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0028.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0520 : Certifies 520 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0047.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0521 : Certifies 521 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0224.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0522 : Certifies 522 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0323.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0523 : Certifies 523 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0378.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0524 : Certifies 524 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0493.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0525 : Certifies 525 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0510.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0526 : Certifies 526 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0658.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0527 : Certifies 527 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0690.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0528 : Certifies 528 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0000.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0529 : Certifies 529 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0001.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0530 : Certifies 530 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0002.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0531 : Certifies 531 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0003.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0532 : Certifies 532 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0004.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0533 : Certifies 533 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0005.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0534 : Certifies 534 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0006.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0535 : Certifies 535 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0009.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0536 : Certifies 536 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0010.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0537 : Certifies 537 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0011.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0538 : Certifies 538 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0012.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0539 : Certifies 539 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0013.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B017 (j : Fin 30) :
    Certifies (510 + j.val) := by
  fin_cases j
  · exact projection_0510
  · exact projection_0511
  · exact projection_0512
  · exact projection_0513
  · exact projection_0514
  · exact projection_0515
  · exact projection_0516
  · exact projection_0517
  · exact projection_0518
  · exact projection_0519
  · exact projection_0520
  · exact projection_0521
  · exact projection_0522
  · exact projection_0523
  · exact projection_0524
  · exact projection_0525
  · exact projection_0526
  · exact projection_0527
  · exact projection_0528
  · exact projection_0529
  · exact projection_0530
  · exact projection_0531
  · exact projection_0532
  · exact projection_0533
  · exact projection_0534
  · exact projection_0535
  · exact projection_0536
  · exact projection_0537
  · exact projection_0538
  · exact projection_0539

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
