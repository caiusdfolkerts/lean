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
/- Source: ProjectionCertificates/R_m14e10q1_0693.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0693

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 331, 51, 83, 781, 53, 597, 713, 690, 722, 482, 820, 936, 456, 19, 35, 67, 259, 21, 37, 261, 517, 73, 265, 521, 49, 81, 577, 50, 82, 658, 162, 290, 194, 322, 52, 532, 292, 772, 200, 328, 392, 648, 776, 560, 592, 416, 672, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_331, vertices_51, vertices_83, vertices_781, vertices_53, vertices_597, vertices_713, vertices_690, vertices_722, vertices_482, vertices_820, vertices_936, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_67, vertices_259, vertices_21, vertices_37, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_49, vertices_81, vertices_577, vertices_50, vertices_82, vertices_658, vertices_162, vertices_290, vertices_194, vertices_322, vertices_52, vertices_532, vertices_292, vertices_772, vertices_200, vertices_328, vertices_392, vertices_648, vertices_776, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_331), (false, vertices_51), (false, vertices_83), (false, vertices_781), (false, vertices_53), (false, vertices_597), (false, vertices_713), (true, vertices_658), (true, vertices_162), (true, vertices_194), (true, vertices_392), (true, vertices_560), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 11 18 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 12 else
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_51) then 0 else
  if p.val = (false, vertices_83) then 1 else
  if p.val = (false, vertices_781) then 13 else
  if p.val = (false, vertices_53) then 2 else
  if p.val = (false, vertices_597) then 14 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (true, vertices_658) then 17 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_448) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_83), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_53), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_658), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 6 7 482 162 2
cert_row_2 1 0 3 6 8 658
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 2 4 6 7 8 936 392 1
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 690
cert_cover_5 0 1 0 3 4 6 50 690 3
cert_coverFacet 1 722
cert_cover_5 1 1 0 3 5 6 82 722 3
cert_coverFacet 2 482
cert_cover_5 2 0 0 4 5 6 162 482 2
cert_coverFacet 3 820
cert_cover_5 3 2 1 3 4 7 52 820 3
cert_coverFacet 4 936
cert_cover_5 4 3 2 4 6 7 392 936 1
cert_coverFacet 5 456
cert_cover_2 5 5 2 6 7 200 456 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0693

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m14e10q1_0714.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0714

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 171, 355, 835, 121, 713, 790, 390, 418, 668, 436, 184, 600, 880, 35, 323, 131, 515, 41, 73, 137, 97, 577, 641, 134, 262, 518, 162, 290, 386, 770, 148, 276, 532, 388, 644, 56, 88, 152, 536, 168, 584, 648, 112, 176, 304, 592, 784, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_171, vertices_355, vertices_835, vertices_121, vertices_713, vertices_790, vertices_390, vertices_418, vertices_668, vertices_436, vertices_184, vertices_600, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_323, vertices_131, vertices_515, vertices_41, vertices_73, vertices_137, vertices_97, vertices_577, vertices_641, vertices_134, vertices_262, vertices_518, vertices_162, vertices_290, vertices_386, vertices_770, vertices_148, vertices_276, vertices_532, vertices_388, vertices_644, vertices_56, vertices_88, vertices_152, vertices_536, vertices_168, vertices_584, vertices_648, vertices_112, vertices_176, vertices_304, vertices_592, vertices_784, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_171), (false, vertices_355), (false, vertices_835), (false, vertices_121), (false, vertices_713), (true, vertices_262), (true, vertices_386), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_388), (true, vertices_152), (true, vertices_536), (true, vertices_176), (true, vertices_304), (true, vertices_592), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 13 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_171) then 16 else
  if p.val = (false, vertices_355) then 17 else
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
cert_nodeAtPriority 1 262 0 386 2 148 276 532 388 152 536 176 304 592 784 416 647 171 355 835 121 713
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 262 2
cert_row_4 1 1 2 3 6 8 668 148 1
cert_row_4 2 1 3 4 6 7 436 148 2
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 262 790 2
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 418
cert_cover_2 2 4 0 6 7 162 418 3
cert_coverFacet 3 668
cert_cover_5 3 1 1 2 3 6 148 668 1
cert_coverFacet 4 436
cert_cover_5 4 2 1 3 4 6 148 436 2
cert_coverFacet 5 184
cert_cover_2 5 3 2 4 6 56 184 3
cert_coverFacet 6 600
cert_cover_2 6 3 2 5 8 88 600 3
cert_coverFacet 7 880
cert_cover_5 7 3 3 4 5 7 112 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0714

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m14e10q1_0715.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0715

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 333, 653, 597, 425, 449, 342, 682, 818, 594, 418, 450, 316, 572, 13, 69, 517, 137, 265, 193, 321, 577, 385, 641, 82, 274, 530, 162, 290, 546, 194, 322, 578, 386, 642, 60, 268, 524, 84, 276, 532, 324, 168, 296, 552, 648, 304, 560, 592, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_333, vertices_653, vertices_597, vertices_425, vertices_449, vertices_342, vertices_682, vertices_818, vertices_594, vertices_418, vertices_450, vertices_316, vertices_572] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_137, vertices_265, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_82, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_60, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_324, vertices_168, vertices_296, vertices_552, vertices_648, vertices_304, vertices_560, vertices_592, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_333), (false, vertices_653), (false, vertices_597), (false, vertices_425), (false, vertices_449), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_386), (true, vertices_60), (true, vertices_276), (true, vertices_552), (true, vertices_304), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 18 21 15 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_653) then 20 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_60) then 17 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_560) then 12 else
  0
cert_priority
cert_nodeAtPriority_2 0 449 3 82 1 274 2 530 162 290 546 322 386 276 552 304 560 707 597 60 333 653 425
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 82 1
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 2 4 6 8 682 162 1
cert_row_4 3 0 3 4 7 8 818 274 2
cert_rows
cert_pivot_2 5 1 2 0
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 82 342 1
cert_coverFacet 1 682
cert_cover_5 1 2 0 2 4 6 162 682 1
cert_coverFacet 2 818
cert_cover_5 2 3 0 3 4 7 274 818 2
cert_coverFacet 3 594
cert_cover_2 3 3 0 5 8 82 594 3
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 316
cert_cover_5 6 1 1 2 3 7 60 316 3
cert_coverFacet 7 572
cert_cover_5 7 1 1 2 3 8 60 572 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0715

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m14e10q1_0717.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0717

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 397, 345, 665, 625, 449, 654, 614, 294, 390, 370, 450, 316, 572, 25, 137, 265, 81, 529, 193, 321, 577, 385, 641, 38, 134, 262, 518, 98, 290, 194, 322, 578, 386, 642, 60, 140, 268, 524, 292, 548, 388, 280, 536, 648, 112, 304, 560, 336, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_397, vertices_345, vertices_665, vertices_625, vertices_449, vertices_654, vertices_614, vertices_294, vertices_390, vertices_370, vertices_450, vertices_316, vertices_572] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_81, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_38, vertices_134, vertices_262, vertices_518, vertices_98, vertices_290, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_60, vertices_140, vertices_268, vertices_524, vertices_292, vertices_548, vertices_388, vertices_280, vertices_536, vertices_648, vertices_112, vertices_304, vertices_560, vertices_336, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_397), (false, vertices_345), (false, vertices_665), (false, vertices_625), (false, vertices_449), (true, vertices_38), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_98), (true, vertices_290), (true, vertices_322), (true, vertices_386), (true, vertices_60), (true, vertices_524), (true, vertices_292), (true, vertices_548), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_397) then 16 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_60) then 17 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_304) then 12 else
  0
cert_priority
cert_nodeAtPriority_2 0 449 1 38 2 134 3 262 518 98 290 322 386 524 292 548 304 707 397 60 345 665 625
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
cert_coverFacet 2 294
cert_cover_2 2 1 0 4 7 38 294 3
cert_coverFacet 3 390
cert_cover_2 3 1 0 6 7 134 390 3
cert_coverFacet 4 370
cert_cover_5 4 3 0 3 4 5 98 370 1
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 316
cert_cover_5 6 1 1 2 3 7 60 316 3
cert_coverFacet 7 572
cert_cover_5 7 1 1 2 3 8 60 572 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0717

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m14e10q1_0719.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0719

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 613, 837, 121, 793, 681, 790, 678, 198, 326, 666, 210, 236, 216, 581, 25, 41, 521, 81, 273, 97, 545, 321, 769, 70, 134, 262, 518, 82, 146, 274, 530, 194, 322, 642, 100, 164, 548, 196, 324, 772, 88, 152, 536, 104, 168, 200, 648, 208, 784, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_613, vertices_837, vertices_121, vertices_793, vertices_681, vertices_790, vertices_678, vertices_198, vertices_326, vertices_666, vertices_210, vertices_236, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_581, vertices_25, vertices_41, vertices_521, vertices_81, vertices_273, vertices_97, vertices_545, vertices_321, vertices_769, vertices_70, vertices_134, vertices_262, vertices_518, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_642, vertices_100, vertices_164, vertices_548, vertices_196, vertices_324, vertices_772, vertices_88, vertices_152, vertices_536, vertices_104, vertices_168, vertices_200, vertices_648, vertices_208, vertices_784, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_613), (false, vertices_837), (false, vertices_121), (false, vertices_793), (false, vertices_681), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_146), (true, vertices_530), (true, vertices_194), (true, vertices_642), (true, vertices_164), (true, vertices_196), (true, vertices_152), (true, vertices_200), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 14 else
  if p.val = (false, vertices_613) then 16 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_208) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
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
cert_row_4 0 0 1 3 7 8 790 262 2
cert_row_4 1 0 2 3 6 8 666 146 1
cert_row_4 2 0 1 4 6 8 678 134 2
cert_row_4 3 1 2 4 5 6 236 100 1
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 262 790 2
cert_coverFacet 1 678
cert_cover_5 1 2 0 1 4 6 134 678 2
cert_coverFacet 2 198
cert_cover_2 2 1 0 5 6 70 198 3
cert_coverFacet 3 326
cert_cover_2 3 1 0 5 7 70 326 3
cert_coverFacet 4 666
cert_cover_5 4 1 0 2 3 6 146 666 1
cert_coverFacet 5 210
cert_cover_2 5 3 0 5 6 82 210 3
cert_coverFacet 6 236
cert_cover_5 6 3 1 2 4 5 100 236 1
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0719

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m14e10q1_0721.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0721

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 213, 277, 421, 601, 961, 94, 110, 278, 294, 570, 930, 740, 616, 21, 133, 261, 81, 273, 529, 193, 577, 385, 769, 78, 22, 38, 262, 26, 42, 274, 530, 290, 546, 770, 84, 276, 100, 164, 292, 196, 88, 536, 104, 552, 584, 608, 416, 672, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_213, vertices_277, vertices_421, vertices_601, vertices_961, vertices_94, vertices_110, vertices_278, vertices_294, vertices_570, vertices_930, vertices_740, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_81, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_769, vertices_78, vertices_22, vertices_38, vertices_262, vertices_26, vertices_42, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_84, vertices_276, vertices_100, vertices_164, vertices_292, vertices_196, vertices_88, vertices_536, vertices_104, vertices_552, vertices_584, vertices_608, vertices_416, vertices_672, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_213), (false, vertices_277), (false, vertices_421), (false, vertices_601), (false, vertices_961), (true, vertices_78), (true, vertices_22), (true, vertices_38), (true, vertices_262), (true, vertices_26), (true, vertices_42), (true, vertices_290), (true, vertices_546), (true, vertices_100), (true, vertices_104), (true, vertices_552), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_421) then 18 else
  if p.val = (false, vertices_601) then 20 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_78) then 15 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 26 3
cert_row_2 1 0 1 2 5 78
cert_row_4 2 0 4 6 7 8 930 290 2
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 3 78 94 3
cert_coverFacet 1 110
cert_cover_5 1 1 0 1 2 4 78 110 3
cert_coverFacet 2 278
cert_cover_2 2 1 0 3 7 22 278 3
cert_coverFacet 3 294
cert_cover_2 3 1 0 4 7 38 294 3
cert_coverFacet 4 570
cert_cover_5 4 0 0 2 3 4 26 570 3
cert_coverFacet 5 930
cert_cover_5 5 2 0 4 6 7 290 930 2
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 100 740 3
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0721

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m14e10q1_0723.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0723

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 397, 213, 837, 625, 401, 782, 570, 170, 394, 242, 402, 684, 740, 69, 133, 261, 81, 145, 273, 529, 577, 385, 769, 42, 138, 266, 522, 50, 146, 274, 530, 162, 386, 770, 140, 268, 524, 676, 196, 580, 772, 168, 552, 392, 112, 560, 208, 400, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_397, vertices_213, vertices_837, vertices_625, vertices_401, vertices_782, vertices_570, vertices_170, vertices_394, vertices_242, vertices_402, vertices_684, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_81, vertices_145, vertices_273, vertices_529, vertices_577, vertices_385, vertices_769, vertices_42, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_386, vertices_770, vertices_140, vertices_268, vertices_524, vertices_676, vertices_196, vertices_580, vertices_772, vertices_168, vertices_552, vertices_392, vertices_112, vertices_560, vertices_208, vertices_400, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_397), (false, vertices_213), (false, vertices_837), (false, vertices_625), (false, vertices_401), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_162), (true, vertices_386), (true, vertices_524), (true, vertices_676), (true, vertices_168), (true, vertices_552), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 15 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_397) then 16 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_162) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_676) then 20 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_224) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_676), by decide +kernel⟩
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
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_2 1 1 4 6 8 676
cert_row_4 2 0 2 3 4 8 570 42 2
cert_row_4 3 0 3 4 5 6 242 50 3
cert_rows
cert_pivot_2 7 1 2 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 570
cert_cover_5 1 2 0 2 3 4 42 570 2
cert_coverFacet 2 170
cert_cover_2 2 2 0 4 6 42 170 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 242
cert_cover_5 4 3 0 3 4 5 50 242 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 684
cert_cover_5 6 1 1 2 4 6 140 684 2
cert_coverFacet 7 740
cert_cover_5 7 1 1 4 5 6 676 740 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0723

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m14e10q1_0733.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0733

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 589, 341, 805, 233, 481, 790, 426, 650, 466, 658, 802, 596, 728, 69, 261, 517, 41, 73, 521, 225, 289, 545, 321, 42, 138, 522, 146, 274, 530, 290, 546, 386, 642, 770, 84, 276, 532, 580, 772, 168, 200, 584, 648, 208, 336, 592, 656, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_589, vertices_341, vertices_805, vertices_233, vertices_481, vertices_790, vertices_426, vertices_650, vertices_466, vertices_658, vertices_802, vertices_596, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_41, vertices_73, vertices_521, vertices_225, vertices_289, vertices_545, vertices_321, vertices_42, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_84, vertices_276, vertices_532, vertices_580, vertices_772, vertices_168, vertices_200, vertices_584, vertices_648, vertices_208, vertices_336, vertices_592, vertices_656, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_589), (false, vertices_341), (false, vertices_805), (false, vertices_233), (false, vertices_481), (true, vertices_138), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_532), (true, vertices_648), (true, vertices_208), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 20 21 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 14 else
  if p.val = (false, vertices_589) then 16 else
  if p.val = (false, vertices_341) then 17 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_656) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_4 1 0 2 4 6 7 426 42 3
cert_row_4 2 0 3 5 6 7 466 146 2
cert_row_4 3 2 3 5 6 8 728 200 1
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 426
cert_cover_5 1 1 0 2 4 6 42 426 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 466
cert_cover_5 3 2 0 3 5 6 146 466 2
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 728
cert_cover_5 7 3 2 3 5 6 200 728 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0733

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m14e10q1_0752.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0752

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 805, 233, 841, 625, 417, 782, 566, 278, 218, 602, 402, 436, 240, 73, 137, 265, 97, 161, 289, 545, 577, 385, 769, 22, 262, 518, 90, 138, 266, 522, 146, 274, 530, 386, 52, 276, 292, 548, 772, 200, 584, 776, 112, 176, 560, 208, 592, 400, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_805, vertices_233, vertices_841, vertices_625, vertices_417, vertices_782, vertices_566, vertices_278, vertices_218, vertices_602, vertices_402, vertices_436, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_97, vertices_161, vertices_289, vertices_545, vertices_577, vertices_385, vertices_769, vertices_22, vertices_262, vertices_518, vertices_90, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_52, vertices_276, vertices_292, vertices_548, vertices_772, vertices_200, vertices_584, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_592, vertices_400, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_805), (false, vertices_233), (false, vertices_841), (false, vertices_625), (false, vertices_417), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_90), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_52), (true, vertices_276), (true, vertices_176), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_90) then 15 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
cert_priority
cert_nodeAtPriority_37 417 22 262 518 522 146 274 530 52 276 176 208 400 395 90 805 233 841 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 2 7 8 782 262 2
cert_row_4 2 0 1 3 4 8 566 22 3
cert_row_4 3 1 3 4 6 7 436 52 3
cert_rows
cert_pivot_2 5 2 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 262 782 2
cert_coverFacet 1 566
cert_cover_5 1 2 0 1 3 4 22 566 3
cert_coverFacet 2 278
cert_cover_2 2 1 0 3 7 22 278 3
cert_coverFacet 3 218
cert_cover_5 3 0 0 2 3 6 90 218 3
cert_coverFacet 4 602
cert_cover_5 4 0 0 2 3 8 90 602 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 52 436 3
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0752

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m14e10q1_0755.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0755

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 789, 121, 281, 689, 865, 662, 838, 390, 618, 682, 394, 412, 184, 25, 73, 265, 49, 273, 529, 97, 545, 321, 769, 134, 262, 518, 554, 74, 138, 266, 322, 578, 386, 642, 148, 276, 532, 388, 772, 56, 152, 280, 104, 168, 392, 176, 656, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_789, vertices_121, vertices_281, vertices_689, vertices_865, vertices_662, vertices_838, vertices_390, vertices_618, vertices_682, vertices_394, vertices_412, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_49, vertices_273, vertices_529, vertices_97, vertices_545, vertices_321, vertices_769, vertices_134, vertices_262, vertices_518, vertices_554, vertices_74, vertices_138, vertices_266, vertices_322, vertices_578, vertices_386, vertices_642, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_56, vertices_152, vertices_280, vertices_104, vertices_168, vertices_392, vertices_176, vertices_656, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_789), (false, vertices_121), (false, vertices_281), (false, vertices_689), (false, vertices_865), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_554), (true, vertices_138), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_388), (true, vertices_152), (true, vertices_168), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (false, vertices_865) then 23 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_554) then 15 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_392) then 12 else
  0
cert_priority
cert_nodeAtPriority_49 281 134 262 518 138 578 386 642 148 388 152 168 392 331 554 789 121 689 865
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 8 554
cert_row_4 1 0 1 5 7 8 838 262 2
cert_row_4 2 0 1 3 6 8 662 134 2
cert_row_4 3 1 2 3 6 7 412 148 1
cert_rows
cert_pivot_2 4 5 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 2 0 1 3 6 134 662 2
cert_coverFacet 1 838
cert_cover_5 1 1 0 1 5 7 262 838 2
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 618
cert_cover_5 3 0 0 2 4 5 554 618 3
cert_coverFacet 4 682
cert_cover_5 4 0 0 2 4 6 554 682 3
cert_coverFacet 5 394
cert_cover_2 5 2 0 6 7 138 394 3
cert_coverFacet 6 412
cert_cover_5 6 3 1 2 3 6 148 412 1
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0755

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m14e10q1_0760.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0760

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 173, 333, 901, 569, 793, 710, 218, 626, 178, 204, 852, 184, 344, 13, 133, 261, 537, 41, 265, 161, 545, 641, 769, 50, 82, 146, 162, 546, 194, 578, 642, 76, 140, 196, 324, 580, 644, 772, 56, 88, 152, 280, 168, 200, 328, 176, 560, 336, 592, 784]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_173, vertices_333, vertices_901, vertices_569, vertices_793, vertices_710, vertices_218, vertices_626, vertices_178, vertices_204, vertices_852, vertices_184, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_537, vertices_41, vertices_265, vertices_161, vertices_545, vertices_641, vertices_769, vertices_50, vertices_82, vertices_146, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_76, vertices_140, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_168, vertices_200, vertices_328, vertices_176, vertices_560, vertices_336, vertices_592, vertices_784] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_173), (false, vertices_333), (false, vertices_901), (false, vertices_569), (false, vertices_793), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_578), (true, vertices_196), (true, vertices_580), (true, vertices_88), (true, vertices_152), (true, vertices_200), (true, vertices_176), (true, vertices_336), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_173) then 16 else
  if p.val = (false, vertices_333) then 17 else
  if p.val = (false, vertices_901) then 18 else
  if p.val = (false, vertices_569) then 20 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_592) then 12 else
  0
cert_priority
cert_nodeAtPriority 0 50 1 82 2 146 194 578 196 580 88 152 200 176 336 592 675 173 333 901 569 793
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 6 218 82 1
cert_row_4 1 0 1 5 6 8 710 194 1
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 1 3 5 7 8 852 324 1
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 1 0 1 5 6 194 710 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 5 82 218 1
cert_coverFacet 2 626
cert_cover_5 2 2 0 3 4 5 50 626 3
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 204
cert_cover_2 4 2 1 5 6 76 204 3
cert_coverFacet 5 852
cert_cover_5 5 3 1 3 5 7 324 852 1
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0760

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m14e10q1_0763.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0763

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 91, 139, 339, 653, 805, 793, 234, 866, 418, 740, 420, 728, 848, 11, 83, 131, 259, 133, 261, 517, 25, 137, 521, 273, 769, 74, 138, 98, 162, 290, 322, 386, 164, 292, 548, 388, 644, 88, 536, 200, 648, 336, 592, 784, 224, 608, 416, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_91, vertices_139, vertices_339, vertices_653, vertices_805, vertices_793, vertices_234, vertices_866, vertices_418, vertices_740, vertices_420, vertices_728, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_83, vertices_131, vertices_259, vertices_133, vertices_261, vertices_517, vertices_25, vertices_137, vertices_521, vertices_273, vertices_769, vertices_74, vertices_138, vertices_98, vertices_162, vertices_290, vertices_322, vertices_386, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_88, vertices_536, vertices_200, vertices_648, vertices_336, vertices_592, vertices_784, vertices_224, vertices_608, vertices_416, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_91), (false, vertices_139), (false, vertices_339), (false, vertices_653), (false, vertices_805), (false, vertices_793), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_164), (true, vertices_200), (true, vertices_592), (true, vertices_224), (true, vertices_608), (true, vertices_416), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_139) then 0 else
  if p.val = (false, vertices_339) then 15 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
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
cert_row_4 0 0 4 5 7 8 866 98 3
cert_row_4 1 0 2 4 5 6 234 74 2
cert_row_4 2 1 4 5 6 8 740 164 2
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 234
cert_cover_5 0 1 0 2 4 5 74 234 2
cert_coverFacet 1 866
cert_cover_5 1 0 0 4 5 7 98 866 3
cert_coverFacet 2 418
cert_cover_2 2 4 0 6 7 162 418 3
cert_coverFacet 3 740
cert_cover_5 3 2 1 4 5 6 164 740 2
cert_coverFacet 4 420
cert_cover_2 4 4 1 6 7 164 420 3
cert_coverFacet 5 728
cert_cover_5 5 3 2 3 5 6 88 728 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0763

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m14e10q1_0780.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0780

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 589, 329, 777, 625, 913, 481, 782, 406, 230, 614, 562, 786, 460, 73, 265, 521, 49, 145, 529, 97, 161, 321, 577, 385, 769, 102, 134, 262, 518, 50, 146, 274, 530, 162, 546, 770, 76, 268, 524, 196, 580, 388, 328, 776, 560, 400, 784, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_589, vertices_329, vertices_777, vertices_625, vertices_913, vertices_481, vertices_782, vertices_406, vertices_230, vertices_614, vertices_562, vertices_786, vertices_460] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_49, vertices_145, vertices_529, vertices_97, vertices_161, vertices_321, vertices_577, vertices_385, vertices_769, vertices_102, vertices_134, vertices_262, vertices_518, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_770, vertices_76, vertices_268, vertices_524, vertices_196, vertices_580, vertices_388, vertices_328, vertices_776, vertices_560, vertices_400, vertices_784, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_589), (false, vertices_329), (false, vertices_777), (false, vertices_625), (false, vertices_913), (false, vertices_481), (true, vertices_102), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_770), (true, vertices_268), (true, vertices_196), (true, vertices_388)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 18 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 13 else
  if p.val = (false, vertices_589) then 16 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (false, vertices_625) then 19 else
  if p.val = (false, vertices_913) then 20 else
  if p.val = (false, vertices_481) then 22 else
  if p.val = (true, vertices_102) then 14 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_388) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 5 102
cert_row_4 1 0 1 2 7 8 782 262 2
cert_row_4 2 0 1 3 6 7 406 134 2
cert_row_4 3 1 2 5 6 7 460 76 3
cert_rows
cert_pivot_2 4 8 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 262 782 2
cert_coverFacet 1 406
cert_cover_5 1 2 0 1 3 6 134 406 2
cert_coverFacet 2 230
cert_cover_5 2 0 0 1 4 6 102 230 3
cert_coverFacet 3 614
cert_cover_5 3 0 0 1 4 8 102 614 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 460
cert_cover_5 6 3 1 2 5 6 76 460 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0780

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m14e10q1_0781.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0781

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 589, 677, 453, 433, 833, 542, 314, 842, 562, 220, 660, 472, 688, 69, 133, 517, 161, 289, 545, 321, 577, 385, 769, 26, 266, 522, 50, 530, 290, 546, 770, 28, 76, 524, 148, 532, 196, 644, 216, 280, 328, 584, 176, 304, 560, 400, 656, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_589, vertices_677, vertices_453, vertices_433, vertices_833, vertices_542, vertices_314, vertices_842, vertices_562, vertices_220, vertices_660, vertices_472, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_769, vertices_26, vertices_266, vertices_522, vertices_50, vertices_530, vertices_290, vertices_546, vertices_770, vertices_28, vertices_76, vertices_524, vertices_148, vertices_532, vertices_196, vertices_644, vertices_216, vertices_280, vertices_328, vertices_584, vertices_176, vertices_304, vertices_560, vertices_400, vertices_656, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_589), (false, vertices_677), (false, vertices_453), (false, vertices_433), (false, vertices_833), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_530), (true, vertices_28), (true, vertices_148), (true, vertices_532), (true, vertices_216), (true, vertices_280), (true, vertices_328), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_589) then 16 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_216) then 20 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_656) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 5 6 216
cert_row_4 1 0 1 2 3 8 542 26 1
cert_row_4 2 0 2 3 4 7 314 26 3
cert_row_4 3 0 2 5 7 8 842 266 2
cert_rows
cert_pivot_2 6 1 3 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 1 0 1 2 3 26 542 1
cert_coverFacet 1 314
cert_cover_5 1 2 0 2 3 4 26 314 3
cert_coverFacet 2 842
cert_cover_5 2 3 0 2 5 7 266 842 2
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 220
cert_cover_5 4 0 1 2 3 5 28 220 3
cert_coverFacet 5 660
cert_cover_2 5 3 1 6 8 148 660 3
cert_coverFacet 6 472
cert_cover_5 6 0 2 3 5 7 216 472 3
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0781

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m14e10q1_0782.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0782

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 333, 789, 709, 121, 625, 902, 570, 170, 394, 786, 738, 452, 488, 69, 261, 517, 25, 73, 265, 113, 273, 529, 577, 26, 42, 138, 266, 274, 530, 162, 546, 386, 642, 770, 196, 324, 388, 644, 772, 56, 104, 168, 328, 392, 560, 784, 224, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_333, vertices_789, vertices_709, vertices_121, vertices_625, vertices_902, vertices_570, vertices_170, vertices_394, vertices_786, vertices_738, vertices_452, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_25, vertices_73, vertices_265, vertices_113, vertices_273, vertices_529, vertices_577, vertices_26, vertices_42, vertices_138, vertices_266, vertices_274, vertices_530, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_56, vertices_104, vertices_168, vertices_328, vertices_392, vertices_560, vertices_784, vertices_224, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_333), (false, vertices_789), (false, vertices_709), (false, vertices_121), (false, vertices_625), (true, vertices_42), (true, vertices_138), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_388), (true, vertices_168), (true, vertices_392), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 14 else
  if p.val = (false, vertices_333) then 16 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_121) then 21 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_4 1 0 2 3 4 8 570 26 3
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 570
cert_cover_5 1 1 0 2 3 4 26 570 3
cert_coverFacet 2 170
cert_cover_2 2 2 0 4 6 42 170 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 162 738 2
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0782

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m14e10q1_0789.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0789

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 555, 787, 451, 229, 929, 542, 346, 284, 108, 684, 332, 788, 964, 43, 67, 259, 515, 97, 161, 545, 193, 385, 769, 26, 74, 522, 274, 530, 322, 28, 44, 76, 268, 524, 276, 532, 100, 164, 196, 324, 644, 772, 280, 104, 552, 328, 784, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_555, vertices_787, vertices_451, vertices_229, vertices_929, vertices_542, vertices_346, vertices_284, vertices_108, vertices_684, vertices_332, vertices_788, vertices_964] (by decide +kernel)
  polygons := literalFinset [vertices_43, vertices_67, vertices_259, vertices_515, vertices_97, vertices_161, vertices_545, vertices_193, vertices_385, vertices_769, vertices_26, vertices_74, vertices_522, vertices_274, vertices_530, vertices_322, vertices_28, vertices_44, vertices_76, vertices_268, vertices_524, vertices_276, vertices_532, vertices_100, vertices_164, vertices_196, vertices_324, vertices_644, vertices_772, vertices_280, vertices_104, vertices_552, vertices_328, vertices_784, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_555), (false, vertices_787), (false, vertices_451), (false, vertices_229), (false, vertices_929), (true, vertices_26), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_532), (true, vertices_324), (true, vertices_644), (true, vertices_772), (true, vertices_280), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 13 15 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 16 else
  if p.val = (false, vertices_555) then 17 else
  if p.val = (false, vertices_787) then 19 else
  if p.val = (false, vertices_451) then 20 else
  if p.val = (false, vertices_229) then 14 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_28) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_328) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
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
cert_row_4 0 1 2 4 6 8 684 44 3
cert_row_4 1 1 5 6 7 8 964 196 3
cert_row_4 2 0 1 2 3 8 542 26 1
cert_row_4 3 0 2 3 5 7 346 26 3
cert_rows
cert_pivot_2 4 6 1 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 2 0 1 2 3 26 542 1
cert_coverFacet 1 346
cert_cover_5 1 3 0 2 3 5 26 346 3
cert_coverFacet 2 284
cert_cover_2 2 2 1 3 7 28 284 3
cert_coverFacet 3 108
cert_cover_2 3 2 1 4 5 44 108 3
cert_coverFacet 4 684
cert_cover_5 4 0 1 2 4 6 44 684 3
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 964
cert_cover_5 7 1 1 5 6 7 196 964 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0789

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m14e10q1_0800.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0800

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 397, 345, 665, 625, 897, 654, 614, 294, 390, 370, 898, 316, 572, 25, 137, 265, 81, 529, 321, 577, 385, 641, 769, 38, 134, 262, 518, 98, 290, 322, 578, 386, 642, 770, 60, 140, 268, 524, 292, 548, 388, 280, 536, 648, 112, 304, 560, 336, 608, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_397, vertices_345, vertices_665, vertices_625, vertices_897, vertices_654, vertices_614, vertices_294, vertices_390, vertices_370, vertices_898, vertices_316, vertices_572] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_81, vertices_529, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_38, vertices_134, vertices_262, vertices_518, vertices_98, vertices_290, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_60, vertices_140, vertices_268, vertices_524, vertices_292, vertices_548, vertices_388, vertices_280, vertices_536, vertices_648, vertices_112, vertices_304, vertices_560, vertices_336, vertices_608, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_397), (false, vertices_345), (false, vertices_665), (false, vertices_625), (false, vertices_897), (true, vertices_38), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_98), (true, vertices_290), (true, vertices_386), (true, vertices_642), (true, vertices_60), (true, vertices_524), (true, vertices_292), (true, vertices_548), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_397) then 16 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_60) then 17 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_304) then 12 else
  0
cert_priority
cert_nodeAtPriority_2 0 897 1 38 2 134 3 262 518 98 290 386 642 524 292 548 304 835 397 60 345 665 625
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
cert_coverFacet 2 294
cert_cover_2 2 1 0 4 7 38 294 3
cert_coverFacet 3 390
cert_cover_2 3 1 0 6 7 134 390 3
cert_coverFacet 4 370
cert_cover_5 4 3 0 3 4 5 98 370 1
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 316
cert_cover_5 6 1 1 2 3 7 60 316 3
cert_coverFacet 7 572
cert_cover_5 7 1 1 2 3 8 60 572 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0800

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m14e10q1_0811.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0811

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 333, 405, 709, 817, 833, 398, 654, 570, 362, 306, 402, 620, 864, 69, 133, 261, 145, 273, 529, 321, 577, 641, 769, 142, 42, 266, 522, 50, 146, 274, 530, 290, 386, 642, 76, 268, 524, 580, 388, 644, 104, 552, 328, 304, 560, 400, 352, 608, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_333, vertices_405, vertices_709, vertices_817, vertices_833, vertices_398, vertices_654, vertices_570, vertices_362, vertices_306, vertices_402, vertices_620, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_145, vertices_273, vertices_529, vertices_321, vertices_577, vertices_641, vertices_769, vertices_142, vertices_42, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_530, vertices_290, vertices_386, vertices_642, vertices_76, vertices_268, vertices_524, vertices_580, vertices_388, vertices_644, vertices_104, vertices_552, vertices_328, vertices_304, vertices_560, vertices_400, vertices_352, vertices_608, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_333), (false, vertices_405), (false, vertices_709), (false, vertices_817), (false, vertices_833), (true, vertices_142), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_290), (true, vertices_386), (true, vertices_524), (true, vertices_104), (true, vertices_552), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_333) then 17 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_817) then 22 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_142) then 15 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_142), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 6 142
cert_row_4 1 0 2 3 4 8 570 42 2
cert_row_4 2 0 2 4 5 7 362 42 3
cert_row_4 3 1 2 4 5 8 620 76 2
cert_rows
cert_pivot_2 6 3 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 7 142 398 3
cert_coverFacet 1 654
cert_cover_5 1 0 0 1 2 8 142 654 3
cert_coverFacet 2 570
cert_cover_5 2 1 0 2 3 4 42 570 2
cert_coverFacet 3 362
cert_cover_5 3 2 0 2 4 5 42 362 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 76 620 2
cert_coverFacet 7 864
cert_cover_2 7 5 4 7 8 352 864 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0811

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m14e10q1_0813.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0813

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 551, 333, 653, 617, 369, 398, 662, 626, 306, 402, 456, 712, 976, 39, 13, 261, 517, 73, 521, 97, 289, 545, 321, 134, 262, 518, 50, 146, 274, 530, 290, 546, 386, 140, 268, 644, 200, 328, 584, 392, 648, 112, 304, 336, 592, 400, 656, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_551, vertices_333, vertices_653, vertices_617, vertices_369, vertices_398, vertices_662, vertices_626, vertices_306, vertices_402, vertices_456, vertices_712, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_39, vertices_13, vertices_261, vertices_517, vertices_73, vertices_521, vertices_97, vertices_289, vertices_545, vertices_321, vertices_134, vertices_262, vertices_518, vertices_50, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_140, vertices_268, vertices_644, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_112, vertices_304, vertices_336, vertices_592, vertices_400, vertices_656, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_551), (false, vertices_333), (false, vertices_653), (false, vertices_617), (false, vertices_369), (true, vertices_134), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_200), (true, vertices_392), (true, vertices_592), (true, vertices_400), (true, vertices_656), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 14 else
  if p.val = (false, vertices_551) then 15 else
  if p.val = (false, vertices_333) then 17 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_4 1 0 1 3 6 8 662 134 2
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 3 5 6 7 8 976 336 2
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 662
cert_cover_5 1 1 0 1 3 6 134 662 2
cert_coverFacet 2 626
cert_cover_5 2 2 0 3 4 5 50 626 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 456
cert_cover_2 5 5 2 6 7 200 456 3
cert_coverFacet 6 712
cert_cover_2 6 5 2 6 8 200 712 3
cert_coverFacet 7 976
cert_cover_5 7 3 3 5 6 7 336 976 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0813

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m14e11q1_0001.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q1_0001

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 587, 563, 451, 541, 333, 389, 242, 610, 812, 916, 488, 616, 944, 19, 67, 131, 515, 13, 21, 133, 261, 73, 521, 529, 321, 385, 50, 146, 98, 546, 194, 578, 268, 524, 148, 532, 388, 772, 104, 296, 552, 328, 584, 176, 560, 912, 224, 608, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_587, vertices_563, vertices_451, vertices_541, vertices_333, vertices_389, vertices_242, vertices_610, vertices_812, vertices_916, vertices_488, vertices_616, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_131, vertices_515, vertices_13, vertices_21, vertices_133, vertices_261, vertices_73, vertices_521, vertices_529, vertices_321, vertices_385, vertices_50, vertices_146, vertices_98, vertices_546, vertices_194, vertices_578, vertices_268, vertices_524, vertices_148, vertices_532, vertices_388, vertices_772, vertices_104, vertices_296, vertices_552, vertices_328, vertices_584, vertices_176, vertices_560, vertices_912, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_587), (false, vertices_563), (false, vertices_451), (false, vertices_541), (false, vertices_333), (false, vertices_389), (true, vertices_98), (true, vertices_772), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_176), (true, vertices_912), (true, vertices_224), (true, vertices_608), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 11 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 12 else
  if p.val = (false, vertices_587) then 16 else
  if p.val = (false, vertices_563) then 17 else
  if p.val = (false, vertices_451) then 18 else
  if p.val = (false, vertices_541) then 13 else
  if p.val = (false, vertices_333) then 14 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_772) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_912) then 21 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_912), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 6 242 50 3
cert_row_2 1 3 6 7 8 912
cert_row_4 2 1 2 4 7 8 812 268 2
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 242
cert_cover_5 0 0 0 3 4 5 50 242 3
cert_coverFacet 1 610
cert_cover_2 1 4 0 5 8 98 610 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 268 812 2
cert_coverFacet 3 916
cert_cover_5 3 1 1 3 6 7 148 916 3
cert_coverFacet 4 488
cert_cover_5 4 3 2 4 5 6 104 488 3
cert_coverFacet 5 616
cert_cover_2 5 4 2 5 8 104 616 3
cert_coverFacet 6 944
cert_cover_5 6 1 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q1_0001

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m14e11q1_0002.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q1_0002

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 283, 595, 419, 93, 397, 165, 581, 818, 236, 612, 728, 920, 992, 19, 35, 259, 515, 13, 37, 69, 133, 517, 25, 265, 81, 161, 577, 385, 274, 530, 290, 546, 76, 140, 100, 164, 548, 580, 88, 664, 280, 200, 392, 592, 784, 224, 608, 416, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_283, vertices_595, vertices_419, vertices_93, vertices_397, vertices_165, vertices_581, vertices_818, vertices_236, vertices_612, vertices_728, vertices_920, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_515, vertices_13, vertices_37, vertices_69, vertices_133, vertices_517, vertices_25, vertices_265, vertices_81, vertices_161, vertices_577, vertices_385, vertices_274, vertices_530, vertices_290, vertices_546, vertices_76, vertices_140, vertices_100, vertices_164, vertices_548, vertices_580, vertices_88, vertices_664, vertices_280, vertices_200, vertices_392, vertices_592, vertices_784, vertices_224, vertices_608, vertices_416, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_283), (false, vertices_595), (false, vertices_419), (false, vertices_93), (false, vertices_397), (false, vertices_165), (false, vertices_581), (true, vertices_100), (true, vertices_664), (true, vertices_200), (true, vertices_784), (true, vertices_224), (true, vertices_608), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 10 18 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 11 else
  if p.val = (false, vertices_283) then 15 else
  if p.val = (false, vertices_595) then 16 else
  if p.val = (false, vertices_419) then 17 else
  if p.val = (false, vertices_93) then 12 else
  if p.val = (false, vertices_397) then 13 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_581) then 1 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_664) then 19 else
  if p.val = (true, vertices_200) then 3 else
  if p.val = (true, vertices_784) then 4 else
  if p.val = (true, vertices_224) then 5 else
  if p.val = (true, vertices_608) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 7 8 818 274 2
cert_row_2 1 2 3 6 8 664
cert_row_4 2 1 2 4 5 6 236 76 2
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 3 1 4
cert_heightProof 4
cert_coverFacet 0 818
cert_cover_5 0 0 0 3 4 7 274 818 2
cert_coverFacet 1 236
cert_cover_5 1 2 1 2 4 5 76 236 2
cert_coverFacet 2 612
cert_cover_2 2 4 1 5 8 100 612 3
cert_coverFacet 3 728
cert_cover_5 3 1 2 3 5 6 88 728 3
cert_coverFacet 4 920
cert_cover_5 4 1 2 3 6 7 664 920 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q1_0002

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m14e11q1_0008.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q1_0008

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 171, 659, 99, 157, 109, 789, 482, 962, 284, 844, 376, 184, 944, 35, 67, 131, 515, 13, 21, 69, 517, 41, 137, 145, 529, 97, 98, 162, 450, 578, 642, 28, 76, 268, 276, 580, 772, 56, 152, 280, 104, 168, 328, 176, 304, 656, 784, 352, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_171, vertices_659, vertices_99, vertices_157, vertices_109, vertices_789, vertices_482, vertices_962, vertices_284, vertices_844, vertices_376, vertices_184, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_131, vertices_515, vertices_13, vertices_21, vertices_69, vertices_517, vertices_41, vertices_137, vertices_145, vertices_529, vertices_97, vertices_98, vertices_162, vertices_450, vertices_578, vertices_642, vertices_28, vertices_76, vertices_268, vertices_276, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_104, vertices_168, vertices_328, vertices_176, vertices_304, vertices_656, vertices_784, vertices_352, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_171), (false, vertices_659), (false, vertices_99), (false, vertices_157), (false, vertices_109), (false, vertices_789), (true, vertices_450), (true, vertices_268), (true, vertices_56), (true, vertices_280), (true, vertices_328), (true, vertices_176), (true, vertices_304), (true, vertices_352), (true, vertices_416), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 11 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 16 else
  if p.val = (false, vertices_171) then 12 else
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_99) then 0 else
  if p.val = (false, vertices_157) then 13 else
  if p.val = (false, vertices_109) then 14 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (true, vertices_450) then 18 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_56) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_99), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_450), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 6 7 450
cert_row_4 1 1 2 5 7 8 844 76 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 482
cert_cover_5 0 0 0 4 5 6 98 482 3
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 8 450 962 3
cert_coverFacet 2 284
cert_cover_2 2 2 1 3 7 28 284 3
cert_coverFacet 3 844
cert_cover_5 3 1 1 2 5 7 76 844 3
cert_coverFacet 4 376
cert_cover_5 4 2 2 3 4 5 56 376 3
cert_coverFacet 5 184
cert_cover_2 5 3 2 4 6 56 184 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q1_0008

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m14e11q1_0010.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q1_0010

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 563, 419, 541, 301, 389, 617, 362, 114, 466, 908, 724, 968, 624, 19, 35, 131, 13, 21, 133, 261, 41, 521, 529, 289, 545, 385, 50, 82, 146, 98, 290, 322, 386, 268, 524, 148, 532, 388, 644, 104, 296, 328, 584, 904, 112, 560, 208, 592, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_563, vertices_419, vertices_541, vertices_301, vertices_389, vertices_617, vertices_362, vertices_114, vertices_466, vertices_908, vertices_724, vertices_968, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_13, vertices_21, vertices_133, vertices_261, vertices_41, vertices_521, vertices_529, vertices_289, vertices_545, vertices_385, vertices_50, vertices_82, vertices_146, vertices_98, vertices_290, vertices_322, vertices_386, vertices_268, vertices_524, vertices_148, vertices_532, vertices_388, vertices_644, vertices_104, vertices_296, vertices_328, vertices_584, vertices_904, vertices_112, vertices_560, vertices_208, vertices_592, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_563), (false, vertices_419), (false, vertices_541), (false, vertices_301), (false, vertices_389), (false, vertices_617), (true, vertices_82), (true, vertices_98), (true, vertices_322), (true, vertices_644), (true, vertices_328), (true, vertices_904), (true, vertices_112), (true, vertices_208), (true, vertices_592), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 12 else
  if p.val = (false, vertices_563) then 13 else
  if p.val = (false, vertices_419) then 14 else
  if p.val = (false, vertices_541) then 16 else
  if p.val = (false, vertices_301) then 17 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_904) then 20 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_904), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 7 362 98 1
cert_row_2 1 2 6 7 8 904
cert_row_4 2 0 3 5 6 7 466 82 3
cert_row_4 3 1 3 5 6 8 724 148 2
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 362
cert_cover_5 0 0 0 2 4 5 98 362 1
cert_coverFacet 1 114
cert_cover_2 1 3 0 4 5 50 114 3
cert_coverFacet 2 466
cert_cover_5 2 2 0 3 5 6 82 466 3
cert_coverFacet 3 908
cert_cover_5 3 1 1 2 6 7 268 908 2
cert_coverFacet 4 724
cert_cover_5 4 3 1 3 5 6 148 724 2
cert_coverFacet 5 968
cert_cover_5 5 1 2 5 6 7 328 968 2
cert_coverFacet 6 624
cert_cover_2 6 4 3 5 8 112 624 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q1_0010

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m14e11q2_0000.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0000

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 157, 589, 229, 905, 481, 62, 110, 538, 586, 370, 914, 436, 664, 13, 69, 133, 137, 521, 225, 321, 577, 385, 769, 46, 26, 74, 522, 50, 274, 530, 98, 322, 578, 770, 28, 76, 52, 148, 100, 164, 152, 536, 584, 648, 304, 400, 656, 352, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_157, vertices_589, vertices_229, vertices_905, vertices_481, vertices_62, vertices_110, vertices_538, vertices_586, vertices_370, vertices_914, vertices_436, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_133, vertices_137, vertices_521, vertices_225, vertices_321, vertices_577, vertices_385, vertices_769, vertices_46, vertices_26, vertices_74, vertices_522, vertices_50, vertices_274, vertices_530, vertices_98, vertices_322, vertices_578, vertices_770, vertices_28, vertices_76, vertices_52, vertices_148, vertices_100, vertices_164, vertices_152, vertices_536, vertices_584, vertices_648, vertices_304, vertices_400, vertices_656, vertices_352, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_157), (false, vertices_589), (false, vertices_229), (false, vertices_905), (false, vertices_481), (true, vertices_46), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_52), (true, vertices_536), (true, vertices_304), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 13 else
  if p.val = (false, vertices_157) then 16 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_905) then 19 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_46) then 14 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_656) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 3 4 5 7 370 50 3
cert_row_4 2 0 3 6 7 8 914 274 2
cert_row_4 3 1 3 4 6 7 436 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 46 62 3
cert_coverFacet 1 110
cert_cover_5 1 0 0 1 2 5 46 110 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 586
cert_cover_2 3 2 0 5 8 74 586 3
cert_coverFacet 4 370
cert_cover_5 4 1 0 3 4 5 50 370 3
cert_coverFacet 5 914
cert_cover_5 5 2 0 3 6 7 274 914 2
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 52 436 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0000

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m14e11q2_0001.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0001

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 341, 901, 313, 625, 929, 206, 678, 602, 426, 554, 460, 568, 344, 69, 261, 517, 49, 81, 273, 289, 545, 577, 897, 70, 134, 518, 42, 74, 138, 522, 162, 546, 578, 204, 324, 388, 644, 56, 88, 280, 536, 296, 552, 328, 392, 560, 336, 592, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_341, vertices_901, vertices_313, vertices_625, vertices_929, vertices_206, vertices_678, vertices_602, vertices_426, vertices_554, vertices_460, vertices_568, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_49, vertices_81, vertices_273, vertices_289, vertices_545, vertices_577, vertices_897, vertices_70, vertices_134, vertices_518, vertices_42, vertices_74, vertices_138, vertices_522, vertices_162, vertices_546, vertices_578, vertices_204, vertices_324, vertices_388, vertices_644, vertices_56, vertices_88, vertices_280, vertices_536, vertices_296, vertices_552, vertices_328, vertices_392, vertices_560, vertices_336, vertices_592, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_341), (false, vertices_901), (false, vertices_313), (false, vertices_625), (false, vertices_929), (true, vertices_134), (true, vertices_42), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_162), (true, vertices_546), (true, vertices_204), (true, vertices_88), (true, vertices_536), (true, vertices_552), (true, vertices_328), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 19 21 22 23 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 13 else
  if p.val = (false, vertices_341) then 15 else
  if p.val = (false, vertices_901) then 24 else
  if p.val = (false, vertices_313) then 18 else
  if p.val = (false, vertices_625) then 20 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_204) then 16 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_392) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 74 2
cert_row_2 1 1 2 5 6 204
cert_row_4 2 0 1 4 6 8 678 134 2
cert_row_4 3 0 2 4 6 7 426 42 3
cert_rows
cert_pivot_2 3 5 1 0
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 70 206 2
cert_coverFacet 1 678
cert_cover_5 1 2 0 1 4 6 134 678 2
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 5 74 602 2
cert_coverFacet 3 426
cert_cover_5 3 3 0 2 4 6 42 426 3
cert_coverFacet 4 554
cert_cover_2 4 2 0 4 8 42 554 3
cert_coverFacet 5 460
cert_cover_5 5 1 1 2 5 7 204 460 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0001

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m14e11q2_0002.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0002

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 653, 421, 185, 361, 841, 406, 662, 122, 306, 594, 866, 728, 432, 133, 261, 517, 41, 329, 137, 521, 161, 289, 769, 150, 262, 518, 50, 82, 274, 530, 98, 290, 578, 770, 388, 644, 56, 88, 152, 104, 584, 648, 176, 304, 592, 400, 656, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_653, vertices_421, vertices_185, vertices_361, vertices_841, vertices_406, vertices_662, vertices_122, vertices_306, vertices_594, vertices_866, vertices_728, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_329, vertices_137, vertices_521, vertices_161, vertices_289, vertices_769, vertices_150, vertices_262, vertices_518, vertices_50, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_578, vertices_770, vertices_388, vertices_644, vertices_56, vertices_88, vertices_152, vertices_104, vertices_584, vertices_648, vertices_176, vertices_304, vertices_592, vertices_400, vertices_656, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_653), (false, vertices_421), (false, vertices_185), (false, vertices_361), (false, vertices_841), (true, vertices_150), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_290), (true, vertices_578), (true, vertices_88), (true, vertices_304), (true, vertices_592), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_185) then 19 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (true, vertices_150) then 14 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_656) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_150), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 6 150
cert_row_4 1 0 4 5 7 8 866 98 3
cert_row_4 2 0 2 3 4 5 122 50 1
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 7 150 406 3
cert_coverFacet 1 662
cert_cover_5 1 0 0 1 3 8 150 662 3
cert_coverFacet 2 122
cert_cover_5 2 2 0 2 3 4 50 122 1
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 594
cert_cover_2 4 3 0 5 8 82 594 3
cert_coverFacet 5 866
cert_cover_5 5 1 0 4 5 7 98 866 3
cert_coverFacet 6 728
cert_cover_5 6 3 2 3 5 6 88 728 3
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0002

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m14e11q2_0003.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0003

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 285, 217, 329, 177, 817, 961, 30, 206, 310, 806, 710, 186, 844, 25, 73, 265, 49, 145, 273, 161, 545, 193, 321, 641, 769, 14, 22, 294, 198, 518, 26, 138, 50, 162, 546, 642, 28, 76, 268, 276, 580, 772, 152, 200, 328, 176, 304, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_285, vertices_217, vertices_329, vertices_177, vertices_817, vertices_961, vertices_30, vertices_206, vertices_310, vertices_806, vertices_710, vertices_186, vertices_844] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_49, vertices_145, vertices_273, vertices_161, vertices_545, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_22, vertices_294, vertices_198, vertices_518, vertices_26, vertices_138, vertices_50, vertices_162, vertices_546, vertices_642, vertices_28, vertices_76, vertices_268, vertices_276, vertices_580, vertices_772, vertices_152, vertices_200, vertices_328, vertices_176, vertices_304, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_285), (false, vertices_217), (false, vertices_329), (false, vertices_177), (false, vertices_817), (false, vertices_961), (true, vertices_14), (true, vertices_22), (true, vertices_294), (true, vertices_198), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_50), (true, vertices_76), (true, vertices_580), (true, vertices_772)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 21 11 14 16 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 17 else
  if p.val = (false, vertices_285) then 12 else
  if p.val = (false, vertices_217) then 13 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_177) then 1 else
  if p.val = (false, vertices_817) then 15 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_22) then 3 else
  if p.val = (true, vertices_294) then 18 else
  if p.val = (true, vertices_198) then 20 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_138) then 6 else
  if p.val = (true, vertices_50) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_772) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 16 => Sum.inl 4
  | 17 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_294), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(true, vertices_198), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 6 186 26 3
cert_row_2 1 0 1 5 6 198
cert_row_2 2 0 1 4 7 294
cert_row_4 3 1 2 5 7 8 844 76 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 206
cert_cover_5 1 1 0 1 2 5 14 206 3
cert_coverFacet 2 310
cert_cover_5 2 2 0 1 3 4 22 310 3
cert_coverFacet 3 806
cert_cover_5 3 2 0 1 4 8 294 806 3
cert_coverFacet 4 710
cert_cover_5 4 1 0 1 5 8 198 710 3
cert_coverFacet 5 186
cert_cover_5 5 0 0 2 3 4 26 186 3
cert_coverFacet 6 844
cert_cover_5 6 3 1 2 5 7 76 844 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0003

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m14e11q2_0004.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0004

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 115, 531, 643, 309, 913, 481, 590, 598, 906, 796, 236, 428, 116, 19, 67, 131, 515, 49, 273, 529, 97, 289, 193, 385, 641, 582, 74, 138, 522, 82, 530, 642, 172, 76, 268, 524, 52, 84, 276, 532, 100, 292, 200, 392, 776, 112, 784, 224, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_115, vertices_531, vertices_643, vertices_309, vertices_913, vertices_481, vertices_590, vertices_598, vertices_906, vertices_796, vertices_236, vertices_428, vertices_116] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_131, vertices_515, vertices_49, vertices_273, vertices_529, vertices_97, vertices_289, vertices_193, vertices_385, vertices_641, vertices_582, vertices_74, vertices_138, vertices_522, vertices_82, vertices_530, vertices_642, vertices_172, vertices_76, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_532, vertices_100, vertices_292, vertices_200, vertices_392, vertices_776, vertices_112, vertices_784, vertices_224, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_115), (false, vertices_531), (false, vertices_643), (false, vertices_309), (false, vertices_913), (false, vertices_481), (true, vertices_582), (true, vertices_522), (true, vertices_172), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_532), (true, vertices_100), (true, vertices_392), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 11 19 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_115) then 15 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_643) then 1 else
  if p.val = (false, vertices_309) then 18 else
  if p.val = (false, vertices_913) then 20 else
  if p.val = (false, vertices_481) then 22 else
  if p.val = (true, vertices_582) then 16 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_172) then 13 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_776) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_172), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_582), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 8 582
cert_row_2 1 1 2 4 6 172
cert_row_4 2 0 2 6 7 8 906 138 3
cert_row_4 3 1 2 3 7 8 796 268 2
cert_rows
cert_pivot_2 5 4 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 582 590 2
cert_coverFacet 1 598
cert_cover_5 1 0 0 1 3 5 582 598 2
cert_coverFacet 2 906
cert_cover_5 2 2 0 2 6 7 138 906 3
cert_coverFacet 3 796
cert_cover_5 3 3 1 2 3 7 268 796 2
cert_coverFacet 4 236
cert_cover_5 4 1 1 2 4 5 172 236 3
cert_coverFacet 5 428
cert_cover_5 5 1 1 2 4 7 172 428 3
cert_coverFacet 6 116
cert_cover_2 6 3 1 4 5 52 116 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0004

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m14e11q2_0005.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0005

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 653, 421, 837, 689, 785, 206, 454, 570, 346, 682, 418, 604, 848, 133, 261, 517, 49, 273, 529, 161, 289, 641, 769, 198, 26, 554, 74, 138, 50, 274, 162, 290, 322, 386, 76, 140, 524, 324, 580, 388, 88, 536, 648, 560, 336, 592, 784, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_653, vertices_421, vertices_837, vertices_689, vertices_785, vertices_206, vertices_454, vertices_570, vertices_346, vertices_682, vertices_418, vertices_604, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_161, vertices_289, vertices_641, vertices_769, vertices_198, vertices_26, vertices_554, vertices_74, vertices_138, vertices_50, vertices_274, vertices_162, vertices_290, vertices_322, vertices_386, vertices_76, vertices_140, vertices_524, vertices_324, vertices_580, vertices_388, vertices_88, vertices_536, vertices_648, vertices_560, vertices_336, vertices_592, vertices_784, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_653), (false, vertices_421), (false, vertices_837), (false, vertices_689), (false, vertices_785), (true, vertices_198), (true, vertices_26), (true, vertices_554), (true, vertices_74), (true, vertices_138), (true, vertices_162), (true, vertices_322), (true, vertices_386), (true, vertices_76), (true, vertices_88), (true, vertices_536), (true, vertices_336), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 12 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 16 else
  if p.val = (false, vertices_653) then 13 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (true, vertices_198) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_554) then 14 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_592) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_554), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_198), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 8 554
cert_row_2 1 0 1 5 6 198
cert_row_4 2 0 2 3 5 7 346 26 3
cert_row_4 3 1 2 3 5 8 604 76 2
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 198 206 2
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 7 198 454 3
cert_coverFacet 2 570
cert_cover_5 2 0 0 2 3 4 26 570 3
cert_coverFacet 3 346
cert_cover_5 3 2 0 2 3 5 26 346 3
cert_coverFacet 4 682
cert_cover_5 4 0 0 2 4 6 554 682 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 604
cert_cover_5 6 3 1 2 3 5 76 604 2
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0005

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m14e11q2_0006.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0006

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 535, 589, 357, 625, 433, 206, 526, 454, 682, 914, 488, 616, 688, 23, 69, 261, 517, 49, 273, 529, 97, 289, 577, 14, 198, 262, 518, 138, 522, 274, 530, 386, 642, 76, 524, 324, 104, 168, 552, 200, 584, 176, 560, 400, 656, 352, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_535, vertices_589, vertices_357, vertices_625, vertices_433, vertices_206, vertices_526, vertices_454, vertices_682, vertices_914, vertices_488, vertices_616, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_69, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_97, vertices_289, vertices_577, vertices_14, vertices_198, vertices_262, vertices_518, vertices_138, vertices_522, vertices_274, vertices_530, vertices_386, vertices_642, vertices_76, vertices_524, vertices_324, vertices_104, vertices_168, vertices_552, vertices_200, vertices_584, vertices_176, vertices_560, vertices_400, vertices_656, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_535), (false, vertices_589), (false, vertices_357), (false, vertices_625), (false, vertices_433), (true, vertices_14), (true, vertices_198), (true, vertices_138), (true, vertices_522), (true, vertices_386), (true, vertices_642), (true, vertices_104), (true, vertices_168), (true, vertices_552), (true, vertices_200), (true, vertices_656), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 21 23 12 18 14 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 19 else
  if p.val = (false, vertices_535) then 20 else
  if p.val = (false, vertices_589) then 13 else
  if p.val = (false, vertices_357) then 15 else
  if p.val = (false, vertices_625) then 16 else
  if p.val = (false, vertices_433) then 17 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_198) then 22 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 14 => Sum.inl 4
  | 15 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 21 => Sum.inl 0
  | 22 => Sum.inr ⟨(true, vertices_198), by decide +kernel⟩
  | 23 => Sum.inl 1
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_4 1 0 3 6 7 8 914 274 2
cert_row_4 2 0 2 4 6 8 682 138 2
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
cert_coverFacet 3 682
cert_cover_5 3 2 0 2 4 6 138 682 2
cert_coverFacet 4 914
cert_cover_5 4 1 0 3 6 7 274 914 2
cert_coverFacet 5 488
cert_cover_5 5 3 2 4 5 6 104 488 3
cert_coverFacet 6 616
cert_cover_2 6 4 2 5 8 104 616 3
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0006

end
end BundlePart29
-- Explicit facial frame witnesses.

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0360 : Certifies 360 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0693.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0361 : Certifies 361 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0714.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0362 : Certifies 362 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0715.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0363 : Certifies 363 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0717.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0364 : Certifies 364 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0719.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0365 : Certifies 365 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0721.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0366 : Certifies 366 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0723.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0367 : Certifies 367 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0733.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0368 : Certifies 368 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0752.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0369 : Certifies 369 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0755.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0370 : Certifies 370 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0760.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0371 : Certifies 371 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0763.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0372 : Certifies 372 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0780.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0373 : Certifies 373 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0781.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0374 : Certifies 374 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0782.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0375 : Certifies 375 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0789.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0376 : Certifies 376 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0800.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0377 : Certifies 377 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0811.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0378 : Certifies 378 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0813.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0379 : Certifies 379 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q1_0001.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0380 : Certifies 380 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q1_0002.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0381 : Certifies 381 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q1_0008.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0382 : Certifies 382 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q1_0010.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0383 : Certifies 383 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0000.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0384 : Certifies 384 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0001.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0385 : Certifies 385 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0002.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0386 : Certifies 386 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0003.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0387 : Certifies 387 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0004.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0388 : Certifies 388 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0005.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0389 : Certifies 389 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0006.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B012 (j : Fin 30) :
    Certifies (360 + j.val) := by
  fin_cases j
  · exact projection_0360
  · exact projection_0361
  · exact projection_0362
  · exact projection_0363
  · exact projection_0364
  · exact projection_0365
  · exact projection_0366
  · exact projection_0367
  · exact projection_0368
  · exact projection_0369
  · exact projection_0370
  · exact projection_0371
  · exact projection_0372
  · exact projection_0373
  · exact projection_0374
  · exact projection_0375
  · exact projection_0376
  · exact projection_0377
  · exact projection_0378
  · exact projection_0379
  · exact projection_0380
  · exact projection_0381
  · exact projection_0382
  · exact projection_0383
  · exact projection_0384
  · exact projection_0385
  · exact projection_0386
  · exact projection_0387
  · exact projection_0388
  · exact projection_0389

end Nonrational.TerminalVerification
