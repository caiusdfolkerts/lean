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
/- Source: ProjectionCertificates/R_m15e10q1_1162.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1162

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 653, 597, 453, 689, 401, 334, 590, 314, 682, 114, 610, 428, 624, 432, 69, 133, 517, 81, 145, 273, 529, 321, 385, 641, 78, 42, 266, 522, 50, 82, 274, 98, 546, 322, 578, 140, 268, 524, 324, 580, 388, 168, 296, 648, 112, 176, 304, 560, 592, 400, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_653, vertices_597, vertices_453, vertices_689, vertices_401, vertices_334, vertices_590, vertices_314, vertices_682, vertices_114, vertices_610, vertices_428, vertices_624, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_81, vertices_145, vertices_273, vertices_529, vertices_321, vertices_385, vertices_641, vertices_78, vertices_42, vertices_266, vertices_522, vertices_50, vertices_82, vertices_274, vertices_98, vertices_546, vertices_322, vertices_578, vertices_140, vertices_268, vertices_524, vertices_324, vertices_580, vertices_388, vertices_168, vertices_296, vertices_648, vertices_112, vertices_176, vertices_304, vertices_560, vertices_592, vertices_400, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_653), (false, vertices_597), (false, vertices_453), (false, vertices_689), (false, vertices_401), (true, vertices_78), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_98), (true, vertices_546), (true, vertices_578), (true, vertices_268), (true, vertices_168), (true, vertices_296), (true, vertices_112), (true, vertices_304), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 16 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_19 0 401 1 42 266 522 50 98 546 578 268 168 296 112 304 608 416 339 78 653 597 453 689
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 2 3 4 7 314 42 2
cert_row_4 2 0 2 4 6 8 682 42 3
cert_row_4 3 1 2 4 6 7 428 140 2
cert_rows
cert_pivot_2 5 3 0 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 7 78 334 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 314
cert_cover_5 2 1 0 2 3 4 42 314 2
cert_coverFacet 3 682
cert_cover_5 3 2 0 2 4 6 42 682 3
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 610
cert_cover_2 5 4 0 5 8 98 610 3
cert_coverFacet 6 428
cert_cover_5 6 3 1 2 4 6 140 428 2
cert_coverFacet 7 624
cert_cover_2 7 4 3 5 8 112 624 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1162

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_1163.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1163

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [143, 271, 179, 339, 213, 837, 314, 682, 812, 716, 368, 624, 688, 720, 864, 15, 19, 131, 259, 69, 133, 261, 81, 145, 321, 42, 138, 266, 50, 274, 162, 140, 268, 524, 196, 580, 772, 296, 552, 648, 112, 176, 304, 560, 208, 336, 592, 656, 352, 608, 672, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_143, vertices_271, vertices_179, vertices_339, vertices_213, vertices_837, vertices_314, vertices_682, vertices_812, vertices_716, vertices_368, vertices_624, vertices_688, vertices_720, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_15, vertices_19, vertices_131, vertices_259, vertices_69, vertices_133, vertices_261, vertices_81, vertices_145, vertices_321, vertices_42, vertices_138, vertices_266, vertices_50, vertices_274, vertices_162, vertices_140, vertices_268, vertices_524, vertices_196, vertices_580, vertices_772, vertices_296, vertices_552, vertices_648, vertices_112, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_592, vertices_656, vertices_352, vertices_608, vertices_672, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_143), (false, vertices_271), (false, vertices_179), (false, vertices_339), (false, vertices_213), (false, vertices_837), (true, vertices_42), (true, vertices_524), (true, vertices_296), (true, vertices_552), (true, vertices_648), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_592), (true, vertices_656), (true, vertices_352), (true, vertices_608), (true, vertices_672), (true, vertices_800), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 21 15 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_143) then 16 else
  if p.val = (false, vertices_271) then 17 else
  if p.val = (false, vertices_179) then 19 else
  if p.val = (false, vertices_339) then 20 else
  if p.val = (false, vertices_213) then 22 else
  if p.val = (false, vertices_837) then 23 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_296) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_800) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_143), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 7 314 42 2
cert_row_4 1 0 2 4 6 8 682 42 3
cert_row_4 2 1 2 4 7 8 812 268 2
cert_row_4 3 1 2 5 6 8 716 140 2
cert_rows
cert_pivot_2 3 0 4 1
cert_heightProof 4
cert_coverFacet 0 314
cert_cover_5 0 0 0 2 3 4 42 314 2
cert_coverFacet 1 682
cert_cover_5 1 1 0 2 4 6 42 682 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 268 812 2
cert_coverFacet 3 716
cert_cover_5 3 3 1 2 5 6 140 716 2
cert_coverFacet 4 368
cert_cover_2 4 4 3 5 7 112 368 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 688
cert_cover_2 6 4 3 6 8 176 688 3
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coverFacet 8 864
cert_cover_2 8 5 4 7 8 352 864 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1163

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_1164.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1164

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 405, 357, 709, 617, 673, 662, 570, 154, 362, 394, 674, 796, 844, 408, 69, 133, 261, 97, 161, 289, 545, 577, 385, 641, 26, 42, 138, 266, 146, 530, 162, 290, 546, 386, 642, 780, 148, 276, 532, 324, 580, 644, 152, 280, 536, 104, 552, 328, 584, 392, 400, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_405, vertices_357, vertices_709, vertices_617, vertices_673, vertices_662, vertices_570, vertices_154, vertices_362, vertices_394, vertices_674, vertices_796, vertices_844, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_97, vertices_161, vertices_289, vertices_545, vertices_577, vertices_385, vertices_641, vertices_26, vertices_42, vertices_138, vertices_266, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_780, vertices_148, vertices_276, vertices_532, vertices_324, vertices_580, vertices_644, vertices_152, vertices_280, vertices_536, vertices_104, vertices_552, vertices_328, vertices_584, vertices_392, vertices_400, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_405), (false, vertices_357), (false, vertices_709), (false, vertices_617), (false, vertices_673), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_530), (true, vertices_546), (true, vertices_642), (true, vertices_780), (true, vertices_532), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_328), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_405) then 21 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_709) then 23 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (false, vertices_673) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_780) then 19 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
cert_nodeAtPriority_43 673 1 26 2 42 138 266 146 530 546 642 532 152 280 536 328 392 419 617 780 405 357 709
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_2 1 1 2 7 8 780
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 0 2 4 5 7 362 42 3
cert_rows
cert_pivot_2 6 1 3 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 570
cert_cover_5 1 2 0 2 3 4 26 570 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 362
cert_cover_5 3 3 0 2 4 5 42 362 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 796
cert_cover_5 6 1 1 2 3 7 780 796 2
cert_coverFacet 7 844
cert_cover_5 7 1 1 2 5 7 780 844 2
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1164

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_1165.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1165

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 589, 569, 409, 329, 721, 558, 358, 710, 818, 914, 60, 284, 332, 308, 25, 73, 265, 521, 145, 529, 193, 321, 577, 385, 38, 70, 518, 786, 290, 546, 194, 322, 386, 642, 28, 44, 76, 268, 524, 52, 276, 292, 324, 580, 56, 280, 552, 328, 304, 560, 400, 656, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_589, vertices_569, vertices_409, vertices_329, vertices_721, vertices_558, vertices_358, vertices_710, vertices_818, vertices_914, vertices_60, vertices_284, vertices_332, vertices_308] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_521, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_38, vertices_70, vertices_518, vertices_786, vertices_290, vertices_546, vertices_194, vertices_322, vertices_386, vertices_642, vertices_28, vertices_44, vertices_76, vertices_268, vertices_524, vertices_52, vertices_276, vertices_292, vertices_324, vertices_580, vertices_56, vertices_280, vertices_552, vertices_328, vertices_304, vertices_560, vertices_400, vertices_656, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_589), (false, vertices_569), (false, vertices_409), (false, vertices_329), (false, vertices_721), (true, vertices_38), (true, vertices_70), (true, vertices_518), (true, vertices_786), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_52), (true, vertices_276), (true, vertices_292), (true, vertices_324), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_786) then 17 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_52) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_292) then 12 else
  if p.val = (true, vertices_324) then 13 else
  if p.val = (true, vertices_304) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 329 38 70 518 290 546 642 28 44 268 52 276 292 324 304 451 786 589 569 409 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 7 8 786
cert_row_4 1 0 1 2 4 8 558 38 2
cert_row_4 2 0 1 4 5 7 358 38 3
cert_row_4 3 0 1 5 6 8 710 70 3
cert_rows
cert_pivot_2 3 2 4 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 38 558 2
cert_coverFacet 1 358
cert_cover_5 1 2 0 1 4 5 38 358 3
cert_coverFacet 2 710
cert_cover_5 2 3 0 1 5 6 70 710 3
cert_coverFacet 3 818
cert_cover_5 3 0 0 3 4 7 786 818 2
cert_coverFacet 4 914
cert_cover_5 4 0 0 3 6 7 786 914 2
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 332
cert_cover_2 7 2 1 5 7 76 332 3
cert_coverFacet 8 308
cert_cover_2 8 3 1 4 7 52 308 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1165

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_1167.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1167

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 899, 653, 613, 421, 369, 398, 346, 154, 626, 658, 572, 300, 312, 664, 771, 37, 133, 517, 97, 289, 321, 577, 385, 641, 26, 138, 266, 82, 146, 530, 322, 578, 386, 642, 44, 140, 268, 524, 292, 548, 388, 56, 152, 280, 536, 296, 648, 112, 304, 560, 336, 656, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_899, vertices_653, vertices_613, vertices_421, vertices_369, vertices_398, vertices_346, vertices_154, vertices_626, vertices_658, vertices_572, vertices_300, vertices_312, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_771, vertices_37, vertices_133, vertices_517, vertices_97, vertices_289, vertices_321, vertices_577, vertices_385, vertices_641, vertices_26, vertices_138, vertices_266, vertices_82, vertices_146, vertices_530, vertices_322, vertices_578, vertices_386, vertices_642, vertices_44, vertices_140, vertices_268, vertices_524, vertices_292, vertices_548, vertices_388, vertices_56, vertices_152, vertices_280, vertices_536, vertices_296, vertices_648, vertices_112, vertices_304, vertices_560, vertices_336, vertices_656, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_899), (false, vertices_653), (false, vertices_613), (false, vertices_421), (false, vertices_369), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_44), (true, vertices_268), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_296), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 22 => Sum.inl 2
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
cert_row_4 0 0 1 2 6 7 398 138 1
cert_row_4 1 0 2 3 5 7 346 26 3
cert_row_4 2 0 3 4 5 8 626 82 2
cert_row_4 3 1 2 3 4 8 572 44 2
cert_rows
cert_pivot_2 6 7 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 138 398 1
cert_coverFacet 1 346
cert_cover_5 1 1 0 2 3 5 26 346 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 626
cert_cover_5 3 2 0 3 4 5 82 626 2
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 572
cert_cover_5 5 3 1 2 3 4 44 572 2
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1167

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_1168.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1168

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [87, 157, 109, 681, 465, 481, 142, 526, 406, 582, 650, 850, 930, 588, 872, 13, 21, 69, 41, 137, 81, 145, 97, 161, 449, 14, 22, 70, 134, 518, 138, 522, 82, 274, 578, 386, 642, 770, 76, 140, 524, 148, 580, 104, 552, 584, 648, 336, 400, 352, 416, 672, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_87, vertices_157, vertices_109, vertices_681, vertices_465, vertices_481, vertices_142, vertices_526, vertices_406, vertices_582, vertices_650, vertices_850, vertices_930, vertices_588, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_69, vertices_41, vertices_137, vertices_81, vertices_145, vertices_97, vertices_161, vertices_449, vertices_14, vertices_22, vertices_70, vertices_134, vertices_518, vertices_138, vertices_522, vertices_82, vertices_274, vertices_578, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_148, vertices_580, vertices_104, vertices_552, vertices_584, vertices_648, vertices_336, vertices_400, vertices_352, vertices_416, vertices_672, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_87), (false, vertices_157), (false, vertices_109), (false, vertices_681), (false, vertices_465), (false, vertices_481), (true, vertices_14), (true, vertices_134), (true, vertices_518), (true, vertices_138), (true, vertices_522), (true, vertices_274), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_524), (true, vertices_580), (true, vertices_584), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 23 24 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_87) then 16 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_109) then 19 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_800) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_87), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 7 406 22 3
cert_row_4 1 0 3 5 7 8 850 82 3
cert_row_4 2 0 4 6 7 8 930 386 1
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 406
cert_cover_5 2 0 0 1 3 6 22 406 3
cert_coverFacet 3 582
cert_cover_2 3 1 0 5 8 70 582 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 850
cert_cover_5 5 1 0 3 5 7 82 850 3
cert_coverFacet 6 930
cert_cover_5 6 2 0 4 6 7 386 930 1
cert_coverFacet 7 588
cert_cover_2 7 2 1 5 8 76 588 3
cert_coverFacet 8 872
cert_cover_5 8 3 2 4 5 7 104 872 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1168

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_1169.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1169

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 805, 901, 569, 409, 361, 406, 358, 198, 602, 338, 706, 620, 708, 344, 773, 25, 41, 265, 145, 529, 289, 545, 385, 641, 70, 134, 262, 82, 146, 274, 530, 194, 322, 578, 642, 100, 292, 548, 196, 580, 388, 644, 88, 280, 536, 104, 552, 328, 584, 336, 400, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_805, vertices_901, vertices_569, vertices_409, vertices_361, vertices_406, vertices_358, vertices_198, vertices_602, vertices_338, vertices_706, vertices_620, vertices_708, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_773, vertices_25, vertices_41, vertices_265, vertices_145, vertices_529, vertices_289, vertices_545, vertices_385, vertices_641, vertices_70, vertices_134, vertices_262, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_100, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_644, vertices_88, vertices_280, vertices_536, vertices_104, vertices_552, vertices_328, vertices_584, vertices_336, vertices_400, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_805), (false, vertices_901), (false, vertices_569), (false, vertices_409), (false, vertices_361), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_82), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_100), (true, vertices_196), (true, vertices_580), (true, vertices_88), (true, vertices_584), (true, vertices_336), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_42 70 2 134 1 262 82 274 194 322 578 100 196 580 88 584 336 704 659 805 901 569 409 361
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 7 406 134 2
cert_row_4 1 0 1 4 5 7 358 70 2
cert_row_4 2 0 2 3 5 8 602 82 1
cert_row_4 3 1 2 4 5 8 620 100 1
cert_rows
cert_pivot_2 6 7 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 134 406 2
cert_coverFacet 1 358
cert_cover_5 1 1 0 1 4 5 70 358 2
cert_coverFacet 2 198
cert_cover_2 2 1 0 5 6 70 198 3
cert_coverFacet 3 602
cert_cover_5 3 2 0 2 3 5 82 602 1
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 100 620 1
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1169

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_1170.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1170

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 899, 397, 229, 805, 625, 782, 602, 282, 242, 402, 572, 172, 184, 408, 643, 37, 133, 261, 97, 545, 193, 577, 385, 769, 26, 266, 522, 82, 146, 274, 194, 578, 386, 770, 44, 140, 268, 524, 164, 548, 772, 56, 152, 280, 536, 168, 392, 112, 176, 560, 592, 400, 224]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_899, vertices_397, vertices_229, vertices_805, vertices_625, vertices_782, vertices_602, vertices_282, vertices_242, vertices_402, vertices_572, vertices_172, vertices_184, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_643, vertices_37, vertices_133, vertices_261, vertices_97, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_26, vertices_266, vertices_522, vertices_82, vertices_146, vertices_274, vertices_194, vertices_578, vertices_386, vertices_770, vertices_44, vertices_140, vertices_268, vertices_524, vertices_164, vertices_548, vertices_772, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_392, vertices_112, vertices_176, vertices_560, vertices_592, vertices_400, vertices_224] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_899), (false, vertices_397), (false, vertices_229), (false, vertices_805), (false, vertices_625), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_44), (true, vertices_524), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_229) then 20 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 0 3 4 5 6 242 82 2
cert_row_4 2 0 2 3 5 8 602 26 3
cert_row_4 3 1 2 3 4 8 572 44 2
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 602
cert_cover_5 1 2 0 2 3 5 26 602 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 242
cert_cover_5 3 1 0 3 4 5 82 242 2
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 572
cert_cover_5 5 3 1 2 3 4 44 572 2
cert_coverFacet 6 172
cert_cover_2 6 2 1 4 6 44 172 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1170

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_1172.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1172

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 333, 569, 409, 585, 721, 558, 358, 710, 818, 914, 60, 284, 588, 308, 25, 73, 265, 521, 145, 529, 193, 321, 577, 385, 38, 70, 518, 786, 290, 546, 194, 322, 386, 642, 28, 44, 76, 268, 524, 52, 276, 292, 324, 580, 56, 280, 552, 584, 304, 560, 400, 656, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_333, vertices_569, vertices_409, vertices_585, vertices_721, vertices_558, vertices_358, vertices_710, vertices_818, vertices_914, vertices_60, vertices_284, vertices_588, vertices_308] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_521, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_38, vertices_70, vertices_518, vertices_786, vertices_290, vertices_546, vertices_194, vertices_322, vertices_386, vertices_642, vertices_28, vertices_44, vertices_76, vertices_268, vertices_524, vertices_52, vertices_276, vertices_292, vertices_324, vertices_580, vertices_56, vertices_280, vertices_552, vertices_584, vertices_304, vertices_560, vertices_400, vertices_656, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_333), (false, vertices_569), (false, vertices_409), (false, vertices_585), (false, vertices_721), (true, vertices_38), (true, vertices_70), (true, vertices_518), (true, vertices_786), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_28), (true, vertices_44), (true, vertices_524), (true, vertices_52), (true, vertices_276), (true, vertices_292), (true, vertices_580), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_786) then 17 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_52) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_292) then 12 else
  if p.val = (true, vertices_580) then 13 else
  if p.val = (true, vertices_304) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 585 38 70 518 290 546 642 28 44 524 52 276 292 580 304 451 786 333 569 409 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 7 8 786
cert_row_4 1 0 1 2 4 8 558 38 2
cert_row_4 2 0 1 4 5 7 358 38 3
cert_row_4 3 0 1 5 6 8 710 70 3
cert_rows
cert_pivot_2 3 2 4 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 38 558 2
cert_coverFacet 1 358
cert_cover_5 1 2 0 1 4 5 38 358 3
cert_coverFacet 2 710
cert_cover_5 2 3 0 1 5 6 70 710 3
cert_coverFacet 3 818
cert_cover_5 3 0 0 3 4 7 786 818 2
cert_coverFacet 4 914
cert_cover_5 4 0 0 3 6 7 786 914 2
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 588
cert_cover_2 7 2 1 5 8 76 588 3
cert_coverFacet 8 308
cert_cover_2 8 3 1 4 7 52 308 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1172

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_1173.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1173

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [87, 157, 109, 681, 465, 481, 78, 526, 406, 646, 586, 850, 930, 652, 872, 13, 21, 69, 41, 137, 81, 145, 97, 161, 449, 14, 22, 70, 134, 518, 74, 522, 82, 274, 578, 386, 642, 770, 76, 140, 524, 148, 644, 104, 552, 584, 648, 336, 400, 352, 416, 672, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_87, vertices_157, vertices_109, vertices_681, vertices_465, vertices_481, vertices_78, vertices_526, vertices_406, vertices_646, vertices_586, vertices_850, vertices_930, vertices_652, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_69, vertices_41, vertices_137, vertices_81, vertices_145, vertices_97, vertices_161, vertices_449, vertices_14, vertices_22, vertices_70, vertices_134, vertices_518, vertices_74, vertices_522, vertices_82, vertices_274, vertices_578, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_148, vertices_644, vertices_104, vertices_552, vertices_584, vertices_648, vertices_336, vertices_400, vertices_352, vertices_416, vertices_672, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_87), (false, vertices_157), (false, vertices_109), (false, vertices_681), (false, vertices_465), (false, vertices_481), (true, vertices_14), (true, vertices_134), (true, vertices_518), (true, vertices_74), (true, vertices_522), (true, vertices_274), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_524), (true, vertices_644), (true, vertices_584), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 23 24 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_87) then 16 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_109) then 19 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_800) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_87), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 7 406 22 3
cert_row_4 1 0 3 5 7 8 850 82 3
cert_row_4 2 0 4 6 7 8 930 386 1
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 406
cert_cover_5 2 0 0 1 3 6 22 406 3
cert_coverFacet 3 646
cert_cover_2 3 1 0 6 8 134 646 3
cert_coverFacet 4 586
cert_cover_2 4 2 0 5 8 74 586 3
cert_coverFacet 5 850
cert_cover_5 5 1 0 3 5 7 82 850 3
cert_coverFacet 6 930
cert_cover_5 6 2 0 4 6 7 386 930 1
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 872
cert_cover_5 8 3 2 4 5 7 104 872 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1173

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_1174.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1174

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 563, 707, 387, 617, 113, 465, 398, 534, 646, 812, 716, 820, 376, 456, 19, 131, 259, 515, 49, 81, 273, 97, 545, 193, 577, 385, 22, 134, 262, 518, 530, 386, 642, 140, 268, 524, 276, 532, 804, 644, 104, 296, 552, 200, 328, 584, 392, 112, 304, 560, 336, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_563, vertices_707, vertices_387, vertices_617, vertices_113, vertices_465, vertices_398, vertices_534, vertices_646, vertices_812, vertices_716, vertices_820, vertices_376, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_49, vertices_81, vertices_273, vertices_97, vertices_545, vertices_193, vertices_577, vertices_385, vertices_22, vertices_134, vertices_262, vertices_518, vertices_530, vertices_386, vertices_642, vertices_140, vertices_268, vertices_524, vertices_276, vertices_532, vertices_804, vertices_644, vertices_104, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_112, vertices_304, vertices_560, vertices_336, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_563), (false, vertices_707), (false, vertices_387), (false, vertices_617), (false, vertices_113), (false, vertices_465), (true, vertices_134), (true, vertices_518), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_532), (true, vertices_804), (true, vertices_644), (true, vertices_296), (true, vertices_200), (true, vertices_328), (true, vertices_392), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 15 else
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_113) then 1 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_804) then 19 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_304) then 13 else
  0
cert_priority
cert_nodeAtPriority_47 387 113 134 518 140 268 524 532 644 296 200 328 392 304 279 563 707 804 617 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_4 1 1 2 5 6 8 716 140 2
cert_row_2 2 1 4 7 8 804
cert_row_4 3 2 3 4 5 7 376 104 1
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 812
cert_cover_5 3 2 1 2 4 7 268 812 2
cert_coverFacet 4 716
cert_cover_5 4 1 1 2 5 6 140 716 2
cert_coverFacet 5 820
cert_cover_5 5 2 1 3 4 7 276 820 2
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 104 376 1
cert_coverFacet 7 456
cert_cover_2 7 5 2 6 7 200 456 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1174

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_1175.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1175

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 541, 85, 613, 345, 297, 481, 158, 654, 282, 298, 434, 738, 468, 708, 21, 69, 517, 25, 41, 265, 521, 81, 97, 289, 545, 321, 142, 26, 42, 266, 522, 146, 274, 162, 290, 546, 642, 28, 524, 84, 148, 196, 580, 644, 280, 296, 336, 400, 224, 608, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_541, vertices_85, vertices_613, vertices_345, vertices_297, vertices_481, vertices_158, vertices_654, vertices_282, vertices_298, vertices_434, vertices_738, vertices_468, vertices_708] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_517, vertices_25, vertices_41, vertices_265, vertices_521, vertices_81, vertices_97, vertices_289, vertices_545, vertices_321, vertices_142, vertices_26, vertices_42, vertices_266, vertices_522, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_642, vertices_28, vertices_524, vertices_84, vertices_148, vertices_196, vertices_580, vertices_644, vertices_280, vertices_296, vertices_336, vertices_400, vertices_224, vertices_608, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_541), (false, vertices_85), (false, vertices_613), (false, vertices_345), (false, vertices_297), (false, vertices_481), (true, vertices_142), (true, vertices_26), (true, vertices_266), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_290), (true, vertices_642), (true, vertices_148), (true, vertices_196), (true, vertices_644), (true, vertices_400), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 15 else
  if p.val = (false, vertices_541) then 18 else
  if p.val = (false, vertices_85) then 0 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_142) then 16 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_53 0 85 1 297 26 266 146 274 162 290 642 148 196 644 400 704 555 142 541 613 345 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 6 142
cert_row_4 1 0 4 5 6 8 738 162 2
cert_row_4 2 0 3 4 6 7 434 146 2
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 142 158 3
cert_coverFacet 1 654
cert_cover_5 1 0 0 1 2 8 142 654 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 434
cert_cover_5 4 2 0 3 4 6 146 434 2
cert_coverFacet 5 738
cert_cover_5 5 1 0 4 5 6 162 738 2
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 84 468 3
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1175

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_1176.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1176

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 157, 525, 165, 805, 313, 241, 206, 590, 394, 466, 866, 740, 408, 368, 13, 37, 133, 517, 25, 265, 521, 49, 145, 161, 289, 769, 78, 138, 266, 522, 194, 322, 578, 386, 770, 140, 524, 164, 548, 196, 580, 152, 280, 392, 112, 304, 208, 336, 400, 224, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_157, vertices_525, vertices_165, vertices_805, vertices_313, vertices_241, vertices_206, vertices_590, vertices_394, vertices_466, vertices_866, vertices_740, vertices_408, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_133, vertices_517, vertices_25, vertices_265, vertices_521, vertices_49, vertices_145, vertices_161, vertices_289, vertices_769, vertices_78, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_140, vertices_524, vertices_164, vertices_548, vertices_196, vertices_580, vertices_152, vertices_280, vertices_392, vertices_112, vertices_304, vertices_208, vertices_336, vertices_400, vertices_224, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_157), (false, vertices_525), (false, vertices_165), (false, vertices_805), (false, vertices_313), (false, vertices_241), (true, vertices_78), (true, vertices_138), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_196), (true, vertices_580), (true, vertices_392), (true, vertices_336), (true, vertices_400), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_165) then 1 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_78) then 16 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 525 1 165 138 194 322 578 386 196 580 392 336 400 352 608 779 78 157 805 313 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 3 5 6 7 466 194 1
cert_row_4 2 0 4 5 7 8 866 322 1
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 6 78 206 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 466
cert_cover_5 3 1 0 3 5 6 194 466 1
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 322 866 1
cert_coverFacet 5 740
cert_cover_5 5 3 1 4 5 6 164 740 2
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1176

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_1177.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1177

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 421, 601, 233, 393, 865, 94, 206, 406, 538, 394, 818, 628, 308, 228, 73, 137, 265, 521, 97, 161, 289, 577, 385, 769, 78, 22, 134, 26, 138, 266, 522, 274, 530, 386, 770, 52, 84, 276, 100, 164, 292, 196, 388, 88, 536, 200, 392, 304, 560, 592, 224, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_421, vertices_601, vertices_233, vertices_393, vertices_865, vertices_94, vertices_206, vertices_406, vertices_538, vertices_394, vertices_818, vertices_628, vertices_308, vertices_228] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_769, vertices_78, vertices_22, vertices_134, vertices_26, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_386, vertices_770, vertices_52, vertices_84, vertices_276, vertices_100, vertices_164, vertices_292, vertices_196, vertices_388, vertices_88, vertices_536, vertices_200, vertices_392, vertices_304, vertices_560, vertices_592, vertices_224, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_421), (false, vertices_601), (false, vertices_233), (false, vertices_393), (false, vertices_865), (true, vertices_78), (true, vertices_22), (true, vertices_134), (true, vertices_26), (true, vertices_138), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_100), (true, vertices_196), (true, vertices_304), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_196) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_560) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 393 22 134 26 138 274 530 386 52 84 276 100 196 304 560 779 78 421 601 233 865
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 1 3 6 7 406 22 3
cert_row_4 2 0 3 4 7 8 818 274 2
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 78 94 3
cert_coverFacet 1 206
cert_cover_5 1 0 0 1 2 6 78 206 3
cert_coverFacet 2 406
cert_cover_5 2 1 0 1 3 6 22 406 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 818
cert_cover_5 5 2 0 3 4 7 274 818 2
cert_coverFacet 6 628
cert_cover_5 6 3 1 3 4 5 52 628 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coverFacet 8 228
cert_cover_2 8 4 1 5 6 100 228 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1177

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_1178.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1178

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 805, 233, 841, 625, 417, 286, 590, 598, 202, 242, 402, 780, 436, 564, 73, 137, 265, 97, 161, 289, 545, 577, 385, 769, 14, 22, 582, 74, 138, 266, 82, 146, 274, 194, 386, 268, 524, 52, 276, 532, 292, 548, 772, 200, 584, 776, 112, 176, 560, 592, 400, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_805, vertices_233, vertices_841, vertices_625, vertices_417, vertices_286, vertices_590, vertices_598, vertices_202, vertices_242, vertices_402, vertices_780, vertices_436, vertices_564] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_97, vertices_161, vertices_289, vertices_545, vertices_577, vertices_385, vertices_769, vertices_14, vertices_22, vertices_582, vertices_74, vertices_138, vertices_266, vertices_82, vertices_146, vertices_274, vertices_194, vertices_386, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_292, vertices_548, vertices_772, vertices_200, vertices_584, vertices_776, vertices_112, vertices_176, vertices_560, vertices_592, vertices_400, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_805), (false, vertices_233), (false, vertices_841), (false, vertices_625), (false, vertices_417), (true, vertices_14), (true, vertices_22), (true, vertices_582), (true, vertices_74), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_194), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_582) then 17 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_52) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 417 14 22 74 82 146 274 194 268 524 52 276 532 176 400 395 582 805 233 841 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 8 582
cert_row_4 1 0 1 2 3 7 286 14 3
cert_row_4 2 0 3 4 5 6 242 82 2
cert_row_4 3 1 3 4 6 7 436 52 3
cert_rows
cert_pivot_2 8 2 0 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 1 0 1 2 3 14 286 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 5 14 590 3
cert_coverFacet 2 598
cert_cover_5 2 0 0 1 3 5 22 598 3
cert_coverFacet 3 202
cert_cover_2 3 2 0 5 6 74 202 3
cert_coverFacet 4 242
cert_cover_5 4 2 0 3 4 5 82 242 2
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 436
cert_cover_5 7 3 1 3 4 6 52 436 3
cert_coverFacet 8 564
cert_cover_2 8 3 1 4 8 52 564 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1178

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_1179.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1179

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 453, 809, 433, 721, 833, 62, 78, 662, 710, 554, 842, 364, 308, 404, 49, 145, 529, 289, 545, 193, 321, 577, 385, 769, 14, 22, 70, 646, 42, 74, 522, 50, 530, 546, 578, 44, 76, 52, 148, 276, 292, 196, 324, 388, 296, 552, 328, 776, 304, 400, 656, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_453, vertices_809, vertices_433, vertices_721, vertices_833, vertices_62, vertices_78, vertices_662, vertices_710, vertices_554, vertices_842, vertices_364, vertices_308, vertices_404] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_529, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_14, vertices_22, vertices_70, vertices_646, vertices_42, vertices_74, vertices_522, vertices_50, vertices_530, vertices_546, vertices_578, vertices_44, vertices_76, vertices_52, vertices_148, vertices_276, vertices_292, vertices_196, vertices_324, vertices_388, vertices_296, vertices_552, vertices_328, vertices_776, vertices_304, vertices_400, vertices_656, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_453), (false, vertices_809), (false, vertices_433), (false, vertices_721), (false, vertices_833), (true, vertices_14), (true, vertices_22), (true, vertices_70), (true, vertices_646), (true, vertices_42), (true, vertices_74), (true, vertices_522), (true, vertices_578), (true, vertices_44), (true, vertices_76), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_292), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_70) then 3 else
  if p.val = (true, vertices_646) then 17 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_52) then 10 else
  if p.val = (true, vertices_148) then 11 else
  if p.val = (true, vertices_276) then 12 else
  if p.val = (true, vertices_292) then 13 else
  if p.val = (true, vertices_328) then 14 else
  0
cert_priority
cert_nodeAtPriority_40 833 14 22 70 42 74 522 578 44 76 52 148 276 292 328 563 646 453 809 433 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 8 646
cert_row_4 1 0 1 2 3 4 62 14 3
cert_row_4 2 0 2 5 7 8 842 74 3
cert_row_4 3 1 2 4 5 7 364 44 3
cert_rows
cert_pivot_2 6 3 0 1
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 1 0 1 2 3 14 62 3
cert_coverFacet 1 78
cert_cover_2 1 1 0 2 5 14 78 3
cert_coverFacet 2 662
cert_cover_5 2 0 0 1 3 6 22 662 3
cert_coverFacet 3 710
cert_cover_5 3 0 0 1 5 6 70 710 3
cert_coverFacet 4 554
cert_cover_2 4 2 0 4 8 42 554 3
cert_coverFacet 5 842
cert_cover_5 5 2 0 2 5 7 74 842 3
cert_coverFacet 6 364
cert_cover_5 6 3 1 2 4 5 44 364 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coverFacet 8 404
cert_cover_2 8 3 1 6 7 148 404 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1179

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_1180.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1180

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 355, 547, 387, 565, 457, 241, 654, 810, 394, 220, 844, 116, 660, 868, 35, 131, 259, 515, 49, 145, 529, 97, 545, 193, 321, 385, 138, 266, 522, 290, 546, 386, 642, 76, 140, 524, 52, 84, 148, 532, 100, 548, 836, 644, 200, 328, 392, 776, 112, 208, 656, 352, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_355, vertices_547, vertices_387, vertices_565, vertices_457, vertices_241, vertices_654, vertices_810, vertices_394, vertices_220, vertices_844, vertices_116, vertices_660, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_49, vertices_145, vertices_529, vertices_97, vertices_545, vertices_193, vertices_321, vertices_385, vertices_138, vertices_266, vertices_522, vertices_290, vertices_546, vertices_386, vertices_642, vertices_76, vertices_140, vertices_524, vertices_52, vertices_84, vertices_148, vertices_532, vertices_100, vertices_548, vertices_836, vertices_644, vertices_200, vertices_328, vertices_392, vertices_776, vertices_112, vertices_208, vertices_656, vertices_352, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_355), (false, vertices_547), (false, vertices_387), (false, vertices_565), (false, vertices_457), (false, vertices_241), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_84), (true, vertices_148), (true, vertices_100), (true, vertices_836), (true, vertices_644), (true, vertices_776), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_355) then 16 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_565) then 18 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_836) then 19 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
cert_nodeAtPriority_44 547 387 138 266 522 76 140 524 84 148 100 644 776 800 659 355 565 836 457 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 266 2
cert_row_2 1 1 5 7 8 836
cert_row_4 2 0 1 2 6 8 654 138 1
cert_row_4 3 1 2 3 5 6 220 76 2
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 138 654 1
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 266 810 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 220
cert_cover_5 3 3 1 2 3 5 76 220 2
cert_coverFacet 4 844
cert_cover_5 4 1 1 2 5 7 76 844 3
cert_coverFacet 5 116
cert_cover_2 5 3 1 4 5 52 116 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 868
cert_cover_5 7 1 1 4 5 7 100 868 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1180

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_1181.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1181

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 557, 397, 773, 713, 849, 62, 286, 170, 394, 370, 738, 628, 788, 680, 13, 261, 517, 137, 521, 193, 321, 577, 385, 769, 30, 42, 138, 266, 50, 274, 98, 162, 194, 322, 386, 44, 268, 52, 276, 532, 548, 772, 168, 552, 392, 648, 112, 336, 592, 784, 608, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_557, vertices_397, vertices_773, vertices_713, vertices_849, vertices_62, vertices_286, vertices_170, vertices_394, vertices_370, vertices_738, vertices_628, vertices_788, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_261, vertices_517, vertices_137, vertices_521, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_30, vertices_42, vertices_138, vertices_266, vertices_50, vertices_274, vertices_98, vertices_162, vertices_194, vertices_322, vertices_386, vertices_44, vertices_268, vertices_52, vertices_276, vertices_532, vertices_548, vertices_772, vertices_168, vertices_552, vertices_392, vertices_648, vertices_112, vertices_336, vertices_592, vertices_784, vertices_608, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_557), (false, vertices_397), (false, vertices_773), (false, vertices_713), (false, vertices_849), (true, vertices_30), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_50), (true, vertices_274), (true, vertices_98), (true, vertices_162), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_168), (true, vertices_112), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_397) then 20 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (true, vertices_30) then 17 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_162) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 773 42 138 266 50 274 98 162 52 276 532 168 112 608 672 451 30 557 397 713 849
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 0 3 4 5 7 370 50 3
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 4 30 62 3
cert_coverFacet 1 286
cert_cover_5 1 0 0 1 2 7 30 286 3
cert_coverFacet 2 170
cert_cover_2 2 2 0 4 6 42 170 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 370
cert_cover_5 4 1 0 3 4 5 50 370 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 98 738 3
cert_coverFacet 6 628
cert_cover_5 6 3 1 3 4 5 52 628 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 680
cert_cover_2 8 4 2 6 8 168 680 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1181

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_1182.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1182

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 535, 109, 309, 713, 625, 270, 278, 666, 458, 434, 332, 484, 688, 736, 519, 13, 21, 37, 73, 521, 49, 529, 97, 577, 14, 22, 262, 138, 266, 522, 146, 274, 530, 386, 76, 268, 276, 100, 292, 324, 200, 328, 648, 176, 304, 560, 656, 224, 608, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_535, vertices_109, vertices_309, vertices_713, vertices_625, vertices_270, vertices_278, vertices_666, vertices_458, vertices_434, vertices_332, vertices_484, vertices_688, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_519, vertices_13, vertices_21, vertices_37, vertices_73, vertices_521, vertices_49, vertices_529, vertices_97, vertices_577, vertices_14, vertices_22, vertices_262, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_76, vertices_268, vertices_276, vertices_100, vertices_292, vertices_324, vertices_200, vertices_328, vertices_648, vertices_176, vertices_304, vertices_560, vertices_656, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_535), (false, vertices_109), (false, vertices_309), (false, vertices_713), (false, vertices_625), (true, vertices_262), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_274), (true, vertices_386), (true, vertices_268), (true, vertices_324), (true, vertices_328), (true, vertices_176), (true, vertices_656), (true, vertices_224), (true, vertices_416), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 16 else
  if p.val = (false, vertices_535) then 17 else
  if p.val = (false, vertices_109) then 19 else
  if p.val = (false, vertices_309) then 20 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_62 262 138 266 146 274 386 268 324 328 176 656 224 416 672 448 527 535 109 309 713 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 138 2
cert_row_4 1 0 2 5 6 7 458 138 2
cert_row_4 2 0 3 4 6 7 434 146 2
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 8 2 0 1
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 666
cert_cover_5 2 0 0 2 3 6 138 666 2
cert_coverFacet 3 458
cert_cover_5 3 1 0 2 5 6 138 458 2
cert_coverFacet 4 434
cert_cover_5 4 2 0 3 4 6 146 434 2
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 100 484 3
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coverFacet 8 736
cert_cover_2 8 5 4 6 8 224 736 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1182

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_1183.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1183

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 403, 771, 345, 721, 865, 174, 614, 426, 802, 668, 364, 588, 600, 408, 131, 259, 515, 81, 145, 273, 321, 577, 641, 769, 38, 134, 518, 170, 290, 546, 386, 770, 44, 76, 140, 524, 100, 580, 644, 88, 152, 280, 536, 296, 328, 584, 392, 592, 400, 656, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_403, vertices_771, vertices_345, vertices_721, vertices_865, vertices_174, vertices_614, vertices_426, vertices_802, vertices_668, vertices_364, vertices_588, vertices_600, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_81, vertices_145, vertices_273, vertices_321, vertices_577, vertices_641, vertices_769, vertices_38, vertices_134, vertices_518, vertices_170, vertices_290, vertices_546, vertices_386, vertices_770, vertices_44, vertices_76, vertices_140, vertices_524, vertices_100, vertices_580, vertices_644, vertices_88, vertices_152, vertices_280, vertices_536, vertices_296, vertices_328, vertices_584, vertices_392, vertices_592, vertices_400, vertices_656, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_403), (false, vertices_771), (false, vertices_345), (false, vertices_721), (false, vertices_865), (true, vertices_38), (true, vertices_170), (true, vertices_290), (true, vertices_546), (true, vertices_44), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_100), (true, vertices_580), (true, vertices_152), (true, vertices_536), (true, vertices_296), (true, vertices_584), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 15 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_403) then 18 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_170) then 19 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
cert_nodeAtPriority_9 1 771 0 38 290 546 44 76 140 524 100 580 152 536 296 584 392 647 403 170 345 721 865
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 6 8 668 140 2
cert_row_2 1 0 2 4 6 170
cert_row_4 2 0 1 4 5 8 614 38 3
cert_row_4 3 1 2 4 5 7 364 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 1 0 1 2 4 38 174 2
cert_coverFacet 1 614
cert_cover_5 1 2 0 1 4 5 38 614 3
cert_coverFacet 2 426
cert_cover_5 2 1 0 2 4 7 170 426 3
cert_coverFacet 3 802
cert_cover_2 3 4 0 7 8 290 802 3
cert_coverFacet 4 668
cert_cover_5 4 0 1 2 3 6 140 668 2
cert_coverFacet 5 364
cert_cover_5 5 3 1 2 4 5 44 364 3
cert_coverFacet 6 588
cert_cover_2 6 2 1 5 8 76 588 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1183

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_1184.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1184

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 395, 675, 457, 241, 865, 334, 526, 666, 124, 540, 692, 356, 804, 216, 131, 259, 515, 393, 97, 161, 545, 193, 321, 769, 14, 262, 518, 138, 266, 522, 642, 28, 76, 524, 52, 532, 100, 292, 548, 324, 772, 88, 152, 536, 200, 328, 112, 176, 208, 656, 352, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_395, vertices_675, vertices_457, vertices_241, vertices_865, vertices_334, vertices_526, vertices_666, vertices_124, vertices_540, vertices_692, vertices_356, vertices_804, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_393, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_769, vertices_14, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_642, vertices_28, vertices_76, vertices_524, vertices_52, vertices_532, vertices_100, vertices_292, vertices_548, vertices_324, vertices_772, vertices_88, vertices_152, vertices_536, vertices_200, vertices_328, vertices_112, vertices_176, vertices_208, vertices_656, vertices_352, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_395), (false, vertices_675), (false, vertices_457), (false, vertices_241), (false, vertices_865), (true, vertices_14), (true, vertices_522), (true, vertices_28), (true, vertices_76), (true, vertices_524), (true, vertices_52), (true, vertices_532), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_324), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 19 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_395) then 20 else
  if p.val = (false, vertices_675) then 17 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
cert_row_4 0 0 1 2 5 7 334 14 3
cert_row_4 1 0 2 3 6 8 666 138 2
cert_row_4 2 1 2 3 4 5 124 28 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 7 0 2 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 666
cert_cover_5 2 1 0 2 3 6 138 666 2
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 4 28 124 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 692
cert_cover_5 5 3 1 3 4 6 52 692 3
cert_coverFacet 6 356
cert_cover_2 6 4 1 5 7 100 356 3
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1184

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_1185.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1185

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 93, 141, 533, 901, 233, 465, 30, 46, 566, 346, 362, 930, 684, 480, 13, 21, 133, 517, 73, 137, 81, 273, 529, 193, 385, 769, 14, 22, 38, 26, 42, 330, 274, 530, 290, 546, 770, 28, 44, 140, 532, 548, 644, 88, 104, 168, 336, 224, 352, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_93, vertices_141, vertices_533, vertices_901, vertices_233, vertices_465, vertices_30, vertices_46, vertices_566, vertices_346, vertices_362, vertices_930, vertices_684, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_133, vertices_517, vertices_73, vertices_137, vertices_81, vertices_273, vertices_529, vertices_193, vertices_385, vertices_769, vertices_14, vertices_22, vertices_38, vertices_26, vertices_42, vertices_330, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_28, vertices_44, vertices_140, vertices_532, vertices_548, vertices_644, vertices_88, vertices_104, vertices_168, vertices_336, vertices_224, vertices_352, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_93), (false, vertices_141), (false, vertices_533), (false, vertices_901), (false, vertices_233), (false, vertices_465), (true, vertices_14), (true, vertices_22), (true, vertices_38), (true, vertices_26), (true, vertices_42), (true, vertices_330), (true, vertices_290), (true, vertices_546), (true, vertices_44), (true, vertices_548), (true, vertices_352), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_22) then 3 else
  if p.val = (true, vertices_38) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_42) then 6 else
  if p.val = (true, vertices_330) then 16 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 141 1 533 14 22 38 26 42 290 546 44 548 352 416 672 787 330 93 901 233 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 7 330
cert_row_4 1 0 1 3 4 8 566 22 3
cert_row_4 2 0 4 6 7 8 930 290 2
cert_row_4 3 1 2 4 6 8 684 44 3
cert_rows
cert_pivot_2 5 3 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 46
cert_cover_2 1 1 0 2 4 14 46 3
cert_coverFacet 2 566
cert_cover_5 2 1 0 1 3 4 22 566 3
cert_coverFacet 3 346
cert_cover_5 3 0 0 2 3 5 26 346 3
cert_coverFacet 4 362
cert_cover_5 4 0 0 2 4 5 42 362 3
cert_coverFacet 5 930
cert_cover_5 5 2 0 4 6 7 290 930 2
cert_coverFacet 6 684
cert_cover_5 6 3 1 2 4 6 44 684 3
cert_coverFacet 7 480
cert_cover_2 7 5 4 6 7 224 480 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1185

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_1186.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1186

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 301, 53, 213, 389, 569, 345, 806, 362, 618, 722, 898, 692, 900, 600, 21, 37, 133, 261, 25, 41, 265, 49, 81, 193, 321, 385, 106, 290, 546, 194, 322, 578, 386, 642, 770, 52, 148, 292, 548, 388, 644, 772, 88, 536, 296, 552, 328, 584, 560, 208, 592, 656, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_301, vertices_53, vertices_213, vertices_389, vertices_569, vertices_345, vertices_806, vertices_362, vertices_618, vertices_722, vertices_898, vertices_692, vertices_900, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_133, vertices_261, vertices_25, vertices_41, vertices_265, vertices_49, vertices_81, vertices_193, vertices_321, vertices_385, vertices_106, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_52, vertices_148, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_88, vertices_536, vertices_296, vertices_552, vertices_328, vertices_584, vertices_560, vertices_208, vertices_592, vertices_656, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_301), (false, vertices_53), (false, vertices_213), (false, vertices_389), (false, vertices_569), (false, vertices_345), (true, vertices_106), (true, vertices_290), (true, vertices_546), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_584), (true, vertices_592), (true, vertices_656), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_53) then 0 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (true, vertices_106) then 16 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
cert_nodeAtPriority_25 0 53 1 389 290 546 578 642 770 548 644 772 584 592 656 896 451 106 301 213 569 345
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 3 5 6 8 722 194 1
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 362
cert_cover_5 1 0 0 2 4 7 106 362 3
cert_coverFacet 2 618
cert_cover_5 2 0 0 2 4 8 106 618 3
cert_coverFacet 3 722
cert_cover_5 3 2 0 3 5 6 194 722 1
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 692
cert_cover_5 5 3 1 3 4 6 52 692 3
cert_coverFacet 6 900
cert_cover_2 6 6 1 7 8 388 900 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1186

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_1187.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1187

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 805, 453, 361, 721, 609, 158, 782, 58, 810, 626, 658, 396, 248, 456, 133, 261, 517, 97, 289, 545, 193, 321, 577, 641, 14, 134, 518, 26, 42, 778, 50, 146, 530, 546, 642, 140, 268, 388, 772, 56, 152, 104, 296, 200, 328, 392, 112, 208, 592, 656, 608, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_805, vertices_453, vertices_361, vertices_721, vertices_609, vertices_158, vertices_782, vertices_58, vertices_810, vertices_626, vertices_658, vertices_396, vertices_248, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_14, vertices_134, vertices_518, vertices_26, vertices_42, vertices_778, vertices_50, vertices_146, vertices_530, vertices_546, vertices_642, vertices_140, vertices_268, vertices_388, vertices_772, vertices_56, vertices_152, vertices_104, vertices_296, vertices_200, vertices_328, vertices_392, vertices_112, vertices_208, vertices_592, vertices_656, vertices_608, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_805), (false, vertices_453), (false, vertices_361), (false, vertices_721), (false, vertices_609), (true, vertices_14), (true, vertices_26), (true, vertices_42), (true, vertices_778), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_546), (true, vertices_140), (true, vertices_268), (true, vertices_56), (true, vertices_152), (true, vertices_200), (true, vertices_392), (true, vertices_112)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (false, vertices_609) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_778) then 17 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_112) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 609 14 26 42 50 146 530 546 140 268 56 152 200 392 112 647 778 805 453 361 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 0 1 2 3 6 158 14 3
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 7 1 0 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 14 158 3
cert_coverFacet 1 782
cert_cover_5 1 0 0 1 2 7 14 782 3
cert_coverFacet 2 58
cert_cover_2 2 2 0 3 4 26 58 3
cert_coverFacet 3 810
cert_cover_5 3 0 0 2 4 7 42 810 3
cert_coverFacet 4 626
cert_cover_5 4 2 0 3 4 5 50 626 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 248
cert_cover_5 7 3 2 3 4 5 56 248 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1187

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_1188.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1188

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 779, 275, 157, 525, 457, 433, 626, 306, 482, 834, 204, 844, 692, 740, 19, 259, 515, 13, 21, 517, 137, 265, 521, 145, 273, 385, 50, 274, 530, 98, 290, 322, 578, 770, 76, 140, 524, 148, 532, 676, 196, 580, 200, 328, 776, 176, 304, 560, 224, 608, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_779, vertices_275, vertices_157, vertices_525, vertices_457, vertices_433, vertices_626, vertices_306, vertices_482, vertices_834, vertices_204, vertices_844, vertices_692, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_259, vertices_515, vertices_13, vertices_21, vertices_517, vertices_137, vertices_265, vertices_521, vertices_145, vertices_273, vertices_385, vertices_50, vertices_274, vertices_530, vertices_98, vertices_290, vertices_322, vertices_578, vertices_770, vertices_76, vertices_140, vertices_524, vertices_148, vertices_532, vertices_676, vertices_196, vertices_580, vertices_200, vertices_328, vertices_776, vertices_176, vertices_304, vertices_560, vertices_224, vertices_608, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_779), (false, vertices_275), (false, vertices_157), (false, vertices_525), (false, vertices_457), (false, vertices_433), (true, vertices_50), (true, vertices_98), (true, vertices_290), (true, vertices_322), (true, vertices_578), (true, vertices_76), (true, vertices_676), (true, vertices_196), (true, vertices_580), (true, vertices_560), (true, vertices_224), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 15 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_676) then 19 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
cert_nodeAtPriority_44 275 525 50 98 290 322 578 76 196 580 560 224 608 832 535 779 157 676 457 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 8 626 50 3
cert_row_4 1 0 4 5 6 7 482 98 3
cert_row_2 2 1 4 6 8 676
cert_row_4 3 1 2 5 7 8 844 76 3
cert_rows
cert_pivot_2 3 0 4 1
cert_heightProof 4
cert_coverFacet 0 626
cert_cover_5 0 0 0 3 4 5 50 626 3
cert_coverFacet 1 306
cert_cover_2 1 3 0 4 7 50 306 3
cert_coverFacet 2 482
cert_cover_5 2 1 0 4 5 6 98 482 3
cert_coverFacet 3 834
cert_cover_2 3 5 0 7 8 322 834 3
cert_coverFacet 4 204
cert_cover_2 4 2 1 5 6 76 204 3
cert_coverFacet 5 844
cert_cover_5 5 3 1 2 5 7 76 844 3
cert_coverFacet 6 692
cert_cover_5 6 2 1 3 4 6 148 692 2
cert_coverFacet 7 740
cert_cover_5 7 2 1 4 5 6 676 740 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1188

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_1189.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1189

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 541, 141, 677, 409, 593, 961, 302, 558, 602, 282, 738, 354, 396, 484, 13, 133, 517, 25, 137, 81, 273, 529, 321, 577, 385, 641, 46, 26, 266, 522, 82, 274, 98, 290, 546, 322, 578, 140, 268, 524, 164, 292, 548, 388, 280, 536, 392, 592, 224, 352, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_541, vertices_141, vertices_677, vertices_409, vertices_593, vertices_961, vertices_302, vertices_558, vertices_602, vertices_282, vertices_738, vertices_354, vertices_396, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_25, vertices_137, vertices_81, vertices_273, vertices_529, vertices_321, vertices_577, vertices_385, vertices_641, vertices_46, vertices_26, vertices_266, vertices_522, vertices_82, vertices_274, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_388, vertices_280, vertices_536, vertices_392, vertices_592, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_541), (false, vertices_141), (false, vertices_677), (false, vertices_409), (false, vertices_593), (false, vertices_961), (true, vertices_46), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_578), (true, vertices_268), (true, vertices_292), (true, vertices_388), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 15 else
  if p.val = (false, vertices_541) then 18 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_593) then 1 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_46) then 16 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_2 1 0 1 2 4 46
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 1 4 5 6 7 484 164 2
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 1 0 1 2 7 46 302 3
cert_coverFacet 1 558
cert_cover_5 1 1 0 1 2 8 46 558 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 5 26 602 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 98 738 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 164 484 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1189

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_1190.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1190

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 781, 601, 361, 737, 897, 94, 334, 406, 626, 178, 354, 540, 692, 900, 73, 265, 521, 97, 161, 289, 577, 385, 641, 769, 78, 22, 262, 50, 82, 146, 98, 162, 290, 322, 386, 28, 268, 524, 148, 532, 388, 644, 772, 88, 536, 328, 176, 560, 592, 352, 608, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_781, vertices_601, vertices_361, vertices_737, vertices_897, vertices_94, vertices_334, vertices_406, vertices_626, vertices_178, vertices_354, vertices_540, vertices_692, vertices_900] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_641, vertices_769, vertices_78, vertices_22, vertices_262, vertices_50, vertices_82, vertices_146, vertices_98, vertices_162, vertices_290, vertices_322, vertices_386, vertices_28, vertices_268, vertices_524, vertices_148, vertices_532, vertices_388, vertices_644, vertices_772, vertices_88, vertices_536, vertices_328, vertices_176, vertices_560, vertices_592, vertices_352, vertices_608, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_781), (false, vertices_601), (false, vertices_361), (false, vertices_737), (false, vertices_897), (true, vertices_78), (true, vertices_22), (true, vertices_262), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_98), (true, vertices_322), (true, vertices_28), (true, vertices_148), (true, vertices_532), (true, vertices_388), (true, vertices_644), (true, vertices_176), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_644) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_560) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 897 22 262 50 82 146 98 322 28 148 532 388 644 176 560 419 78 781 601 361 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 1 3 6 7 406 22 3
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 1 3 4 6 8 692 148 2
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 78 94 3
cert_coverFacet 1 334
cert_cover_5 1 0 0 1 2 7 78 334 3
cert_coverFacet 2 406
cert_cover_5 2 1 0 1 3 6 22 406 3
cert_coverFacet 3 626
cert_cover_5 3 2 0 3 4 5 50 626 3
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 692
cert_cover_5 7 3 1 3 4 6 148 692 2
cert_coverFacet 8 900
cert_cover_2 8 6 1 7 8 388 900 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1190

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_1191.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1191

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 29, 77, 341, 665, 617, 961, 286, 302, 570, 658, 738, 418, 108, 484, 13, 21, 69, 25, 73, 521, 145, 273, 321, 577, 385, 641, 270, 26, 42, 146, 274, 530, 162, 290, 546, 386, 642, 28, 44, 76, 276, 100, 292, 324, 536, 104, 552, 656, 224, 608, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_29, vertices_77, vertices_341, vertices_665, vertices_617, vertices_961, vertices_286, vertices_302, vertices_570, vertices_658, vertices_738, vertices_418, vertices_108, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_69, vertices_25, vertices_73, vertices_521, vertices_145, vertices_273, vertices_321, vertices_577, vertices_385, vertices_641, vertices_270, vertices_26, vertices_42, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_28, vertices_44, vertices_76, vertices_276, vertices_100, vertices_292, vertices_324, vertices_536, vertices_104, vertices_552, vertices_656, vertices_224, vertices_608, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_29), (false, vertices_77), (false, vertices_341), (false, vertices_665), (false, vertices_617), (false, vertices_961), (true, vertices_270), (true, vertices_26), (true, vertices_42), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_44), (true, vertices_100), (true, vertices_292), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 22 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 15 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_77) then 1 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_270) then 16 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_29), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_77), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_270), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 26 3
cert_row_2 1 0 1 2 7 270
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 1 0 1 2 3 270 286 3
cert_coverFacet 1 302
cert_cover_5 1 1 0 1 2 4 270 302 3
cert_coverFacet 2 570
cert_cover_5 2 0 0 2 3 4 26 570 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 162 738 2
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 108
cert_cover_2 6 2 1 4 5 44 108 3
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 100 484 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1191

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_1192.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1192

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 173, 809, 393, 849, 737, 94, 206, 314, 394, 338, 60, 820, 724, 676, 41, 137, 265, 161, 545, 193, 321, 577, 385, 769, 78, 26, 138, 266, 82, 274, 194, 322, 386, 28, 44, 140, 52, 84, 532, 164, 548, 196, 644, 56, 296, 392, 304, 336, 592, 784, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_173, vertices_809, vertices_393, vertices_849, vertices_737, vertices_94, vertices_206, vertices_314, vertices_394, vertices_338, vertices_60, vertices_820, vertices_724, vertices_676] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_265, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_78, vertices_26, vertices_138, vertices_266, vertices_82, vertices_274, vertices_194, vertices_322, vertices_386, vertices_28, vertices_44, vertices_140, vertices_52, vertices_84, vertices_532, vertices_164, vertices_548, vertices_196, vertices_644, vertices_56, vertices_296, vertices_392, vertices_304, vertices_336, vertices_592, vertices_784, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_173), (false, vertices_809), (false, vertices_393), (false, vertices_849), (false, vertices_737), (true, vertices_78), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_82), (true, vertices_274), (true, vertices_28), (true, vertices_52), (true, vertices_84), (true, vertices_532), (true, vertices_548), (true, vertices_196), (true, vertices_644), (true, vertices_56), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_173) then 19 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (false, vertices_849) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_644) then 12 else
  if p.val = (true, vertices_56) then 13 else
  if p.val = (true, vertices_304) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 393 26 138 266 82 274 28 52 84 532 548 196 644 56 304 451 78 173 809 849 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 5 6 8 724 84 3
cert_row_2 1 0 1 2 5 78
cert_row_4 2 0 2 3 4 7 314 26 3
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 6 5 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 3 78 94 3
cert_coverFacet 1 206
cert_cover_5 1 1 0 1 2 6 78 206 3
cert_coverFacet 2 314
cert_cover_5 2 2 0 2 3 4 26 314 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 820
cert_cover_5 6 3 1 3 4 7 52 820 3
cert_coverFacet 7 724
cert_cover_5 7 0 1 3 5 6 84 724 3
cert_coverFacet 8 676
cert_cover_2 8 4 1 6 8 164 676 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1192

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_1193.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1193

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 789, 613, 453, 713, 777, 118, 342, 314, 170, 738, 450, 572, 792, 680, 69, 261, 517, 137, 265, 521, 193, 577, 385, 769, 86, 42, 138, 266, 50, 274, 98, 162, 194, 322, 386, 52, 276, 532, 100, 548, 324, 56, 280, 536, 168, 552, 648, 776, 784, 608, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_789, vertices_613, vertices_453, vertices_713, vertices_777, vertices_118, vertices_342, vertices_314, vertices_170, vertices_738, vertices_450, vertices_572, vertices_792, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_193, vertices_577, vertices_385, vertices_769, vertices_86, vertices_42, vertices_138, vertices_266, vertices_50, vertices_274, vertices_98, vertices_162, vertices_194, vertices_322, vertices_386, vertices_52, vertices_276, vertices_532, vertices_100, vertices_548, vertices_324, vertices_56, vertices_280, vertices_536, vertices_168, vertices_552, vertices_648, vertices_776, vertices_784, vertices_608, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_789), (false, vertices_613), (false, vertices_453), (false, vertices_713), (false, vertices_777), (true, vertices_86), (true, vertices_42), (true, vertices_50), (true, vertices_274), (true, vertices_98), (true, vertices_162), (true, vertices_194), (true, vertices_322), (true, vertices_52), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_552), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_713) then 23 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (true, vertices_86) then 17 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
cert_nodeAtPriority_51 777 42 50 274 98 162 194 322 52 56 280 536 168 552 672 395 86 789 613 453 713
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 7 314 42 2
cert_row_4 1 0 4 5 6 8 738 98 3
cert_row_2 2 0 1 3 5 86
cert_row_4 3 1 2 3 4 8 572 52 1
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 2 0 1 3 4 86 118 3
cert_coverFacet 1 342
cert_cover_5 1 2 0 1 3 7 86 342 3
cert_coverFacet 2 314
cert_cover_5 2 0 0 2 3 4 42 314 2
cert_coverFacet 3 170
cert_cover_2 3 2 0 4 6 42 170 3
cert_coverFacet 4 738
cert_cover_5 4 1 0 4 5 6 98 738 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 572
cert_cover_5 6 3 1 2 3 4 52 572 1
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coverFacet 8 680
cert_cover_2 8 4 2 6 8 168 680 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1193

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3723 : Certifies 3723 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1162.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3724 : Certifies 3724 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1163.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3725 : Certifies 3725 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1164.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3726 : Certifies 3726 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1165.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3727 : Certifies 3727 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1167.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3728 : Certifies 3728 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1168.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3729 : Certifies 3729 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1169.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3730 : Certifies 3730 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1170.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3731 : Certifies 3731 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1172.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3732 : Certifies 3732 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1173.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3733 : Certifies 3733 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1174.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3734 : Certifies 3734 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1175.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3735 : Certifies 3735 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1176.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3736 : Certifies 3736 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1177.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3737 : Certifies 3737 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1178.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3738 : Certifies 3738 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1179.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3739 : Certifies 3739 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1180.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3740 : Certifies 3740 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1181.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3741 : Certifies 3741 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1182.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3742 : Certifies 3742 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1183.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3743 : Certifies 3743 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1184.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3744 : Certifies 3744 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1185.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3745 : Certifies 3745 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1186.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3746 : Certifies 3746 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1187.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3747 : Certifies 3747 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1188.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3748 : Certifies 3748 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1189.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3749 : Certifies 3749 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1190.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3750 : Certifies 3750 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1191.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3751 : Certifies 3751 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1192.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3752 : Certifies 3752 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1193.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B123 (j : Fin 30) :
    Certifies (3723 + j.val) := by
  fin_cases j
  · exact projection_3723
  · exact projection_3724
  · exact projection_3725
  · exact projection_3726
  · exact projection_3727
  · exact projection_3728
  · exact projection_3729
  · exact projection_3730
  · exact projection_3731
  · exact projection_3732
  · exact projection_3733
  · exact projection_3734
  · exact projection_3735
  · exact projection_3736
  · exact projection_3737
  · exact projection_3738
  · exact projection_3739
  · exact projection_3740
  · exact projection_3741
  · exact projection_3742
  · exact projection_3743
  · exact projection_3744
  · exact projection_3745
  · exact projection_3746
  · exact projection_3747
  · exact projection_3748
  · exact projection_3749
  · exact projection_3750
  · exact projection_3751
  · exact projection_3752

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
