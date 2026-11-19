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
/- Source: ProjectionCertificates/R_m15e10q1_0649.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0649

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 781, 661, 421, 297, 737, 790, 122, 282, 778, 722, 610, 404, 472, 488, 133, 261, 517, 41, 265, 521, 161, 289, 545, 641, 26, 42, 266, 522, 82, 274, 530, 98, 546, 578, 770, 148, 276, 532, 388, 772, 88, 280, 104, 296, 456, 776, 208, 400, 656, 224, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_781, vertices_661, vertices_421, vertices_297, vertices_737, vertices_790, vertices_122, vertices_282, vertices_778, vertices_722, vertices_610, vertices_404, vertices_472, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_641, vertices_26, vertices_42, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_98, vertices_546, vertices_578, vertices_770, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_88, vertices_280, vertices_104, vertices_296, vertices_456, vertices_776, vertices_208, vertices_400, vertices_656, vertices_224, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_781), (false, vertices_661), (false, vertices_421), (false, vertices_297), (false, vertices_737), (true, vertices_26), (true, vertices_266), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_578), (true, vertices_770), (true, vertices_276), (true, vertices_88), (true, vertices_280), (true, vertices_104), (true, vertices_456), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_456) then 22 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(true, vertices_456), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_2 1 2 5 6 7 456
cert_row_4 2 0 2 3 4 5 122 26 3
cert_row_4 3 0 3 5 6 8 722 82 3
cert_rows
cert_pivot_2 1 7 2 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 4 26 122 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 722
cert_cover_5 4 3 0 3 5 6 82 722 3
cert_coverFacet 5 610
cert_cover_2 5 4 0 5 8 98 610 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 472
cert_cover_5 7 1 2 3 5 6 88 472 3
cert_coverFacet 8 488
cert_cover_5 8 1 2 4 5 6 104 488 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0649

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0650.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0650

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 115, 275, 707, 653, 453, 337, 570, 786, 610, 796, 396, 440, 744, 496, 19, 67, 259, 515, 133, 261, 517, 81, 273, 193, 321, 641, 50, 274, 530, 98, 546, 578, 770, 140, 268, 524, 388, 772, 56, 280, 536, 168, 552, 392, 648, 112, 432, 336, 784, 224, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_115, vertices_275, vertices_707, vertices_653, vertices_453, vertices_337, vertices_570, vertices_786, vertices_610, vertices_796, vertices_396, vertices_440, vertices_744, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_259, vertices_515, vertices_133, vertices_261, vertices_517, vertices_81, vertices_273, vertices_193, vertices_321, vertices_641, vertices_50, vertices_274, vertices_530, vertices_98, vertices_546, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_388, vertices_772, vertices_56, vertices_280, vertices_536, vertices_168, vertices_552, vertices_392, vertices_648, vertices_112, vertices_432, vertices_336, vertices_784, vertices_224, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_115), (false, vertices_275), (false, vertices_707), (false, vertices_653), (false, vertices_453), (false, vertices_337), (true, vertices_530), (true, vertices_546), (true, vertices_268), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_552), (true, vertices_392), (true, vertices_432), (true, vertices_784), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_115) then 16 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_337) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_432) then 23 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 50 1
cert_row_4 1 1 2 3 7 8 796 268 2
cert_row_2 2 3 4 6 7 432
cert_row_4 3 2 4 5 6 8 744 168 2
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 570
cert_cover_5 0 0 0 2 3 4 50 570 1
cert_coverFacet 1 786
cert_cover_2 1 3 0 7 8 274 786 3
cert_coverFacet 2 610
cert_cover_2 2 4 0 5 8 98 610 3
cert_coverFacet 3 796
cert_cover_5 3 1 1 2 3 7 268 796 2
cert_coverFacet 4 396
cert_cover_2 4 2 1 6 7 140 396 3
cert_coverFacet 5 440
cert_cover_5 5 2 2 3 4 6 56 440 3
cert_coverFacet 6 744
cert_cover_5 6 3 2 4 5 6 168 744 2
cert_coverFacet 7 496
cert_cover_5 7 2 3 4 5 6 112 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0650

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0651.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0651

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 653, 613, 197, 457, 849, 678, 426, 650, 626, 306, 786, 116, 436, 468, 69, 133, 517, 137, 265, 521, 193, 321, 577, 769, 138, 266, 522, 50, 274, 530, 162, 290, 546, 642, 770, 52, 84, 404, 100, 164, 548, 196, 644, 392, 648, 112, 304, 336, 592, 784, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_653, vertices_613, vertices_197, vertices_457, vertices_849, vertices_678, vertices_426, vertices_650, vertices_626, vertices_306, vertices_786, vertices_116, vertices_436, vertices_468] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_577, vertices_769, vertices_138, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_404, vertices_100, vertices_164, vertices_548, vertices_196, vertices_644, vertices_392, vertices_648, vertices_112, vertices_304, vertices_336, vertices_592, vertices_784, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_653), (false, vertices_613), (false, vertices_197), (false, vertices_457), (false, vertices_849), (true, vertices_138), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_52), (true, vertices_84), (true, vertices_404), (true, vertices_164), (true, vertices_112), (true, vertices_304), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_404) then 20 else
  if p.val = (true, vertices_164) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 138 2
cert_row_2 1 1 3 6 7 404
cert_row_4 2 0 1 4 6 8 678 162 1
cert_row_4 3 0 3 4 5 8 626 50 3
cert_rows
cert_pivot_2 2 7 1 0
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 162 678 1
cert_coverFacet 1 426
cert_cover_5 1 0 0 2 4 6 138 426 2
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 626
cert_cover_5 3 3 0 3 4 5 50 626 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 116
cert_cover_2 6 3 1 4 5 52 116 3
cert_coverFacet 7 436
cert_cover_5 7 1 1 3 4 6 52 436 3
cert_coverFacet 8 468
cert_cover_5 8 1 1 3 5 6 84 468 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0651

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0652.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0652

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 421, 345, 681, 393, 625, 305, 206, 678, 326, 774, 650, 850, 460, 820, 73, 137, 265, 521, 49, 81, 273, 161, 289, 545, 577, 385, 70, 134, 262, 518, 74, 138, 522, 322, 578, 642, 770, 204, 164, 292, 548, 324, 388, 772, 328, 392, 648, 304, 560, 336, 592, 784, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_421, vertices_345, vertices_681, vertices_393, vertices_625, vertices_305, vertices_206, vertices_678, vertices_326, vertices_774, vertices_650, vertices_850, vertices_460, vertices_820] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_521, vertices_49, vertices_81, vertices_273, vertices_161, vertices_289, vertices_545, vertices_577, vertices_385, vertices_70, vertices_134, vertices_262, vertices_518, vertices_74, vertices_138, vertices_522, vertices_322, vertices_578, vertices_642, vertices_770, vertices_204, vertices_164, vertices_292, vertices_548, vertices_324, vertices_388, vertices_772, vertices_328, vertices_392, vertices_648, vertices_304, vertices_560, vertices_336, vertices_592, vertices_784, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_421), (false, vertices_345), (false, vertices_681), (false, vertices_393), (false, vertices_625), (false, vertices_305), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_322), (true, vertices_642), (true, vertices_770), (true, vertices_204), (true, vertices_548), (true, vertices_324), (true, vertices_772), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_262) then 4 else
  if p.val = (true, vertices_518) then 5 else
  if p.val = (true, vertices_138) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_204) then 18 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_784) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 6 204
cert_row_4 1 0 1 4 6 8 678 134 2
cert_row_4 2 0 3 5 7 8 850 322 1
cert_row_4 3 1 3 4 7 8 820 292 1
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 70 206 2
cert_coverFacet 1 678
cert_cover_5 1 1 0 1 4 6 134 678 2
cert_coverFacet 2 326
cert_cover_2 2 1 0 5 7 70 326 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 850
cert_cover_5 5 2 0 3 5 7 322 850 1
cert_coverFacet 6 460
cert_cover_5 6 0 1 2 5 7 204 460 3
cert_coverFacet 7 820
cert_cover_5 7 3 1 3 4 7 292 820 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0652

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0653.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0653

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 781, 53, 405, 613, 689, 590, 458, 778, 738, 60, 284, 108, 376, 496, 21, 37, 261, 517, 49, 145, 545, 385, 641, 769, 74, 266, 522, 194, 578, 386, 642, 770, 28, 44, 76, 268, 524, 52, 276, 100, 580, 56, 280, 104, 328, 776, 368, 176, 400, 224, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_781, vertices_53, vertices_405, vertices_613, vertices_689, vertices_590, vertices_458, vertices_778, vertices_738, vertices_60, vertices_284, vertices_108, vertices_376, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_261, vertices_517, vertices_49, vertices_145, vertices_545, vertices_385, vertices_641, vertices_769, vertices_74, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_76, vertices_268, vertices_524, vertices_52, vertices_276, vertices_100, vertices_580, vertices_56, vertices_280, vertices_104, vertices_328, vertices_776, vertices_368, vertices_176, vertices_400, vertices_224, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_781), (false, vertices_53), (false, vertices_405), (false, vertices_613), (false, vertices_689), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_194), (true, vertices_578), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_56), (true, vertices_280), (true, vertices_104), (true, vertices_328), (true, vertices_368), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_53) then 0 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_368) then 24 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_53), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_368), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 7 368
cert_row_4 1 0 1 2 5 8 590 74 1
cert_row_4 2 0 2 5 6 7 458 74 3
cert_row_4 3 0 4 5 6 8 738 194 1
cert_rows
cert_pivot_2 3 1 2 0
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 74 590 1
cert_coverFacet 1 458
cert_cover_5 1 2 0 2 5 6 74 458 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 738
cert_cover_5 3 3 0 4 5 6 194 738 1
cert_coverFacet 4 60
cert_cover_2 4 2 1 3 4 28 60 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 108
cert_cover_2 6 2 1 4 5 44 108 3
cert_coverFacet 7 376
cert_cover_5 7 0 2 3 4 5 56 376 3
cert_coverFacet 8 496
cert_cover_5 8 0 3 4 5 6 368 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0653

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0654.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0654

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 837, 57, 345, 617, 433, 422, 710, 774, 186, 666, 554, 468, 600, 720, 25, 41, 73, 49, 273, 289, 545, 321, 577, 769, 134, 262, 518, 154, 42, 522, 162, 290, 546, 642, 770, 196, 324, 580, 388, 772, 56, 88, 536, 552, 584, 176, 208, 336, 592, 400, 656, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_837, vertices_57, vertices_345, vertices_617, vertices_433, vertices_422, vertices_710, vertices_774, vertices_186, vertices_666, vertices_554, vertices_468, vertices_600, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_73, vertices_49, vertices_273, vertices_289, vertices_545, vertices_321, vertices_577, vertices_769, vertices_134, vertices_262, vertices_518, vertices_154, vertices_42, vertices_522, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_56, vertices_88, vertices_536, vertices_552, vertices_584, vertices_176, vertices_208, vertices_336, vertices_592, vertices_400, vertices_656, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_837), (false, vertices_57), (false, vertices_345), (false, vertices_617), (false, vertices_433), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_154), (true, vertices_42), (true, vertices_522), (true, vertices_162), (true, vertices_642), (true, vertices_196), (true, vertices_388), (true, vertices_536), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_154) then 17 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 57 134 262 518 42 522 162 642 196 388 536 208 592 656 704 803 154 837 345 617 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 0 1 4 6 7 422 134 2
cert_row_4 2 0 1 5 6 8 710 134 2
cert_row_4 3 1 3 5 6 7 468 196 1
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 1 0 1 4 6 134 422 2
cert_coverFacet 1 710
cert_cover_5 1 2 0 1 5 6 134 710 2
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 186
cert_cover_5 3 0 0 2 3 4 154 186 3
cert_coverFacet 4 666
cert_cover_5 4 0 0 2 3 8 154 666 3
cert_coverFacet 5 554
cert_cover_2 5 2 0 4 8 42 554 3
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 196 468 1
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coverFacet 8 720
cert_cover_2 8 5 3 6 8 208 720 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0654

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0655.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0655

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 39, 659, 227, 301, 105, 713, 406, 534, 422, 780, 852, 872, 496, 720, 7, 35, 131, 515, 13, 37, 41, 73, 521, 97, 193, 641, 22, 38, 390, 518, 146, 530, 162, 268, 524, 276, 532, 292, 772, 104, 296, 584, 776, 208, 336, 592, 400, 656, 224, 352, 416, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_39, vertices_659, vertices_227, vertices_301, vertices_105, vertices_713, vertices_406, vertices_534, vertices_422, vertices_780, vertices_852, vertices_872, vertices_496, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_35, vertices_131, vertices_515, vertices_13, vertices_37, vertices_41, vertices_73, vertices_521, vertices_97, vertices_193, vertices_641, vertices_22, vertices_38, vertices_390, vertices_518, vertices_146, vertices_530, vertices_162, vertices_268, vertices_524, vertices_276, vertices_532, vertices_292, vertices_772, vertices_104, vertices_296, vertices_584, vertices_776, vertices_208, vertices_336, vertices_592, vertices_400, vertices_656, vertices_224, vertices_352, vertices_416, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_39), (false, vertices_659), (false, vertices_227), (false, vertices_301), (false, vertices_105), (false, vertices_713), (true, vertices_22), (true, vertices_390), (true, vertices_276), (true, vertices_532), (true, vertices_772), (true, vertices_776), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_400), (true, vertices_352), (true, vertices_416), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 14 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 15 else
  if p.val = (false, vertices_39) then 0 else
  if p.val = (false, vertices_659) then 19 else
  if p.val = (false, vertices_227) then 20 else
  if p.val = (false, vertices_301) then 16 else
  if p.val = (false, vertices_105) then 1 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_390) then 17 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_39), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_105), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_4 1 1 3 5 7 8 852 276 2
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 5 6 7 496 208 1
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 22 406 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 422
cert_cover_5 2 0 0 1 4 6 38 422 3
cert_coverFacet 3 780
cert_cover_2 3 2 1 7 8 268 780 3
cert_coverFacet 4 852
cert_cover_5 4 1 1 3 5 7 276 852 2
cert_coverFacet 5 872
cert_cover_5 5 2 2 4 5 7 104 872 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 208 496 1
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0655

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0656.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0656

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 781, 357, 165, 645, 345, 617, 902, 794, 626, 178, 402, 244, 468, 600, 37, 133, 261, 517, 73, 265, 521, 97, 161, 545, 321, 641, 50, 146, 274, 530, 162, 546, 386, 642, 770, 212, 100, 164, 324, 388, 644, 772, 88, 280, 536, 584, 776, 112, 176, 336, 592, 400, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_781, vertices_357, vertices_165, vertices_645, vertices_345, vertices_617, vertices_902, vertices_794, vertices_626, vertices_178, vertices_402, vertices_244, vertices_468, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_321, vertices_641, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_212, vertices_100, vertices_164, vertices_324, vertices_388, vertices_644, vertices_772, vertices_88, vertices_280, vertices_536, vertices_584, vertices_776, vertices_112, vertices_176, vertices_336, vertices_592, vertices_400, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_781), (false, vertices_357), (false, vertices_165), (false, vertices_645), (false, vertices_345), (false, vertices_617), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_770), (true, vertices_212), (true, vertices_388), (true, vertices_536), (true, vertices_112), (true, vertices_176), (true, vertices_592), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_357) then 18 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_645) then 1 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_212) then 19 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_645), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 7 8 794 274 1
cert_row_4 1 0 1 6 7 8 902 386 1
cert_row_2 2 1 3 5 6 212
cert_row_4 3 0 3 4 5 8 626 50 3
cert_rows
cert_pivot_2 2 7 1 0
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 794
cert_cover_5 1 0 0 2 3 7 274 794 1
cert_coverFacet 2 626
cert_cover_5 2 3 0 3 4 5 50 626 3
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 244
cert_cover_5 5 2 1 3 4 5 212 244 2
cert_coverFacet 6 468
cert_cover_5 6 2 1 3 5 7 212 468 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0656

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0657.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0657

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 23, 563, 269, 405, 665, 457, 310, 358, 582, 738, 844, 712, 496, 688, 7, 19, 515, 13, 21, 261, 137, 265, 521, 145, 529, 385, 22, 294, 70, 518, 50, 98, 546, 578, 268, 524, 276, 324, 580, 200, 328, 584, 648, 176, 304, 560, 400, 656, 224, 352, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_23, vertices_563, vertices_269, vertices_405, vertices_665, vertices_457, vertices_310, vertices_358, vertices_582, vertices_738, vertices_844, vertices_712, vertices_496, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_19, vertices_515, vertices_13, vertices_21, vertices_261, vertices_137, vertices_265, vertices_521, vertices_145, vertices_529, vertices_385, vertices_22, vertices_294, vertices_70, vertices_518, vertices_50, vertices_98, vertices_546, vertices_578, vertices_268, vertices_524, vertices_276, vertices_324, vertices_580, vertices_200, vertices_328, vertices_584, vertices_648, vertices_176, vertices_304, vertices_560, vertices_400, vertices_656, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_23), (false, vertices_563), (false, vertices_269), (false, vertices_405), (false, vertices_665), (false, vertices_457), (true, vertices_294), (true, vertices_70), (true, vertices_98), (true, vertices_578), (true, vertices_324), (true, vertices_580), (true, vertices_584), (true, vertices_176), (true, vertices_304), (true, vertices_224), (true, vertices_352), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 15 else
  if p.val = (false, vertices_23) then 0 else
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_269) then 1 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (true, vertices_294) then 17 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_23), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_294), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 5 7 8 844 268 2
cert_row_2 1 0 1 4 7 294
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 1 0 1 3 4 22 310 3
cert_coverFacet 1 358
cert_cover_5 1 1 0 1 4 5 294 358 3
cert_coverFacet 2 582
cert_cover_2 2 1 0 5 8 70 582 3
cert_coverFacet 3 738
cert_cover_5 3 2 0 4 5 6 98 738 3
cert_coverFacet 4 844
cert_cover_5 4 0 1 2 5 7 268 844 2
cert_coverFacet 5 712
cert_cover_2 5 5 2 6 8 200 712 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 176 496 2
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0657

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0658.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0658

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 541, 269, 341, 361, 713, 209, 406, 534, 422, 550, 738, 812, 616, 496, 13, 21, 261, 73, 265, 521, 81, 145, 529, 193, 321, 641, 22, 38, 390, 518, 146, 530, 162, 546, 642, 268, 524, 276, 532, 292, 548, 104, 296, 552, 584, 208, 336, 400, 224, 352, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_541, vertices_269, vertices_341, vertices_361, vertices_713, vertices_209, vertices_406, vertices_534, vertices_422, vertices_550, vertices_738, vertices_812, vertices_616, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_261, vertices_73, vertices_265, vertices_521, vertices_81, vertices_145, vertices_529, vertices_193, vertices_321, vertices_641, vertices_22, vertices_38, vertices_390, vertices_518, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_268, vertices_524, vertices_276, vertices_532, vertices_292, vertices_548, vertices_104, vertices_296, vertices_552, vertices_584, vertices_208, vertices_336, vertices_400, vertices_224, vertices_352, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_541), (false, vertices_269), (false, vertices_341), (false, vertices_361), (false, vertices_713), (false, vertices_209), (true, vertices_22), (true, vertices_38), (true, vertices_390), (true, vertices_518), (true, vertices_162), (true, vertices_546), (true, vertices_292), (true, vertices_548), (true, vertices_552), (true, vertices_400), (true, vertices_224), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_541) then 18 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_209) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_38) then 3 else
  if p.val = (true, vertices_390) then 16 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
cert_nodeAtPriority_25 0 269 1 209 22 38 518 162 546 292 548 552 400 224 608 416 659 390 541 341 361 713
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 7 8 812 268 2
cert_row_2 1 0 1 6 7 390
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 3 4 5 6 7 496 208 1
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 1 0 1 3 6 22 406 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 422
cert_cover_5 2 1 0 1 4 6 38 422 3
cert_coverFacet 3 550
cert_cover_2 3 1 0 4 8 38 550 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 162 738 2
cert_coverFacet 5 812
cert_cover_5 5 0 1 2 4 7 268 812 2
cert_coverFacet 6 616
cert_cover_2 6 4 2 5 8 104 616 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 208 496 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0658

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0659.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0659

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 653, 269, 341, 613, 233, 329, 790, 906, 242, 626, 402, 780, 596, 472, 13, 69, 261, 517, 73, 137, 265, 97, 161, 545, 321, 641, 114, 146, 274, 530, 162, 546, 386, 642, 770, 268, 524, 84, 276, 532, 580, 772, 200, 328, 392, 648, 776, 208, 336, 592, 400, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_653, vertices_269, vertices_341, vertices_613, vertices_233, vertices_329, vertices_790, vertices_906, vertices_242, vertices_626, vertices_402, vertices_780, vertices_596, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_97, vertices_161, vertices_545, vertices_321, vertices_641, vertices_114, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_580, vertices_772, vertices_200, vertices_328, vertices_392, vertices_648, vertices_776, vertices_208, vertices_336, vertices_592, vertices_400, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_653), (false, vertices_269), (false, vertices_341), (false, vertices_613), (false, vertices_233), (false, vertices_329), (true, vertices_114), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_770), (true, vertices_532), (true, vertices_772), (true, vertices_392), (true, vertices_776), (true, vertices_208), (true, vertices_592), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (true, vertices_114) then 16 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 269 1 329 146 274 530 386 770 532 772 392 776 208 592 400 675 114 653 341 613 233
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 5 114
cert_row_4 1 0 1 3 7 8 790 274 1
cert_row_4 2 0 2 6 7 8 906 386 1
cert_row_4 3 2 3 5 6 7 472 200 1
cert_rows
cert_pivot_2 4 1 0 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 274 790 1
cert_coverFacet 1 906
cert_cover_5 1 2 0 2 6 7 386 906 1
cert_coverFacet 2 242
cert_cover_5 2 0 0 3 4 6 114 242 3
cert_coverFacet 3 626
cert_cover_5 3 0 0 3 4 8 114 626 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 200 472 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0659

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0660.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0660

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 541, 149, 229, 837, 345, 209, 678, 410, 666, 866, 418, 660, 612, 496, 21, 69, 133, 517, 25, 265, 521, 81, 145, 193, 321, 769, 154, 266, 522, 162, 290, 546, 386, 642, 770, 148, 532, 100, 164, 548, 580, 644, 280, 536, 208, 336, 400, 656, 224, 352, 608, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_541, vertices_149, vertices_229, vertices_837, vertices_345, vertices_209, vertices_678, vertices_410, vertices_666, vertices_866, vertices_418, vertices_660, vertices_612, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_133, vertices_517, vertices_25, vertices_265, vertices_521, vertices_81, vertices_145, vertices_193, vertices_321, vertices_769, vertices_154, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_280, vertices_536, vertices_208, vertices_336, vertices_400, vertices_656, vertices_224, vertices_352, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_541), (false, vertices_149), (false, vertices_229), (false, vertices_837), (false, vertices_345), (false, vertices_209), (true, vertices_154), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_548), (true, vertices_644), (true, vertices_400), (true, vertices_656), (true, vertices_352), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_541) then 18 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (false, vertices_209) then 1 else
  if p.val = (true, vertices_154) then 16 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 149 1 209 162 290 546 386 642 548 644 400 656 352 608 416 779 154 541 229 837 345
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 3 4 5 6 7 496 208 1
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 7 154 410 3
cert_coverFacet 2 666
cert_cover_5 2 0 0 2 3 8 154 666 3
cert_coverFacet 3 866
cert_cover_5 3 2 0 4 5 7 290 866 2
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 660
cert_cover_2 5 3 1 6 8 148 660 3
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 208 496 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0660

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0661.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0661

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 661, 421, 837, 297, 329, 737, 58, 538, 842, 242, 722, 796, 404, 440, 133, 261, 517, 41, 73, 265, 97, 161, 289, 321, 577, 641, 26, 42, 74, 522, 50, 210, 530, 98, 578, 148, 276, 532, 388, 772, 56, 280, 536, 296, 328, 776, 176, 400, 656, 224, 416, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_661, vertices_421, vertices_837, vertices_297, vertices_329, vertices_737, vertices_58, vertices_538, vertices_842, vertices_242, vertices_722, vertices_796, vertices_404, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_73, vertices_265, vertices_97, vertices_161, vertices_289, vertices_321, vertices_577, vertices_641, vertices_26, vertices_42, vertices_74, vertices_522, vertices_50, vertices_210, vertices_530, vertices_98, vertices_578, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_56, vertices_280, vertices_536, vertices_296, vertices_328, vertices_776, vertices_176, vertices_400, vertices_656, vertices_224, vertices_416, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_661), (false, vertices_421), (false, vertices_837), (false, vertices_297), (false, vertices_329), (false, vertices_737), (true, vertices_26), (true, vertices_522), (true, vertices_50), (true, vertices_210), (true, vertices_530), (true, vertices_578), (true, vertices_276), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_776), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 15 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_210) then 16 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_4 0 1 2 3 7 8 796 276 1
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_2 2 0 3 5 6 210
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 58
cert_cover_2 0 2 0 3 4 26 58 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 842
cert_cover_5 2 1 0 2 5 7 74 842 3
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 50 242 3
cert_coverFacet 4 722
cert_cover_5 4 2 0 3 5 8 210 722 3
cert_coverFacet 5 796
cert_cover_5 5 0 1 2 3 7 276 796 1
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 440
cert_cover_5 7 3 2 3 4 6 56 440 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0661

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0662.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0662

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 901, 569, 425, 713, 305, 118, 278, 710, 774, 618, 562, 460, 372, 360, 41, 137, 521, 49, 273, 529, 289, 385, 641, 769, 22, 70, 262, 518, 50, 274, 530, 98, 546, 578, 770, 116, 276, 196, 324, 388, 644, 772, 104, 296, 552, 200, 328, 584, 392, 304, 560, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_901, vertices_569, vertices_425, vertices_713, vertices_305, vertices_118, vertices_278, vertices_710, vertices_774, vertices_618, vertices_562, vertices_460, vertices_372, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_521, vertices_49, vertices_273, vertices_529, vertices_289, vertices_385, vertices_641, vertices_769, vertices_22, vertices_70, vertices_262, vertices_518, vertices_50, vertices_274, vertices_530, vertices_98, vertices_546, vertices_578, vertices_770, vertices_116, vertices_276, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_104, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_304, vertices_560, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_901), (false, vertices_569), (false, vertices_425), (false, vertices_713), (false, vertices_305), (true, vertices_22), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_98), (true, vertices_546), (true, vertices_578), (true, vertices_116), (true, vertices_276), (true, vertices_196), (true, vertices_324), (true, vertices_104), (true, vertices_328), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_901) then 18 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_713) then 23 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_116) then 19 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
cert_nodeAtPriority_43 305 2 22 1 70 262 518 50 98 546 578 276 196 324 104 328 352 787 901 116 569 425 713
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 4 5 116
cert_row_4 1 0 2 4 5 8 618 98 1
cert_row_4 2 0 1 5 6 8 710 70 3
cert_row_4 3 1 2 5 6 7 460 196 1
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 0 0 1 3 4 22 118 3
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 710
cert_cover_5 2 2 0 1 5 6 70 710 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 618
cert_cover_5 4 1 0 2 4 5 98 618 1
cert_coverFacet 5 562
cert_cover_2 5 3 0 4 8 50 562 3
cert_coverFacet 6 460
cert_cover_5 6 3 1 2 5 6 196 460 1
cert_coverFacet 7 372
cert_cover_5 7 0 1 3 4 7 116 372 3
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0662

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0663.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0663

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 589, 789, 453, 401, 737, 782, 314, 618, 178, 786, 674, 236, 428, 432, 69, 261, 517, 145, 273, 529, 193, 577, 385, 641, 42, 266, 522, 50, 146, 274, 530, 162, 546, 642, 770, 172, 76, 268, 524, 196, 388, 772, 104, 296, 584, 176, 304, 400, 784, 224, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_589, vertices_789, vertices_453, vertices_401, vertices_737, vertices_782, vertices_314, vertices_618, vertices_178, vertices_786, vertices_674, vertices_236, vertices_428, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_641, vertices_42, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_642, vertices_770, vertices_172, vertices_76, vertices_268, vertices_524, vertices_196, vertices_388, vertices_772, vertices_104, vertices_296, vertices_584, vertices_176, vertices_304, vertices_400, vertices_784, vertices_224, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_589), (false, vertices_789), (false, vertices_453), (false, vertices_401), (false, vertices_737), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_162), (true, vertices_546), (true, vertices_770), (true, vertices_172), (true, vertices_268), (true, vertices_104), (true, vertices_296), (true, vertices_176), (true, vertices_304), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_172) then 19 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_172), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 6 172
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 2 3 4 7 314 42 2
cert_row_4 3 0 2 4 5 8 618 42 3
cert_rows
cert_pivot_2 6 1 3 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 314
cert_cover_5 1 2 0 2 3 4 42 314 2
cert_coverFacet 2 618
cert_cover_5 2 3 0 2 4 5 42 618 3
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 236
cert_cover_5 6 0 1 2 4 5 172 236 3
cert_coverFacet 7 428
cert_cover_5 7 0 1 2 4 7 172 428 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0663

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0664.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0664

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 781, 421, 617, 297, 689, 342, 150, 774, 842, 626, 658, 468, 488, 240, 133, 261, 517, 41, 265, 521, 161, 289, 545, 641, 22, 134, 262, 518, 82, 146, 530, 322, 578, 642, 770, 340, 148, 388, 772, 104, 296, 328, 584, 776, 112, 176, 560, 208, 656, 224, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_781, vertices_421, vertices_617, vertices_297, vertices_689, vertices_342, vertices_150, vertices_774, vertices_842, vertices_626, vertices_658, vertices_468, vertices_488, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_641, vertices_22, vertices_134, vertices_262, vertices_518, vertices_82, vertices_146, vertices_530, vertices_322, vertices_578, vertices_642, vertices_770, vertices_340, vertices_148, vertices_388, vertices_772, vertices_104, vertices_296, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_656, vertices_224, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_781), (false, vertices_421), (false, vertices_617), (false, vertices_297), (false, vertices_689), (true, vertices_22), (true, vertices_262), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_340), (true, vertices_148), (true, vertices_328), (true, vertices_112), (true, vertices_208), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_340) then 22 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_340), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 5 7 340
cert_row_4 1 0 3 4 5 8 626 82 2
cert_row_4 2 0 2 5 7 8 842 322 1
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 22 342 3
cert_coverFacet 1 150
cert_cover_2 1 1 0 3 6 22 150 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 842
cert_cover_5 3 2 0 2 5 7 322 842 1
cert_coverFacet 4 626
cert_cover_5 4 1 0 3 4 5 82 626 2
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 468
cert_cover_5 6 0 1 3 5 6 340 468 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coverFacet 8 240
cert_cover_2 8 4 3 5 6 112 240 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0664

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0665.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0665

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 333, 789, 613, 433, 353, 654, 410, 794, 178, 738, 204, 780, 708, 488, 69, 261, 517, 49, 273, 529, 97, 289, 545, 321, 282, 138, 522, 50, 146, 530, 162, 546, 642, 76, 140, 268, 524, 196, 580, 644, 772, 200, 328, 392, 776, 176, 400, 784, 224, 352, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_333, vertices_789, vertices_613, vertices_433, vertices_353, vertices_654, vertices_410, vertices_794, vertices_178, vertices_738, vertices_204, vertices_780, vertices_708, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_321, vertices_282, vertices_138, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_76, vertices_140, vertices_268, vertices_524, vertices_196, vertices_580, vertices_644, vertices_772, vertices_200, vertices_328, vertices_392, vertices_776, vertices_176, vertices_400, vertices_784, vertices_224, vertices_352, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_333), (false, vertices_789), (false, vertices_613), (false, vertices_433), (false, vertices_353), (true, vertices_282), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_162), (true, vertices_642), (true, vertices_140), (true, vertices_524), (true, vertices_196), (true, vertices_644), (true, vertices_200), (true, vertices_392), (true, vertices_776), (true, vertices_224), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_353) then 0 else
  if p.val = (true, vertices_282) then 17 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_19 0 353 1 138 522 146 162 642 140 524 196 644 200 392 776 224 704 563 282 333 789 613 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 7 282
cert_row_4 1 0 1 2 6 8 654 138 1
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 2 4 5 6 7 488 200 1
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 138 654 1
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 6 282 410 3
cert_coverFacet 2 794
cert_cover_5 2 0 0 2 3 8 282 794 3
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 162 738 2
cert_coverFacet 5 204
cert_cover_2 5 2 1 5 6 76 204 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 200 488 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0665

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0666.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0666

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 93, 397, 229, 121, 777, 929, 286, 58, 778, 562, 850, 340, 964, 752, 13, 69, 133, 89, 41, 265, 521, 97, 161, 545, 385, 769, 26, 42, 266, 522, 50, 274, 530, 546, 770, 28, 268, 84, 276, 196, 324, 388, 56, 776, 112, 560, 336, 592, 224, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_93, vertices_397, vertices_229, vertices_121, vertices_777, vertices_929, vertices_286, vertices_58, vertices_778, vertices_562, vertices_850, vertices_340, vertices_964, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_133, vertices_89, vertices_41, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_385, vertices_769, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_546, vertices_770, vertices_28, vertices_268, vertices_84, vertices_276, vertices_196, vertices_324, vertices_388, vertices_56, vertices_776, vertices_112, vertices_560, vertices_336, vertices_592, vertices_224, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_93), (false, vertices_397), (false, vertices_229), (false, vertices_121), (false, vertices_777), (false, vertices_929), (true, vertices_26), (true, vertices_266), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_770), (true, vertices_276), (true, vertices_324), (true, vertices_560), (true, vertices_336), (true, vertices_592), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 15 else
  if p.val = (false, vertices_93) then 20 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_121) then 21 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_929) then 24 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_704) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 7 286 26 1
cert_row_4 1 0 3 5 7 8 850 274 2
cert_row_4 2 1 5 6 7 8 964 196 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 26 286 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 850
cert_cover_5 4 1 0 3 5 7 274 850 2
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 964
cert_cover_5 6 2 1 5 6 7 196 964 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0666

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0667.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0667

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 709, 57, 281, 617, 241, 913, 558, 358, 902, 58, 282, 370, 468, 612, 25, 41, 265, 521, 49, 145, 273, 97, 193, 577, 641, 769, 38, 262, 518, 26, 42, 266, 522, 50, 274, 354, 770, 100, 548, 196, 324, 580, 388, 644, 56, 280, 552, 112, 208, 336, 400, 608, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_709, vertices_57, vertices_281, vertices_617, vertices_241, vertices_913, vertices_558, vertices_358, vertices_902, vertices_58, vertices_282, vertices_370, vertices_468, vertices_612] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_521, vertices_49, vertices_145, vertices_273, vertices_97, vertices_193, vertices_577, vertices_641, vertices_769, vertices_38, vertices_262, vertices_518, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_354, vertices_770, vertices_100, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_56, vertices_280, vertices_552, vertices_112, vertices_208, vertices_336, vertices_400, vertices_608, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_709), (false, vertices_57), (false, vertices_281), (false, vertices_617), (false, vertices_241), (false, vertices_913), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_42), (true, vertices_50), (true, vertices_274), (true, vertices_354), (true, vertices_100), (true, vertices_548), (true, vertices_324), (true, vertices_388), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 21 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (false, vertices_913) then 23 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_42) then 6 else
  if p.val = (true, vertices_50) then 7 else
  if p.val = (true, vertices_274) then 8 else
  if p.val = (true, vertices_354) then 16 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_336) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_57), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_354), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 38 2
cert_row_2 1 0 4 5 7 354
cert_row_4 2 0 1 6 7 8 902 262 2
cert_row_4 3 1 3 5 6 7 468 196 1
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 38 558 2
cert_coverFacet 1 358
cert_cover_5 1 1 0 1 4 5 38 358 3
cert_coverFacet 2 902
cert_cover_5 2 2 0 1 6 7 262 902 2
cert_coverFacet 3 58
cert_cover_2 3 2 0 3 4 26 58 3
cert_coverFacet 4 282
cert_cover_2 4 2 0 3 7 26 282 3
cert_coverFacet 5 370
cert_cover_5 5 1 0 3 4 5 50 370 3
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 196 468 1
cert_coverFacet 7 612
cert_cover_2 7 4 1 5 8 100 612 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0667

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0668.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0668

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 837, 361, 625, 433, 897, 30, 334, 534, 902, 186, 394, 572, 620, 424, 49, 145, 529, 97, 289, 321, 577, 385, 641, 769, 14, 22, 262, 518, 26, 138, 266, 146, 530, 386, 642, 28, 556, 76, 532, 324, 580, 772, 56, 104, 168, 296, 328, 392, 176, 560, 608, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_837, vertices_361, vertices_625, vertices_433, vertices_897, vertices_30, vertices_334, vertices_534, vertices_902, vertices_186, vertices_394, vertices_572, vertices_620, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_529, vertices_97, vertices_289, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_146, vertices_530, vertices_386, vertices_642, vertices_28, vertices_556, vertices_76, vertices_532, vertices_324, vertices_580, vertices_772, vertices_56, vertices_104, vertices_168, vertices_296, vertices_328, vertices_392, vertices_176, vertices_560, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_837), (false, vertices_361), (false, vertices_625), (false, vertices_433), (false, vertices_897), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_386), (true, vertices_28), (true, vertices_556), (true, vertices_76), (true, vertices_532), (true, vertices_56), (true, vertices_168), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_138) then 6 else
  if p.val = (true, vertices_266) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_556) then 19 else
  if p.val = (true, vertices_76) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_556), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 7 334 14 3
cert_row_4 1 0 1 6 7 8 902 262 2
cert_row_2 2 1 2 4 8 556
cert_row_4 3 0 2 3 4 6 186 26 3
cert_rows
cert_pivot_2 5 7 1 0
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 334
cert_cover_5 1 0 0 1 2 5 14 334 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 902
cert_cover_5 3 1 0 1 6 7 262 902 2
cert_coverFacet 4 186
cert_cover_5 4 3 0 2 3 4 26 186 3
cert_coverFacet 5 394
cert_cover_2 5 2 0 6 7 138 394 3
cert_coverFacet 6 572
cert_cover_5 6 2 1 2 3 4 28 572 3
cert_coverFacet 7 620
cert_cover_5 7 2 1 2 4 5 556 620 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0668

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0669.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0669

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 391, 651, 51, 595, 121, 425, 585, 54, 662, 908, 308, 852, 872, 368, 263, 19, 35, 131, 515, 41, 73, 137, 521, 49, 81, 289, 577, 385, 22, 38, 134, 50, 530, 642, 52, 276, 532, 292, 388, 644, 772, 104, 296, 584, 392, 648, 776, 112, 304, 336, 592, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_391, vertices_651, vertices_51, vertices_595, vertices_121, vertices_425, vertices_585, vertices_54, vertices_662, vertices_908, vertices_308, vertices_852, vertices_872, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_263, vertices_19, vertices_35, vertices_131, vertices_515, vertices_41, vertices_73, vertices_137, vertices_521, vertices_49, vertices_81, vertices_289, vertices_577, vertices_385, vertices_22, vertices_38, vertices_134, vertices_50, vertices_530, vertices_642, vertices_52, vertices_276, vertices_532, vertices_292, vertices_388, vertices_644, vertices_772, vertices_104, vertices_296, vertices_584, vertices_392, vertices_648, vertices_776, vertices_112, vertices_304, vertices_336, vertices_592, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_391), (false, vertices_651), (false, vertices_51), (false, vertices_595), (false, vertices_121), (false, vertices_425), (false, vertices_585), (true, vertices_22), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_644), (true, vertices_772), (true, vertices_776), (true, vertices_304), (true, vertices_336), (true, vertices_352), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 14 else
  if p.val = (false, vertices_391) then 15 else
  if p.val = (false, vertices_651) then 17 else
  if p.val = (false, vertices_51) then 0 else
  if p.val = (false, vertices_595) then 18 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_585) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_52) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 22 3
cert_row_4 1 1 2 6 7 8 908 388 1
cert_row_4 2 1 3 5 7 8 852 276 2
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 54
cert_cover_2 0 1 0 3 4 22 54 3
cert_coverFacet 1 662
cert_cover_5 1 0 0 1 3 6 22 662 3
cert_coverFacet 2 908
cert_cover_5 2 1 1 2 6 7 388 908 1
cert_coverFacet 3 308
cert_cover_2 3 3 1 4 7 52 308 3
cert_coverFacet 4 852
cert_cover_5 4 2 1 3 5 7 276 852 2
cert_coverFacet 5 872
cert_cover_5 5 3 2 4 5 7 104 872 3
cert_coverFacet 6 368
cert_cover_2 6 4 3 5 7 112 368 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0669

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0670.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0670

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 589, 809, 457, 433, 705, 542, 182, 710, 794, 306, 802, 348, 212, 464, 73, 265, 521, 161, 289, 545, 193, 577, 385, 641, 22, 134, 518, 538, 50, 274, 162, 290, 546, 642, 770, 28, 76, 524, 84, 148, 196, 580, 280, 328, 776, 176, 304, 208, 336, 400, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_589, vertices_809, vertices_457, vertices_433, vertices_705, vertices_542, vertices_182, vertices_710, vertices_794, vertices_306, vertices_802, vertices_348, vertices_212, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_22, vertices_134, vertices_518, vertices_538, vertices_50, vertices_274, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_28, vertices_76, vertices_524, vertices_84, vertices_148, vertices_196, vertices_580, vertices_280, vertices_328, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_400, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_589), (false, vertices_809), (false, vertices_457), (false, vertices_433), (false, vertices_705), (true, vertices_22), (true, vertices_134), (true, vertices_518), (true, vertices_538), (true, vertices_50), (true, vertices_274), (true, vertices_290), (true, vertices_770), (true, vertices_28), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_280), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_538) then 17 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 705 22 134 518 50 274 290 770 28 84 148 196 280 208 336 675 538 589 809 457 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 6 182 22 3
cert_row_4 1 0 1 5 6 8 710 134 2
cert_row_2 2 0 2 3 8 538
cert_row_4 3 1 2 3 5 7 348 28 3
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 2 0 1 2 3 22 542 2
cert_coverFacet 1 182
cert_cover_5 1 0 0 1 3 4 22 182 3
cert_coverFacet 2 710
cert_cover_5 2 1 0 1 5 6 134 710 2
cert_coverFacet 3 794
cert_cover_5 3 2 0 2 3 7 538 794 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 348
cert_cover_5 6 3 1 2 3 5 28 348 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0670

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0671.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0671

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 661, 229, 805, 793, 417, 206, 654, 346, 538, 658, 482, 588, 612, 872, 37, 133, 517, 145, 273, 529, 161, 289, 385, 769, 142, 26, 74, 522, 146, 274, 530, 194, 322, 386, 642, 76, 524, 100, 548, 196, 580, 644, 280, 536, 328, 584, 776, 656, 224, 352, 608, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_661, vertices_229, vertices_805, vertices_793, vertices_417, vertices_206, vertices_654, vertices_346, vertices_538, vertices_658, vertices_482, vertices_588, vertices_612, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_385, vertices_769, vertices_142, vertices_26, vertices_74, vertices_522, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_642, vertices_76, vertices_524, vertices_100, vertices_548, vertices_196, vertices_580, vertices_644, vertices_280, vertices_536, vertices_328, vertices_584, vertices_776, vertices_656, vertices_224, vertices_352, vertices_608, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_661), (false, vertices_229), (false, vertices_805), (false, vertices_793), (false, vertices_417), (true, vertices_142), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_642), (true, vertices_76), (true, vertices_524), (true, vertices_580), (true, vertices_328), (true, vertices_584), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_229) then 20 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_793) then 23 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_142) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
cert_nodeAtPriority_51 417 26 74 522 530 194 322 642 76 524 580 328 584 352 608 403 142 661 229 805 793
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 6 142
cert_row_4 1 0 2 3 5 7 346 26 3
cert_row_4 2 0 4 5 6 7 482 194 1
cert_row_4 3 2 4 5 7 8 872 328 1
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 142 206 3
cert_coverFacet 1 654
cert_cover_5 1 0 0 1 2 8 142 654 3
cert_coverFacet 2 346
cert_cover_5 2 1 0 2 3 5 26 346 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 482
cert_cover_5 5 2 0 4 5 6 194 482 1
cert_coverFacet 6 588
cert_cover_2 6 2 1 5 8 76 588 3
cert_coverFacet 7 612
cert_cover_2 7 4 1 5 8 100 612 3
cert_coverFacet 8 872
cert_cover_5 8 3 2 4 5 7 328 872 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0671

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0672.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0672

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 787, 611, 837, 361, 433, 662, 682, 348, 156, 620, 652, 788, 408, 424, 19, 35, 515, 177, 273, 97, 289, 321, 577, 769, 146, 530, 162, 546, 642, 28, 76, 140, 524, 148, 276, 532, 324, 580, 644, 772, 152, 280, 104, 168, 296, 552, 328, 392, 648, 400, 784, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_787, vertices_611, vertices_837, vertices_361, vertices_433, vertices_662, vertices_682, vertices_348, vertices_156, vertices_620, vertices_652, vertices_788, vertices_408, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_515, vertices_177, vertices_273, vertices_97, vertices_289, vertices_321, vertices_577, vertices_769, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_28, vertices_76, vertices_140, vertices_524, vertices_148, vertices_276, vertices_532, vertices_324, vertices_580, vertices_644, vertices_772, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_552, vertices_328, vertices_392, vertices_648, vertices_400, vertices_784, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_787), (false, vertices_611), (false, vertices_837), (false, vertices_361), (false, vertices_433), (true, vertices_642), (true, vertices_28), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_644), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_552), (true, vertices_392), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 23 else
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_28) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_648) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 5 7 348 28 3
cert_row_4 1 0 1 3 6 8 662 146 1
cert_row_4 2 0 2 4 6 8 682 162 1
cert_row_4 3 1 2 4 5 8 620 76 2
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 146 662 1
cert_coverFacet 1 682
cert_cover_5 1 2 0 2 4 6 162 682 1
cert_coverFacet 2 348
cert_cover_5 2 0 1 2 3 5 28 348 3
cert_coverFacet 3 156
cert_cover_2 3 2 1 3 6 28 156 3
cert_coverFacet 4 620
cert_cover_5 4 3 1 2 4 5 76 620 2
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0672

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0673.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0673

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [227, 309, 661, 613, 713, 433, 806, 842, 466, 610, 418, 796, 216, 344, 664, 21, 37, 517, 305, 145, 97, 161, 193, 577, 641, 98, 162, 290, 546, 194, 322, 578, 386, 770, 276, 532, 292, 548, 772, 88, 152, 280, 536, 200, 328, 584, 648, 776, 208, 336, 400, 656, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_309, vertices_661, vertices_613, vertices_713, vertices_433, vertices_806, vertices_842, vertices_466, vertices_610, vertices_418, vertices_796, vertices_216, vertices_344, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_517, vertices_305, vertices_145, vertices_97, vertices_161, vertices_193, vertices_577, vertices_641, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_276, vertices_532, vertices_292, vertices_548, vertices_772, vertices_88, vertices_152, vertices_280, vertices_536, vertices_200, vertices_328, vertices_584, vertices_648, vertices_776, vertices_208, vertices_336, vertices_400, vertices_656, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_309), (false, vertices_661), (false, vertices_613), (false, vertices_713), (false, vertices_433), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_770), (true, vertices_772), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_328), (true, vertices_776), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 16 else
  if p.val = (false, vertices_309) then 23 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_290) then 0 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_4 1 0 3 5 6 7 466 194 1
cert_row_4 2 0 2 5 7 8 842 322 1
cert_row_4 3 1 2 3 7 8 796 276 1
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 842
cert_cover_5 1 2 0 2 5 7 322 842 1
cert_coverFacet 2 466
cert_cover_5 2 1 0 3 5 6 194 466 1
cert_coverFacet 3 610
cert_cover_2 3 4 0 5 8 98 610 3
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 796
cert_cover_5 5 3 1 2 3 7 276 796 1
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0673

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0674.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0674

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 213, 601, 689, 481, 833, 542, 46, 678, 298, 842, 92, 428, 460, 660, 81, 145, 529, 161, 289, 545, 193, 321, 577, 769, 14, 38, 518, 42, 266, 522, 290, 546, 770, 28, 44, 76, 396, 84, 148, 532, 164, 196, 644, 88, 536, 296, 328, 584, 656, 416, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_213, vertices_601, vertices_689, vertices_481, vertices_833, vertices_542, vertices_46, vertices_678, vertices_298, vertices_842, vertices_92, vertices_428, vertices_460, vertices_660] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_529, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_769, vertices_14, vertices_38, vertices_518, vertices_42, vertices_266, vertices_522, vertices_290, vertices_546, vertices_770, vertices_28, vertices_44, vertices_76, vertices_396, vertices_84, vertices_148, vertices_532, vertices_164, vertices_196, vertices_644, vertices_88, vertices_536, vertices_296, vertices_328, vertices_584, vertices_656, vertices_416, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_213), (false, vertices_601), (false, vertices_689), (false, vertices_481), (false, vertices_833), (true, vertices_14), (true, vertices_38), (true, vertices_518), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_396), (true, vertices_532), (true, vertices_164), (true, vertices_644), (true, vertices_296), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_396) then 19 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_164) then 11 else
  if p.val = (true, vertices_644) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_328) then 14 else
  0
cert_priority
cert_nodeAtPriority_9 0 833 1 14 38 518 42 266 522 28 44 76 532 164 644 296 328 803 213 396 601 689 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 14 3
cert_row_4 1 0 1 4 6 8 678 38 3
cert_row_2 2 1 2 6 7 396
cert_row_4 3 0 2 5 7 8 842 266 2
cert_rows
cert_pivot_2 3 4 1 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 14 542 3
cert_coverFacet 1 46
cert_cover_2 1 1 0 2 4 14 46 3
cert_coverFacet 2 678
cert_cover_5 2 1 0 1 4 6 38 678 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 842
cert_cover_5 4 3 0 2 5 7 266 842 2
cert_coverFacet 5 92
cert_cover_2 5 2 1 3 5 28 92 3
cert_coverFacet 6 428
cert_cover_5 6 2 1 2 4 6 44 428 3
cert_coverFacet 7 460
cert_cover_5 7 2 1 2 5 6 76 460 3
cert_coverFacet 8 660
cert_cover_2 8 3 1 6 8 148 660 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0674

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0675.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0675

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 397, 837, 345, 617, 649, 182, 790, 682, 626, 436, 120, 312, 424, 848, 133, 261, 517, 73, 137, 265, 521, 321, 577, 641, 22, 134, 518, 50, 530, 162, 546, 642, 180, 276, 388, 772, 56, 88, 280, 104, 168, 296, 552, 392, 648, 112, 304, 336, 592, 784, 608, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_397, vertices_837, vertices_345, vertices_617, vertices_649, vertices_182, vertices_790, vertices_682, vertices_626, vertices_436, vertices_120, vertices_312, vertices_424, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_521, vertices_321, vertices_577, vertices_641, vertices_22, vertices_134, vertices_518, vertices_50, vertices_530, vertices_162, vertices_546, vertices_642, vertices_180, vertices_276, vertices_388, vertices_772, vertices_56, vertices_88, vertices_280, vertices_104, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_112, vertices_304, vertices_336, vertices_592, vertices_784, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_397), (false, vertices_837), (false, vertices_345), (false, vertices_617), (false, vertices_649), (true, vertices_22), (true, vertices_50), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_180), (true, vertices_276), (true, vertices_56), (true, vertices_168), (true, vertices_296), (true, vertices_112), (true, vertices_304), (true, vertices_592), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_649) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_180) then 20 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_180), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 22 3
cert_row_2 1 1 3 4 6 180
cert_row_4 2 0 2 4 6 8 682 162 1
cert_row_4 3 0 3 4 5 8 626 50 3
cert_rows
cert_pivot_2 7 1 2 0
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 1 0 1 3 4 22 182 3
cert_coverFacet 1 790
cert_cover_5 1 0 0 1 3 7 22 790 3
cert_coverFacet 2 682
cert_cover_5 2 2 0 2 4 6 162 682 1
cert_coverFacet 3 626
cert_cover_5 3 3 0 3 4 5 50 626 3
cert_coverFacet 4 436
cert_cover_5 4 1 1 3 4 7 180 436 3
cert_coverFacet 5 120
cert_cover_2 5 3 2 4 5 56 120 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coverFacet 8 848
cert_cover_2 8 5 3 7 8 336 848 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0675

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0676.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0676

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 557, 141, 181, 305, 913, 865, 590, 346, 410, 962, 92, 156, 372, 612, 13, 37, 133, 137, 521, 49, 145, 273, 289, 545, 641, 769, 282, 74, 138, 522, 322, 578, 386, 642, 28, 76, 140, 524, 52, 84, 148, 100, 548, 580, 88, 152, 304, 336, 400, 352, 608, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_557, vertices_141, vertices_181, vertices_305, vertices_913, vertices_865, vertices_590, vertices_346, vertices_410, vertices_962, vertices_92, vertices_156, vertices_372, vertices_612] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_133, vertices_137, vertices_521, vertices_49, vertices_145, vertices_273, vertices_289, vertices_545, vertices_641, vertices_769, vertices_282, vertices_74, vertices_138, vertices_522, vertices_322, vertices_578, vertices_386, vertices_642, vertices_28, vertices_76, vertices_140, vertices_524, vertices_52, vertices_84, vertices_148, vertices_100, vertices_548, vertices_580, vertices_88, vertices_152, vertices_304, vertices_336, vertices_400, vertices_352, vertices_608, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_557), (false, vertices_141), (false, vertices_181), (false, vertices_305), (false, vertices_913), (false, vertices_865), (true, vertices_282), (true, vertices_74), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_28), (true, vertices_76), (true, vertices_84), (true, vertices_100), (true, vertices_580), (true, vertices_88), (true, vertices_152), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (false, vertices_913) then 22 else
  if p.val = (false, vertices_865) then 24 else
  if p.val = (true, vertices_282) then 16 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_336) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_282), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 322 2
cert_row_4 1 0 1 2 5 8 590 74 1
cert_row_2 2 0 2 3 7 282
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 6 8 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 74 590 1
cert_coverFacet 1 346
cert_cover_5 1 2 0 2 3 5 282 346 3
cert_coverFacet 2 410
cert_cover_5 2 2 0 2 3 6 282 410 3
cert_coverFacet 3 962
cert_cover_5 3 0 0 5 6 7 322 962 2
cert_coverFacet 4 92
cert_cover_2 4 2 1 3 5 28 92 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 372
cert_cover_5 6 3 1 3 4 5 52 372 3
cert_coverFacet 7 612
cert_cover_2 7 4 1 5 8 100 612 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0676

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0677.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0677

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 341, 533, 805, 185, 217, 361, 902, 426, 178, 722, 802, 460, 596, 708, 21, 261, 517, 153, 41, 73, 49, 81, 529, 289, 545, 321, 50, 146, 530, 162, 290, 546, 386, 642, 770, 84, 532, 196, 324, 580, 388, 644, 772, 168, 296, 200, 328, 392, 176, 208, 592, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_341, vertices_533, vertices_805, vertices_185, vertices_217, vertices_361, vertices_902, vertices_426, vertices_178, vertices_722, vertices_802, vertices_460, vertices_596, vertices_708] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_261, vertices_517, vertices_153, vertices_41, vertices_73, vertices_49, vertices_81, vertices_529, vertices_289, vertices_545, vertices_321, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_84, vertices_532, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_168, vertices_296, vertices_200, vertices_328, vertices_392, vertices_176, vertices_208, vertices_592, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_341), (false, vertices_533), (false, vertices_805), (false, vertices_185), (false, vertices_217), (false, vertices_361), (true, vertices_146), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_196), (true, vertices_580), (true, vertices_388), (true, vertices_644), (true, vertices_392), (true, vertices_592), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 15 else
  if p.val = (false, vertices_341) then 17 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_185) then 20 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_48 0 533 2 146 1 162 290 386 642 770 196 580 388 644 392 592 704 563 341 805 185 217 361
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 162 1
cert_row_4 1 0 3 5 6 8 722 146 2
cert_row_4 2 0 1 6 7 8 902 386 1
cert_row_4 3 1 2 5 6 7 460 196 1
cert_rows
cert_pivot_2 4 3 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 2 0 1 6 7 386 902 1
cert_coverFacet 1 426
cert_cover_5 1 0 0 2 4 6 162 426 1
cert_coverFacet 2 178
cert_cover_2 2 3 0 4 6 50 178 3
cert_coverFacet 3 722
cert_cover_5 3 1 0 3 5 6 146 722 2
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 460
cert_cover_5 5 3 1 2 5 6 196 460 1
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0677

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0678.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0678

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 109, 781, 341, 617, 721, 174, 410, 554, 778, 658, 738, 396, 484, 464, 13, 69, 261, 105, 521, 81, 273, 529, 577, 769, 42, 138, 266, 522, 146, 274, 530, 162, 546, 642, 770, 44, 140, 268, 100, 164, 324, 388, 552, 392, 776, 208, 336, 400, 656, 224, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_109, vertices_781, vertices_341, vertices_617, vertices_721, vertices_174, vertices_410, vertices_554, vertices_778, vertices_658, vertices_738, vertices_396, vertices_484, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_105, vertices_521, vertices_81, vertices_273, vertices_529, vertices_577, vertices_769, vertices_42, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_642, vertices_770, vertices_44, vertices_140, vertices_268, vertices_100, vertices_164, vertices_324, vertices_388, vertices_552, vertices_392, vertices_776, vertices_208, vertices_336, vertices_400, vertices_656, vertices_224, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_109), (false, vertices_781), (false, vertices_341), (false, vertices_617), (false, vertices_721), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_162), (true, vertices_546), (true, vertices_642), (true, vertices_140), (true, vertices_164), (true, vertices_388), (true, vertices_392), (true, vertices_400), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_109) then 21 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 42 1 138 2 266 522 146 162 546 642 140 164 388 392 400 224 448 787 781 341 109 617 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 138 2
cert_row_4 1 0 1 2 4 6 174 42 1
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 1 0 1 2 4 42 174 1
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 6 138 410 2
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 162 738 2
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 100 484 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0678

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3243 : Certifies 3243 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0649.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3244 : Certifies 3244 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0650.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3245 : Certifies 3245 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0651.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3246 : Certifies 3246 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0652.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3247 : Certifies 3247 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0653.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3248 : Certifies 3248 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0654.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3249 : Certifies 3249 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0655.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3250 : Certifies 3250 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0656.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3251 : Certifies 3251 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0657.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3252 : Certifies 3252 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0658.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3253 : Certifies 3253 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0659.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3254 : Certifies 3254 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0660.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3255 : Certifies 3255 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0661.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3256 : Certifies 3256 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0662.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3257 : Certifies 3257 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0663.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3258 : Certifies 3258 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0664.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3259 : Certifies 3259 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0665.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3260 : Certifies 3260 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0666.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3261 : Certifies 3261 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0667.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3262 : Certifies 3262 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0668.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3263 : Certifies 3263 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0669.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3264 : Certifies 3264 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0670.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3265 : Certifies 3265 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0671.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3266 : Certifies 3266 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0672.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3267 : Certifies 3267 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0673.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3268 : Certifies 3268 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0674.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3269 : Certifies 3269 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0675.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3270 : Certifies 3270 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0676.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3271 : Certifies 3271 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0677.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3272 : Certifies 3272 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0678.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B107 (j : Fin 30) :
    Certifies (3243 + j.val) := by
  fin_cases j
  · exact projection_3243
  · exact projection_3244
  · exact projection_3245
  · exact projection_3246
  · exact projection_3247
  · exact projection_3248
  · exact projection_3249
  · exact projection_3250
  · exact projection_3251
  · exact projection_3252
  · exact projection_3253
  · exact projection_3254
  · exact projection_3255
  · exact projection_3256
  · exact projection_3257
  · exact projection_3258
  · exact projection_3259
  · exact projection_3260
  · exact projection_3261
  · exact projection_3262
  · exact projection_3263
  · exact projection_3264
  · exact projection_3265
  · exact projection_3266
  · exact projection_3267
  · exact projection_3268
  · exact projection_3269
  · exact projection_3270
  · exact projection_3271
  · exact projection_3272

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
