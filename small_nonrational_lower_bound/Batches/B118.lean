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
/- Source: ProjectionCertificates/R_m15e10q1_1002.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1002

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 173, 301, 217, 369, 737, 270, 526, 678, 294, 538, 786, 866, 668, 976, 45, 25, 137, 265, 81, 273, 97, 161, 289, 193, 14, 38, 262, 518, 26, 266, 522, 274, 530, 290, 546, 770, 140, 268, 524, 164, 292, 644, 152, 536, 208, 336, 656, 784, 352, 608, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_173, vertices_301, vertices_217, vertices_369, vertices_737, vertices_270, vertices_526, vertices_678, vertices_294, vertices_538, vertices_786, vertices_866, vertices_668, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_45, vertices_25, vertices_137, vertices_265, vertices_81, vertices_273, vertices_97, vertices_161, vertices_289, vertices_193, vertices_14, vertices_38, vertices_262, vertices_518, vertices_26, vertices_266, vertices_522, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_644, vertices_152, vertices_536, vertices_208, vertices_336, vertices_656, vertices_784, vertices_352, vertices_608, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_173), (false, vertices_301), (false, vertices_217), (false, vertices_369), (false, vertices_737), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_522), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_524), (true, vertices_644), (true, vertices_536), (true, vertices_656), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 16 else
  if p.val = (false, vertices_173) then 18 else
  if p.val = (false, vertices_301) then 19 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 6 8 668 140 2
cert_row_4 1 0 1 4 6 8 678 38 3
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 3 5 6 7 8 976 208 3
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
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 866
cert_cover_5 6 2 0 4 5 7 290 866 2
cert_coverFacet 7 668
cert_cover_5 7 0 1 2 3 6 140 668 2
cert_coverFacet 8 976
cert_cover_5 8 3 3 5 6 7 208 976 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1002

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_1003.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1003

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 419, 771, 173, 105, 841, 369, 406, 534, 646, 850, 108, 716, 628, 436, 131, 259, 515, 41, 73, 137, 521, 97, 161, 289, 321, 769, 22, 134, 518, 274, 530, 386, 642, 770, 44, 76, 140, 52, 404, 532, 100, 164, 580, 644, 104, 584, 648, 112, 304, 336, 592, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_419, vertices_771, vertices_173, vertices_105, vertices_841, vertices_369, vertices_406, vertices_534, vertices_646, vertices_850, vertices_108, vertices_716, vertices_628, vertices_436] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_41, vertices_73, vertices_137, vertices_521, vertices_97, vertices_161, vertices_289, vertices_321, vertices_769, vertices_22, vertices_134, vertices_518, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_140, vertices_52, vertices_404, vertices_532, vertices_100, vertices_164, vertices_580, vertices_644, vertices_104, vertices_584, vertices_648, vertices_112, vertices_304, vertices_336, vertices_592, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_419), (false, vertices_771), (false, vertices_173), (false, vertices_105), (false, vertices_841), (false, vertices_369), (true, vertices_22), (true, vertices_134), (true, vertices_518), (true, vertices_274), (true, vertices_530), (true, vertices_76), (true, vertices_52), (true, vertices_404), (true, vertices_532), (true, vertices_100), (true, vertices_580), (true, vertices_644), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_173) then 18 else
  if p.val = (false, vertices_105) then 1 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_404) then 19 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_644) then 12 else
  if p.val = (true, vertices_592) then 13 else
  0
cert_priority
cert_nodeAtPriority_44 771 105 22 134 518 274 530 76 52 532 100 580 644 592 651 419 173 404 841 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 7 8 850 274 2
cert_row_2 1 1 3 6 7 404
cert_row_4 2 1 2 5 6 8 716 76 3
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 0 7 2 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 1 0 1 3 6 22 406 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 850
cert_cover_5 3 0 0 3 5 7 274 850 2
cert_coverFacet 4 108
cert_cover_2 4 2 1 4 5 44 108 3
cert_coverFacet 5 716
cert_cover_5 5 2 1 2 5 6 76 716 3
cert_coverFacet 6 628
cert_cover_5 6 3 1 3 4 5 52 628 3
cert_coverFacet 7 436
cert_cover_5 7 1 1 3 4 6 52 436 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1003

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_1004.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1004

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 179, 611, 771, 837, 185, 361, 790, 658, 674, 460, 724, 404, 408, 744, 19, 35, 259, 515, 25, 41, 265, 177, 97, 321, 577, 769, 146, 274, 530, 162, 546, 642, 770, 148, 276, 532, 196, 324, 580, 388, 772, 152, 280, 104, 168, 200, 328, 392, 400, 656, 608, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_179, vertices_611, vertices_771, vertices_837, vertices_185, vertices_361, vertices_790, vertices_658, vertices_674, vertices_460, vertices_724, vertices_404, vertices_408, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_515, vertices_25, vertices_41, vertices_265, vertices_177, vertices_97, vertices_321, vertices_577, vertices_769, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_642, vertices_770, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_152, vertices_280, vertices_104, vertices_168, vertices_200, vertices_328, vertices_392, vertices_400, vertices_656, vertices_608, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_179), (false, vertices_611), (false, vertices_771), (false, vertices_837), (false, vertices_185), (false, vertices_361), (true, vertices_530), (true, vertices_642), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_196), (true, vertices_388), (true, vertices_200), (true, vertices_392), (true, vertices_400), (true, vertices_656), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 21 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 15 else
  if p.val = (false, vertices_179) then 22 else
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_185) then 23 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_4 1 1 2 5 6 7 460 196 1
cert_row_4 2 1 3 5 6 8 724 148 2
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 658
cert_cover_2 1 3 0 6 8 146 658 3
cert_coverFacet 2 674
cert_cover_2 2 4 0 6 8 162 674 3
cert_coverFacet 3 460
cert_cover_5 3 1 1 2 5 6 196 460 1
cert_coverFacet 4 724
cert_cover_5 4 2 1 3 5 6 148 724 2
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 104 744 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1004

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_1005.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1005

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 285, 665, 425, 625, 305, 206, 526, 598, 650, 482, 610, 540, 460, 372, 25, 137, 265, 49, 273, 529, 161, 289, 545, 641, 14, 70, 518, 138, 522, 98, 162, 546, 194, 578, 642, 28, 204, 268, 524, 84, 276, 532, 324, 536, 392, 648, 112, 304, 592, 352, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_285, vertices_665, vertices_425, vertices_625, vertices_305, vertices_206, vertices_526, vertices_598, vertices_650, vertices_482, vertices_610, vertices_540, vertices_460, vertices_372] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_49, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_14, vertices_70, vertices_518, vertices_138, vertices_522, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_204, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_324, vertices_536, vertices_392, vertices_648, vertices_112, vertices_304, vertices_592, vertices_352, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_285), (false, vertices_665), (false, vertices_425), (false, vertices_625), (false, vertices_305), (true, vertices_14), (true, vertices_70), (true, vertices_518), (true, vertices_138), (true, vertices_522), (true, vertices_98), (true, vertices_194), (true, vertices_578), (true, vertices_204), (true, vertices_524), (true, vertices_84), (true, vertices_532), (true, vertices_324), (true, vertices_352), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_204) then 19 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_324) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 305 2 14 1 70 3 518 138 522 98 194 578 524 84 532 324 352 448 675 285 204 665 425 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 6 204
cert_row_4 1 0 1 3 5 8 598 70 2
cert_row_4 2 0 4 5 6 7 482 98 3
cert_row_4 3 1 3 4 5 7 372 84 2
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 598
cert_cover_5 2 1 0 1 3 5 70 598 2
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 482
cert_cover_5 4 2 0 4 5 6 98 482 3
cert_coverFacet 5 610
cert_cover_2 5 4 0 5 8 98 610 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 460
cert_cover_5 7 0 1 2 5 7 204 460 3
cert_coverFacet 8 372
cert_cover_5 8 3 1 3 4 5 84 372 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1005

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_1006.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1006

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 213, 409, 625, 785, 481, 110, 270, 422, 794, 618, 604, 156, 396, 228, 81, 145, 273, 529, 97, 289, 545, 193, 385, 769, 14, 38, 262, 106, 266, 522, 290, 546, 770, 28, 76, 140, 268, 84, 148, 100, 164, 196, 388, 152, 280, 536, 584, 392, 592, 784, 224, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_213, vertices_409, vertices_625, vertices_785, vertices_481, vertices_110, vertices_270, vertices_422, vertices_794, vertices_618, vertices_604, vertices_156, vertices_396, vertices_228] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_385, vertices_769, vertices_14, vertices_38, vertices_262, vertices_106, vertices_266, vertices_522, vertices_290, vertices_546, vertices_770, vertices_28, vertices_76, vertices_140, vertices_268, vertices_84, vertices_148, vertices_100, vertices_164, vertices_196, vertices_388, vertices_152, vertices_280, vertices_536, vertices_584, vertices_392, vertices_592, vertices_784, vertices_224, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_213), (false, vertices_409), (false, vertices_625), (false, vertices_785), (false, vertices_481), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_106), (true, vertices_266), (true, vertices_522), (true, vertices_28), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_100), (true, vertices_164), (true, vertices_388), (true, vertices_536), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_106) then 17 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_164) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_584) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 785 14 38 262 266 522 28 76 140 268 100 164 388 536 584 803 106 213 409 625 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 7 422 38 3
cert_row_2 1 0 2 4 5 106
cert_row_4 2 0 2 3 7 8 794 266 2
cert_row_4 3 1 2 3 5 8 604 28 3
cert_rows
cert_pivot_2 6 4 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 422
cert_cover_5 2 0 0 1 4 6 38 422 3
cert_coverFacet 3 794
cert_cover_5 3 2 0 2 3 7 266 794 2
cert_coverFacet 4 618
cert_cover_5 4 1 0 2 4 8 106 618 3
cert_coverFacet 5 604
cert_cover_5 5 3 1 2 3 5 28 604 3
cert_coverFacet 6 156
cert_cover_2 6 2 1 3 6 28 156 3
cert_coverFacet 7 396
cert_cover_2 7 2 1 6 7 140 396 3
cert_coverFacet 8 228
cert_cover_2 8 4 1 5 6 100 228 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1006

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_1007.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1007

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 157, 601, 233, 177, 817, 334, 590, 790, 482, 802, 540, 396, 436, 456, 25, 73, 137, 49, 145, 529, 97, 161, 545, 577, 78, 262, 518, 98, 290, 546, 322, 578, 770, 28, 140, 268, 524, 148, 276, 532, 388, 536, 200, 328, 584, 392, 176, 304, 784, 224, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_157, vertices_601, vertices_233, vertices_177, vertices_817, vertices_334, vertices_590, vertices_790, vertices_482, vertices_802, vertices_540, vertices_396, vertices_436, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_137, vertices_49, vertices_145, vertices_529, vertices_97, vertices_161, vertices_545, vertices_577, vertices_78, vertices_262, vertices_518, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_388, vertices_536, vertices_200, vertices_328, vertices_584, vertices_392, vertices_176, vertices_304, vertices_784, vertices_224, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_157), (false, vertices_601), (false, vertices_233), (false, vertices_177), (false, vertices_817), (true, vertices_78), (true, vertices_262), (true, vertices_518), (true, vertices_290), (true, vertices_322), (true, vertices_770), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_532), (true, vertices_388), (true, vertices_328), (true, vertices_392), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_157) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 177 262 518 290 322 770 268 524 276 532 388 328 392 416 448 611 78 157 601 233 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 1 3 7 8 790 262 2
cert_row_4 2 0 4 5 6 7 482 98 3
cert_row_4 3 1 3 4 6 7 436 148 2
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 7 78 334 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 790
cert_cover_5 2 1 0 1 3 7 262 790 2
cert_coverFacet 3 482
cert_cover_5 3 2 0 4 5 6 98 482 3
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 436
cert_cover_5 7 3 1 3 4 6 148 436 2
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1007

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_1008.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1008

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 93, 569, 201, 905, 241, 398, 230, 358, 818, 898, 796, 204, 340, 368, 25, 73, 137, 521, 49, 81, 161, 545, 193, 641, 102, 134, 262, 162, 290, 546, 386, 642, 770, 28, 76, 140, 268, 84, 276, 196, 324, 536, 200, 392, 776, 112, 304, 560, 336, 784, 224, 352, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_93, vertices_569, vertices_201, vertices_905, vertices_241, vertices_398, vertices_230, vertices_358, vertices_818, vertices_898, vertices_796, vertices_204, vertices_340, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_137, vertices_521, vertices_49, vertices_81, vertices_161, vertices_545, vertices_193, vertices_641, vertices_102, vertices_134, vertices_262, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_140, vertices_268, vertices_84, vertices_276, vertices_196, vertices_324, vertices_536, vertices_200, vertices_392, vertices_776, vertices_112, vertices_304, vertices_560, vertices_336, vertices_784, vertices_224, vertices_352, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_93), (false, vertices_569), (false, vertices_201), (false, vertices_905), (false, vertices_241), (true, vertices_102), (true, vertices_134), (true, vertices_262), (true, vertices_290), (true, vertices_386), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_276), (true, vertices_196), (true, vertices_324), (true, vertices_304), (true, vertices_336), (true, vertices_784), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_93) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (false, vertices_905) then 22 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (true, vertices_102) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 201 134 262 290 386 770 140 268 276 196 324 304 336 784 352 675 102 93 569 905 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 5 102
cert_row_4 1 0 1 2 6 7 398 134 2
cert_row_4 2 0 3 4 7 8 818 290 1
cert_row_4 3 1 2 3 7 8 796 28 3
cert_rows
cert_pivot_2 5 6 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 134 398 2
cert_coverFacet 1 230
cert_cover_5 1 0 0 1 4 6 102 230 3
cert_coverFacet 2 358
cert_cover_5 2 0 0 1 4 7 102 358 3
cert_coverFacet 3 818
cert_cover_5 3 2 0 3 4 7 290 818 1
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 796
cert_cover_5 5 3 1 2 3 7 28 796 3
cert_coverFacet 6 204
cert_cover_2 6 2 1 5 6 76 204 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1008

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_1009.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1009

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 565, 57, 409, 361, 929, 214, 598, 458, 866, 898, 60, 156, 620, 204, 25, 41, 265, 49, 145, 529, 289, 545, 385, 641, 86, 146, 530, 194, 322, 578, 386, 642, 770, 28, 44, 76, 140, 52, 148, 532, 548, 196, 580, 56, 152, 104, 200, 328, 392, 352, 608, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_565, vertices_57, vertices_409, vertices_361, vertices_929, vertices_214, vertices_598, vertices_458, vertices_866, vertices_898, vertices_60, vertices_156, vertices_620, vertices_204] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_49, vertices_145, vertices_529, vertices_289, vertices_545, vertices_385, vertices_641, vertices_86, vertices_146, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_76, vertices_140, vertices_52, vertices_148, vertices_532, vertices_548, vertices_196, vertices_580, vertices_56, vertices_152, vertices_104, vertices_200, vertices_328, vertices_392, vertices_352, vertices_608, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_565), (false, vertices_57), (false, vertices_409), (false, vertices_361), (false, vertices_929), (true, vertices_86), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_770), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_140), (true, vertices_148), (true, vertices_196), (true, vertices_580), (true, vertices_200), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_86) then 17 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_580) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 57 194 322 578 386 770 28 44 76 140 148 196 580 200 608 659 86 565 409 361 929
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 2 5 6 7 458 194 1
cert_row_4 2 0 4 5 7 8 866 322 1
cert_row_4 3 1 2 4 5 8 620 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 6 86 214 3
cert_coverFacet 1 598
cert_cover_5 1 0 0 1 3 8 86 598 3
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 6 194 458 1
cert_coverFacet 3 866
cert_cover_5 3 2 0 4 5 7 322 866 1
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 156
cert_cover_2 6 2 1 3 6 28 156 3
cert_coverFacet 7 620
cert_cover_5 7 3 1 2 4 5 44 620 3
cert_coverFacet 8 204
cert_cover_2 8 2 1 5 6 76 204 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1009

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_1010.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1010

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 677, 837, 389, 345, 665, 393, 806, 362, 242, 658, 674, 834, 428, 248, 133, 261, 517, 25, 137, 265, 81, 529, 321, 577, 385, 641, 82, 146, 530, 98, 162, 290, 546, 322, 578, 642, 770, 164, 292, 548, 388, 772, 88, 152, 104, 168, 296, 328, 392, 240, 656, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_677, vertices_837, vertices_389, vertices_345, vertices_665, vertices_393, vertices_806, vertices_362, vertices_242, vertices_658, vertices_674, vertices_834, vertices_428, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_137, vertices_265, vertices_81, vertices_529, vertices_321, vertices_577, vertices_385, vertices_641, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_290, vertices_546, vertices_322, vertices_578, vertices_642, vertices_770, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_88, vertices_152, vertices_104, vertices_168, vertices_296, vertices_328, vertices_392, vertices_240, vertices_656, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_677), (false, vertices_837), (false, vertices_389), (false, vertices_345), (false, vertices_665), (false, vertices_393), (true, vertices_146), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_642), (true, vertices_770), (true, vertices_292), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_240)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_393) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_240) then 23 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 6 240
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 2 4 5 7 362 98 1
cert_row_4 3 1 2 4 6 7 428 164 1
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 362
cert_cover_5 1 2 0 2 4 5 98 362 1
cert_coverFacet 2 242
cert_cover_5 2 0 0 3 4 5 82 242 2
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 428
cert_cover_5 6 3 1 2 4 6 164 428 1
cert_coverFacet 7 248
cert_cover_5 7 0 2 3 4 5 88 248 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1010

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_1011.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1011

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 199, 643, 85, 345, 913, 481, 174, 526, 554, 930, 92, 796, 236, 872, 7, 131, 515, 21, 69, 81, 273, 529, 193, 321, 385, 641, 14, 134, 518, 42, 522, 162, 546, 642, 28, 172, 76, 524, 84, 532, 196, 88, 280, 104, 552, 328, 776, 784, 224, 352, 416, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_199, vertices_643, vertices_85, vertices_345, vertices_913, vertices_481, vertices_174, vertices_526, vertices_554, vertices_930, vertices_92, vertices_796, vertices_236, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_131, vertices_515, vertices_21, vertices_69, vertices_81, vertices_273, vertices_529, vertices_193, vertices_321, vertices_385, vertices_641, vertices_14, vertices_134, vertices_518, vertices_42, vertices_522, vertices_162, vertices_546, vertices_642, vertices_28, vertices_172, vertices_76, vertices_524, vertices_84, vertices_532, vertices_196, vertices_88, vertices_280, vertices_104, vertices_552, vertices_328, vertices_776, vertices_784, vertices_224, vertices_352, vertices_416, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_199), (false, vertices_643), (false, vertices_85), (false, vertices_345), (false, vertices_913), (false, vertices_481), (true, vertices_14), (true, vertices_42), (true, vertices_522), (true, vertices_162), (true, vertices_546), (true, vertices_28), (true, vertices_172), (true, vertices_76), (true, vertices_524), (true, vertices_104), (true, vertices_552), (true, vertices_776), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 15 else
  if p.val = (false, vertices_199) then 16 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_85) then 1 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_913) then 22 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_172) then 18 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(true, vertices_172), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 6 7 8 930 162 3
cert_row_2 1 1 2 4 6 172
cert_row_4 2 1 2 3 7 8 796 28 3
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 1 0 1 2 4 14 174 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 930
cert_cover_5 3 0 0 4 6 7 162 930 3
cert_coverFacet 4 92
cert_cover_2 4 2 1 3 5 28 92 3
cert_coverFacet 5 796
cert_cover_5 5 2 1 2 3 7 28 796 3
cert_coverFacet 6 236
cert_cover_5 6 1 1 2 4 5 172 236 3
cert_coverFacet 7 872
cert_cover_5 7 3 2 4 5 7 104 872 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1011

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_1012.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1012

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 597, 405, 197, 617, 201, 905, 422, 682, 370, 626, 898, 236, 340, 356, 21, 69, 133, 73, 137, 521, 273, 529, 193, 577, 385, 769, 114, 274, 530, 162, 290, 546, 386, 642, 770, 84, 276, 100, 164, 292, 196, 324, 388, 104, 168, 552, 200, 648, 336, 592, 352, 608, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_597, vertices_405, vertices_197, vertices_617, vertices_201, vertices_905, vertices_422, vertices_682, vertices_370, vertices_626, vertices_898, vertices_236, vertices_340, vertices_356] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_133, vertices_73, vertices_137, vertices_521, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_769, vertices_114, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_84, vertices_276, vertices_100, vertices_164, vertices_292, vertices_196, vertices_324, vertices_388, vertices_104, vertices_168, vertices_552, vertices_200, vertices_648, vertices_336, vertices_592, vertices_352, vertices_608, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_597), (false, vertices_405), (false, vertices_197), (false, vertices_617), (false, vertices_201), (false, vertices_905), (true, vertices_114), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_100), (true, vertices_164), (true, vertices_292), (true, vertices_324), (true, vertices_168), (true, vertices_336), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (false, vertices_905) then 22 else
  if p.val = (true, vertices_114) then 16 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
cert_nodeAtPriority_25 0 197 1 201 162 290 546 386 642 100 164 292 324 168 336 352 787 114 597 405 617 905
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 5 114
cert_row_4 1 0 1 4 6 7 422 162 1
cert_row_4 2 0 2 4 6 8 682 162 1
cert_row_4 3 1 2 4 5 6 236 100 1
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 1 0 1 4 6 162 422 1
cert_coverFacet 1 682
cert_cover_5 1 2 0 2 4 6 162 682 1
cert_coverFacet 2 370
cert_cover_5 2 0 0 3 4 7 114 370 3
cert_coverFacet 3 626
cert_cover_5 3 0 0 3 4 8 114 626 3
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 236
cert_cover_5 5 3 1 2 4 5 100 236 1
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 356
cert_cover_2 7 4 1 5 7 100 356 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1012

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_1013.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1013

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 555, 771, 45, 181, 453, 929, 346, 602, 962, 60, 284, 724, 340, 696, 11, 259, 515, 13, 37, 133, 261, 41, 161, 545, 385, 769, 90, 266, 522, 322, 578, 770, 28, 44, 268, 52, 84, 148, 276, 196, 324, 56, 280, 536, 552, 176, 336, 592, 656, 672, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_555, vertices_771, vertices_45, vertices_181, vertices_453, vertices_929, vertices_346, vertices_602, vertices_962, vertices_60, vertices_284, vertices_724, vertices_340, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_259, vertices_515, vertices_13, vertices_37, vertices_133, vertices_261, vertices_41, vertices_161, vertices_545, vertices_385, vertices_769, vertices_90, vertices_266, vertices_522, vertices_322, vertices_578, vertices_770, vertices_28, vertices_44, vertices_268, vertices_52, vertices_84, vertices_148, vertices_276, vertices_196, vertices_324, vertices_56, vertices_280, vertices_536, vertices_552, vertices_176, vertices_336, vertices_592, vertices_656, vertices_672, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_555), (false, vertices_771), (false, vertices_45), (false, vertices_181), (false, vertices_453), (false, vertices_929), (true, vertices_90), (true, vertices_322), (true, vertices_578), (true, vertices_28), (true, vertices_84), (true, vertices_276), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_336), (true, vertices_592), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 14 21 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 15 else
  if p.val = (false, vertices_555) then 19 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_45) then 1 else
  if p.val = (false, vertices_181) then 16 else
  if p.val = (false, vertices_453) then 17 else
  if p.val = (false, vertices_929) then 24 else
  if p.val = (true, vertices_90) then 20 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_4 0 0 5 6 7 8 962 322 2
cert_row_2 1 0 2 3 5 90
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 346
cert_cover_5 0 1 0 2 3 7 90 346 3
cert_coverFacet 1 602
cert_cover_5 1 1 0 2 3 8 90 602 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 322 962 2
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 724
cert_cover_5 5 2 1 3 5 6 84 724 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 696
cert_cover_5 7 3 2 3 4 6 56 696 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1013

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_1014.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1014

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 659, 227, 557, 565, 105, 433, 902, 450, 834, 316, 844, 404, 660, 488, 67, 131, 515, 549, 41, 73, 521, 49, 145, 529, 97, 161, 194, 322, 578, 386, 642, 770, 44, 268, 524, 52, 148, 276, 532, 388, 644, 772, 104, 296, 328, 584, 304, 400, 656, 224, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_659, vertices_227, vertices_557, vertices_565, vertices_105, vertices_433, vertices_902, vertices_450, vertices_834, vertices_316, vertices_844, vertices_404, vertices_660, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_515, vertices_549, vertices_41, vertices_73, vertices_521, vertices_49, vertices_145, vertices_529, vertices_97, vertices_161, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_532, vertices_388, vertices_644, vertices_772, vertices_104, vertices_296, vertices_328, vertices_584, vertices_304, vertices_400, vertices_656, vertices_224, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_659), (false, vertices_227), (false, vertices_557), (false, vertices_565), (false, vertices_105), (false, vertices_433), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_296), (true, vertices_328), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_227) then 17 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_565) then 20 else
  if p.val = (false, vertices_105) then 0 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_448) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_105), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_4 1 1 2 3 4 7 316 44 2
cert_row_4 2 1 2 5 7 8 844 268 2
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 450
cert_cover_2 1 5 0 6 7 194 450 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 316
cert_cover_5 3 1 1 2 3 4 44 316 2
cert_coverFacet 4 844
cert_cover_5 4 2 1 2 5 7 268 844 2
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1014

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_1015.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1015

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 421, 601, 233, 393, 865, 118, 406, 806, 282, 538, 626, 220, 228, 408, 73, 137, 265, 521, 97, 161, 289, 577, 385, 769, 22, 38, 262, 26, 266, 522, 114, 274, 530, 546, 770, 84, 148, 100, 164, 292, 196, 388, 88, 152, 280, 536, 200, 392, 592, 400, 224, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_421, vertices_601, vertices_233, vertices_393, vertices_865, vertices_118, vertices_406, vertices_806, vertices_282, vertices_538, vertices_626, vertices_220, vertices_228, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_769, vertices_22, vertices_38, vertices_262, vertices_26, vertices_266, vertices_522, vertices_114, vertices_274, vertices_530, vertices_546, vertices_770, vertices_84, vertices_148, vertices_100, vertices_164, vertices_292, vertices_196, vertices_388, vertices_88, vertices_152, vertices_280, vertices_536, vertices_200, vertices_392, vertices_592, vertices_400, vertices_224, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_421), (false, vertices_601), (false, vertices_233), (false, vertices_393), (false, vertices_865), (true, vertices_22), (true, vertices_38), (true, vertices_262), (true, vertices_26), (true, vertices_114), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_84), (true, vertices_148), (true, vertices_100), (true, vertices_196), (true, vertices_152), (true, vertices_280), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_114) then 17 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 393 22 38 262 26 274 530 546 84 148 100 196 152 280 400 779 114 421 601 233 865
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 38 3
cert_row_2 1 0 3 4 5 114
cert_row_4 2 0 1 3 6 7 406 22 3
cert_row_4 3 1 2 3 5 6 220 84 1
cert_rows
cert_pivot_2 8 4 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 1 0 1 3 4 22 118 3
cert_coverFacet 1 406
cert_cover_5 1 2 0 1 3 6 22 406 3
cert_coverFacet 2 806
cert_cover_5 2 0 0 1 4 7 38 806 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 626
cert_cover_5 5 1 0 3 4 8 114 626 3
cert_coverFacet 6 220
cert_cover_5 6 3 1 2 3 5 84 220 1
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1015

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_1016.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1016

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 341, 313, 561, 721, 481, 206, 526, 598, 426, 554, 706, 572, 284, 460, 49, 81, 273, 529, 161, 289, 545, 193, 321, 641, 14, 70, 518, 42, 138, 522, 162, 546, 194, 578, 642, 28, 204, 268, 524, 84, 276, 532, 324, 56, 280, 296, 552, 392, 560, 592, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_341, vertices_313, vertices_561, vertices_721, vertices_481, vertices_206, vertices_526, vertices_598, vertices_426, vertices_554, vertices_706, vertices_572, vertices_284, vertices_460] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_14, vertices_70, vertices_518, vertices_42, vertices_138, vertices_522, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_204, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_324, vertices_56, vertices_280, vertices_296, vertices_552, vertices_392, vertices_560, vertices_592, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_341), (false, vertices_313), (false, vertices_561), (false, vertices_721), (false, vertices_481), (true, vertices_14), (true, vertices_70), (true, vertices_518), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_194), (true, vertices_578), (true, vertices_28), (true, vertices_204), (true, vertices_268), (true, vertices_524), (true, vertices_532), (true, vertices_552), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_204) then 19 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
cert_nodeAtPriority_9 0 561 1 14 70 518 42 138 522 194 578 28 268 524 532 552 392 675 341 204 313 721 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 42 3
cert_row_2 1 1 2 5 6 204
cert_row_4 2 0 1 3 5 8 598 70 2
cert_row_4 3 1 2 3 4 8 572 28 3
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 598
cert_cover_5 2 2 0 1 3 5 70 598 2
cert_coverFacet 3 426
cert_cover_5 3 0 0 2 4 6 42 426 3
cert_coverFacet 4 554
cert_cover_2 4 2 0 4 8 42 554 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 572
cert_cover_5 6 3 1 2 3 4 28 572 3
cert_coverFacet 7 284
cert_cover_2 7 2 1 3 7 28 284 3
cert_coverFacet 8 460
cert_cover_5 8 1 1 2 5 7 204 460 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1016

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_1017.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1017

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 205, 405, 805, 581, 105, 425, 790, 666, 282, 362, 714, 802, 724, 408, 69, 133, 261, 517, 41, 73, 137, 97, 289, 545, 577, 385, 26, 74, 650, 266, 274, 530, 98, 290, 546, 578, 770, 148, 276, 532, 196, 580, 772, 152, 280, 104, 296, 200, 392, 400, 656, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_205, vertices_405, vertices_805, vertices_581, vertices_105, vertices_425, vertices_790, vertices_666, vertices_282, vertices_362, vertices_714, vertices_802, vertices_724, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_517, vertices_41, vertices_73, vertices_137, vertices_97, vertices_289, vertices_545, vertices_577, vertices_385, vertices_26, vertices_74, vertices_650, vertices_266, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_148, vertices_276, vertices_532, vertices_196, vertices_580, vertices_772, vertices_152, vertices_280, vertices_104, vertices_296, vertices_200, vertices_392, vertices_400, vertices_656, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_205), (false, vertices_405), (false, vertices_805), (false, vertices_581), (false, vertices_105), (false, vertices_425), (true, vertices_26), (true, vertices_74), (true, vertices_650), (true, vertices_266), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_770), (true, vertices_532), (true, vertices_152), (true, vertices_280), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 15 else
  if p.val = (false, vertices_205) then 18 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_105) then 1 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_650) then 16 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 581 1 105 26 74 266 274 530 290 770 532 152 280 656 704 611 650 205 405 805 425
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 7 362 74 2
cert_row_2 1 0 2 6 8 650
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 1 3 5 6 8 724 148 2
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 666
cert_cover_5 1 1 0 2 3 6 26 666 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 362
cert_cover_5 3 0 0 2 4 5 74 362 2
cert_coverFacet 4 714
cert_cover_5 4 1 0 2 5 6 74 714 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 148 724 2
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1017

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_1019.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1019

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 61, 525, 661, 425, 177, 961, 46, 526, 118, 838, 234, 458, 596, 752, 13, 21, 517, 41, 265, 521, 49, 145, 161, 385, 641, 769, 14, 38, 70, 518, 42, 202, 266, 522, 98, 322, 770, 44, 524, 52, 84, 532, 580, 168, 392, 112, 176, 592, 656, 224, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_61, vertices_525, vertices_661, vertices_425, vertices_177, vertices_961, vertices_46, vertices_526, vertices_118, vertices_838, vertices_234, vertices_458, vertices_596, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_517, vertices_41, vertices_265, vertices_521, vertices_49, vertices_145, vertices_161, vertices_385, vertices_641, vertices_769, vertices_14, vertices_38, vertices_70, vertices_518, vertices_42, vertices_202, vertices_266, vertices_522, vertices_98, vertices_322, vertices_770, vertices_44, vertices_524, vertices_52, vertices_84, vertices_532, vertices_580, vertices_168, vertices_392, vertices_112, vertices_176, vertices_592, vertices_656, vertices_224, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_61), (false, vertices_525), (false, vertices_661), (false, vertices_425), (false, vertices_177), (false, vertices_961), (true, vertices_14), (true, vertices_38), (true, vertices_70), (true, vertices_518), (true, vertices_42), (true, vertices_202), (true, vertices_98), (true, vertices_322), (true, vertices_84), (true, vertices_580), (true, vertices_112), (true, vertices_592), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_61) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_177) then 1 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_38) then 3 else
  if p.val = (true, vertices_70) then 4 else
  if p.val = (true, vertices_518) then 5 else
  if p.val = (true, vertices_42) then 6 else
  if p.val = (true, vertices_202) then 16 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_224) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_2 0 0 2 5 6 202
cert_row_4 1 0 1 5 7 8 838 70 3
cert_row_4 2 0 1 3 4 5 118 38 2
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 2 7 0 3
cert_heightProof 4
cert_coverFacet 0 46
cert_cover_2 0 1 0 2 4 14 46 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 118
cert_cover_5 2 2 0 1 3 4 38 118 2
cert_coverFacet 3 838
cert_cover_5 3 1 0 1 5 7 70 838 3
cert_coverFacet 4 234
cert_cover_5 4 0 0 2 4 5 42 234 3
cert_coverFacet 5 458
cert_cover_5 5 0 0 2 5 7 202 458 3
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1019

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_1020.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1020

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [39, 583, 563, 333, 309, 721, 337, 398, 526, 422, 682, 588, 968, 496, 688, 7, 35, 515, 37, 69, 261, 49, 81, 273, 529, 321, 577, 14, 38, 390, 518, 138, 522, 162, 546, 76, 268, 524, 292, 580, 328, 584, 392, 648, 176, 304, 560, 208, 336, 656, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_39, vertices_583, vertices_563, vertices_333, vertices_309, vertices_721, vertices_337, vertices_398, vertices_526, vertices_422, vertices_682, vertices_588, vertices_968, vertices_496, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_35, vertices_515, vertices_37, vertices_69, vertices_261, vertices_49, vertices_81, vertices_273, vertices_529, vertices_321, vertices_577, vertices_14, vertices_38, vertices_390, vertices_518, vertices_138, vertices_522, vertices_162, vertices_546, vertices_76, vertices_268, vertices_524, vertices_292, vertices_580, vertices_328, vertices_584, vertices_392, vertices_648, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_656, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_39), (false, vertices_583), (false, vertices_563), (false, vertices_333), (false, vertices_309), (false, vertices_721), (false, vertices_337), (true, vertices_14), (true, vertices_390), (true, vertices_138), (true, vertices_522), (true, vertices_162), (true, vertices_524), (true, vertices_584), (true, vertices_392), (true, vertices_648), (true, vertices_176), (true, vertices_416), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_39) then 0 else
  if p.val = (false, vertices_583) then 15 else
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_309) then 20 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_337) then 1 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_390) then 17 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_39), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_4 1 0 2 4 6 8 682 138 2
cert_row_4 2 2 5 6 7 8 968 328 2
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 422
cert_cover_5 2 0 0 1 4 6 38 422 3
cert_coverFacet 3 682
cert_cover_5 3 1 0 2 4 6 138 682 2
cert_coverFacet 4 588
cert_cover_2 4 2 1 5 8 76 588 3
cert_coverFacet 5 968
cert_cover_5 5 2 2 5 6 7 328 968 2
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 176 496 2
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1020

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_1021.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1021

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 397, 525, 597, 149, 241, 961, 46, 526, 566, 234, 458, 866, 188, 624, 13, 21, 133, 517, 265, 521, 81, 145, 193, 577, 385, 769, 14, 38, 518, 42, 202, 266, 522, 98, 546, 322, 770, 44, 140, 524, 52, 148, 532, 168, 392, 112, 176, 560, 592, 224, 608, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_397, vertices_525, vertices_597, vertices_149, vertices_241, vertices_961, vertices_46, vertices_526, vertices_566, vertices_234, vertices_458, vertices_866, vertices_188, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_133, vertices_517, vertices_265, vertices_521, vertices_81, vertices_145, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_38, vertices_518, vertices_42, vertices_202, vertices_266, vertices_522, vertices_98, vertices_546, vertices_322, vertices_770, vertices_44, vertices_140, vertices_524, vertices_52, vertices_148, vertices_532, vertices_168, vertices_392, vertices_112, vertices_176, vertices_560, vertices_592, vertices_224, vertices_608, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_397), (false, vertices_525), (false, vertices_597), (false, vertices_149), (false, vertices_241), (false, vertices_961), (true, vertices_14), (true, vertices_38), (true, vertices_518), (true, vertices_42), (true, vertices_202), (true, vertices_98), (true, vertices_546), (true, vertices_322), (true, vertices_44), (true, vertices_52), (true, vertices_168), (true, vertices_560), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_241) then 22 else
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
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
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
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
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
cert_coverFacet 7 624
cert_cover_2 7 4 3 5 8 112 624 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1021

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_1022.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1022

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [39, 583, 651, 179, 117, 849, 657, 398, 526, 422, 364, 588, 968, 368, 944, 7, 35, 131, 515, 37, 69, 49, 81, 145, 529, 577, 641, 14, 38, 390, 518, 138, 522, 162, 76, 268, 524, 100, 292, 580, 328, 584, 392, 648, 112, 176, 304, 336, 656, 784, 352, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_39, vertices_583, vertices_651, vertices_179, vertices_117, vertices_849, vertices_657, vertices_398, vertices_526, vertices_422, vertices_364, vertices_588, vertices_968, vertices_368, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_35, vertices_131, vertices_515, vertices_37, vertices_69, vertices_49, vertices_81, vertices_145, vertices_529, vertices_577, vertices_641, vertices_14, vertices_38, vertices_390, vertices_518, vertices_138, vertices_522, vertices_162, vertices_76, vertices_268, vertices_524, vertices_100, vertices_292, vertices_580, vertices_328, vertices_584, vertices_392, vertices_648, vertices_112, vertices_176, vertices_304, vertices_336, vertices_656, vertices_784, vertices_352, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_39), (false, vertices_583), (false, vertices_651), (false, vertices_179), (false, vertices_117), (false, vertices_849), (false, vertices_657), (true, vertices_14), (true, vertices_390), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_292), (true, vertices_328), (true, vertices_584), (true, vertices_392), (true, vertices_304), (true, vertices_352), (true, vertices_416), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 14 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_39) then 0 else
  if p.val = (false, vertices_583) then 15 else
  if p.val = (false, vertices_651) then 19 else
  if p.val = (false, vertices_179) then 20 else
  if p.val = (false, vertices_117) then 16 else
  if p.val = (false, vertices_849) then 23 else
  if p.val = (false, vertices_657) then 1 else
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
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_39), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
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
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
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
cert_row_4 3 3 4 6 7 8 944 176 3
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
cert_coverFacet 6 368
cert_cover_2 6 4 3 5 7 112 368 3
cert_coverFacet 7 944
cert_cover_5 7 3 3 4 6 7 176 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1022

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_1023.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1023

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 157, 397, 805, 689, 961, 30, 526, 550, 122, 586, 738, 844, 472, 240, 141, 21, 37, 261, 49, 145, 545, 385, 641, 769, 14, 22, 38, 518, 26, 74, 522, 50, 98, 546, 578, 28, 268, 524, 548, 772, 88, 152, 328, 584, 392, 112, 176, 208, 224, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_157, vertices_397, vertices_805, vertices_689, vertices_961, vertices_30, vertices_526, vertices_550, vertices_122, vertices_586, vertices_738, vertices_844, vertices_472, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_141, vertices_21, vertices_37, vertices_261, vertices_49, vertices_145, vertices_545, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_38, vertices_518, vertices_26, vertices_74, vertices_522, vertices_50, vertices_98, vertices_546, vertices_578, vertices_28, vertices_268, vertices_524, vertices_548, vertices_772, vertices_88, vertices_152, vertices_328, vertices_584, vertices_392, vertices_112, vertices_176, vertices_208, vertices_224, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_157), (false, vertices_397), (false, vertices_805), (false, vertices_689), (false, vertices_961), (true, vertices_14), (true, vertices_518), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_98), (true, vertices_546), (true, vertices_578), (true, vertices_524), (true, vertices_88), (true, vertices_328), (true, vertices_584), (true, vertices_112), (true, vertices_208), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 22 24 25 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 16 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (false, vertices_961) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 5 7 8 844 268 2
cert_row_4 1 0 4 5 6 8 738 98 3
cert_row_4 2 0 2 3 4 5 122 26 3
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 122
cert_cover_5 3 2 0 2 3 4 26 122 3
cert_coverFacet 4 586
cert_cover_2 4 2 0 5 8 74 586 3
cert_coverFacet 5 738
cert_cover_5 5 1 0 4 5 6 98 738 3
cert_coverFacet 6 844
cert_cover_5 6 0 1 2 5 7 268 844 2
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 88 472 3
cert_coverFacet 8 240
cert_cover_2 8 4 3 5 6 112 240 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1023

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_1024.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1024

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 403, 357, 709, 313, 241, 662, 774, 570, 282, 842, 836, 744, 360, 688, 387, 69, 133, 261, 49, 145, 273, 97, 289, 193, 134, 262, 518, 26, 266, 522, 146, 274, 530, 770, 324, 580, 644, 772, 56, 280, 104, 296, 552, 328, 584, 176, 560, 656, 224, 352, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_403, vertices_357, vertices_709, vertices_313, vertices_241, vertices_662, vertices_774, vertices_570, vertices_282, vertices_842, vertices_836, vertices_744, vertices_360, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_387, vertices_69, vertices_133, vertices_261, vertices_49, vertices_145, vertices_273, vertices_97, vertices_289, vertices_193, vertices_134, vertices_262, vertices_518, vertices_26, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_770, vertices_324, vertices_580, vertices_644, vertices_772, vertices_56, vertices_280, vertices_104, vertices_296, vertices_552, vertices_328, vertices_584, vertices_176, vertices_560, vertices_656, vertices_224, vertices_352, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_403), (false, vertices_357), (false, vertices_709), (false, vertices_313), (false, vertices_241), (true, vertices_518), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_530), (true, vertices_770), (true, vertices_772), (true, vertices_104), (true, vertices_552), (true, vertices_328), (true, vertices_584), (true, vertices_560), (true, vertices_656), (true, vertices_672), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 16 else
  if p.val = (false, vertices_403) then 17 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
cert_nodeAtPriority_62 518 26 266 522 530 770 772 104 552 328 584 560 656 672 832 391 403 357 709 313 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 134 2
cert_row_4 1 0 2 3 4 8 570 26 3
cert_row_4 2 0 2 5 7 8 842 266 2
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 134 662 2
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 570
cert_cover_5 2 1 0 2 3 4 26 570 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 842
cert_cover_5 4 2 0 2 5 7 266 842 2
cert_coverFacet 5 836
cert_cover_2 5 5 1 7 8 324 836 3
cert_coverFacet 6 744
cert_cover_5 6 3 2 4 5 6 104 744 3
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1024

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_1025.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1025

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [31, 301, 597, 357, 793, 961, 46, 534, 230, 582, 186, 914, 706, 408, 488, 13, 21, 293, 69, 25, 265, 529, 321, 577, 769, 14, 22, 38, 70, 518, 26, 42, 146, 530, 162, 194, 578, 642, 44, 532, 100, 580, 152, 280, 168, 296, 392, 400, 784, 224, 352, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_31, vertices_301, vertices_597, vertices_357, vertices_793, vertices_961, vertices_46, vertices_534, vertices_230, vertices_582, vertices_186, vertices_914, vertices_706, vertices_408, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_293, vertices_69, vertices_25, vertices_265, vertices_529, vertices_321, vertices_577, vertices_769, vertices_14, vertices_22, vertices_38, vertices_70, vertices_518, vertices_26, vertices_42, vertices_146, vertices_530, vertices_162, vertices_194, vertices_578, vertices_642, vertices_44, vertices_532, vertices_100, vertices_580, vertices_152, vertices_280, vertices_168, vertices_296, vertices_392, vertices_400, vertices_784, vertices_224, vertices_352, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_31), (false, vertices_301), (false, vertices_597), (false, vertices_357), (false, vertices_793), (false, vertices_961), (true, vertices_38), (true, vertices_70), (true, vertices_518), (true, vertices_42), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_152), (true, vertices_168), (true, vertices_392), (true, vertices_400), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 24 25 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_31) then 16 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_793) then 22 else
  if p.val = (false, vertices_961) then 26 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_642) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_31), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 6 230 38 3
cert_row_4 1 0 3 6 7 8 914 146 3
cert_row_4 2 0 2 3 4 6 186 26 3
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 46
cert_cover_2 0 1 0 2 4 14 46 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 230
cert_cover_5 2 0 0 1 4 5 38 230 3
cert_coverFacet 3 582
cert_cover_2 3 1 0 5 8 70 582 3
cert_coverFacet 4 186
cert_cover_5 4 2 0 2 3 4 26 186 3
cert_coverFacet 5 914
cert_cover_5 5 1 0 3 6 7 146 914 3
cert_coverFacet 6 706
cert_cover_2 6 5 0 6 8 194 706 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 168 488 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1025

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_1026.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1026

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 779, 51, 611, 457, 585, 369, 182, 678, 774, 412, 716, 780, 752, 464, 19, 35, 259, 515, 73, 265, 521, 49, 273, 97, 321, 577, 22, 166, 262, 518, 50, 546, 770, 140, 268, 524, 148, 276, 644, 772, 200, 584, 392, 776, 112, 176, 208, 336, 400, 608, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_779, vertices_51, vertices_611, vertices_457, vertices_585, vertices_369, vertices_182, vertices_678, vertices_774, vertices_412, vertices_716, vertices_780, vertices_752, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_515, vertices_73, vertices_265, vertices_521, vertices_49, vertices_273, vertices_97, vertices_321, vertices_577, vertices_22, vertices_166, vertices_262, vertices_518, vertices_50, vertices_546, vertices_770, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_644, vertices_772, vertices_200, vertices_584, vertices_392, vertices_776, vertices_112, vertices_176, vertices_208, vertices_336, vertices_400, vertices_608, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_779), (false, vertices_51), (false, vertices_611), (false, vertices_457), (false, vertices_585), (false, vertices_369), (true, vertices_166), (true, vertices_518), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_644), (true, vertices_772), (true, vertices_176), (true, vertices_208), (true, vertices_400), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 15 else
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_51) then 0 else
  if p.val = (false, vertices_611) then 19 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_585) then 1 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (true, vertices_166) then 16 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 1 51 0 585 518 140 268 524 148 644 772 176 208 400 672 704 279 166 779 611 457 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 6 166
cert_row_4 1 1 2 3 6 7 412 140 2
cert_row_4 2 1 2 5 6 8 716 140 2
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 7 1 3
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 4 22 182 3
cert_coverFacet 1 678
cert_cover_5 1 0 0 1 4 8 166 678 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 412
cert_cover_5 3 1 1 2 3 6 140 412 2
cert_coverFacet 4 716
cert_cover_5 4 2 1 2 5 6 140 716 2
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 752
cert_cover_5 6 3 3 4 5 6 112 752 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1026

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_1027.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1027

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 205, 677, 837, 217, 625, 902, 314, 154, 394, 866, 674, 348, 396, 368, 69, 133, 517, 201, 49, 81, 145, 161, 545, 577, 26, 138, 266, 50, 146, 162, 290, 546, 386, 642, 770, 76, 140, 268, 324, 388, 644, 772, 88, 152, 280, 392, 112, 304, 336, 352, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_205, vertices_677, vertices_837, vertices_217, vertices_625, vertices_902, vertices_314, vertices_154, vertices_394, vertices_866, vertices_674, vertices_348, vertices_396, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_201, vertices_49, vertices_81, vertices_145, vertices_161, vertices_545, vertices_577, vertices_26, vertices_138, vertices_266, vertices_50, vertices_146, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_268, vertices_324, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_392, vertices_112, vertices_304, vertices_336, vertices_352, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_205), (false, vertices_677), (false, vertices_837), (false, vertices_217), (false, vertices_625), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_268), (true, vertices_388), (true, vertices_280), (true, vertices_392), (true, vertices_304), (true, vertices_336), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 16 else
  if p.val = (false, vertices_205) then 21 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_217) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 26 1 138 2 266 290 546 386 642 770 268 388 280 392 304 336 352 179 677 837 205 217 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_4 1 0 4 5 7 8 866 290 2
cert_row_4 2 0 2 3 4 7 314 26 3
cert_row_4 3 1 2 3 5 7 348 76 2
cert_rows
cert_pivot_2 6 8 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 314
cert_cover_5 1 2 0 2 3 4 26 314 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 866
cert_cover_5 4 1 0 4 5 7 290 866 2
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 348
cert_cover_5 6 3 1 2 3 5 76 348 2
cert_coverFacet 7 396
cert_cover_2 7 2 1 6 7 140 396 3
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1027

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_1028.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1028

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 451, 285, 121, 433, 737, 542, 270, 774, 714, 930, 628, 308, 804, 600, 323, 25, 73, 265, 49, 273, 97, 161, 193, 385, 14, 262, 518, 74, 266, 522, 194, 386, 642, 770, 28, 268, 52, 276, 532, 292, 548, 772, 88, 536, 584, 112, 304, 592, 608, 416, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_451, vertices_285, vertices_121, vertices_433, vertices_737, vertices_542, vertices_270, vertices_774, vertices_714, vertices_930, vertices_628, vertices_308, vertices_804, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_323, vertices_25, vertices_73, vertices_265, vertices_49, vertices_273, vertices_97, vertices_161, vertices_193, vertices_385, vertices_14, vertices_262, vertices_518, vertices_74, vertices_266, vertices_522, vertices_194, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_52, vertices_276, vertices_532, vertices_292, vertices_548, vertices_772, vertices_88, vertices_536, vertices_584, vertices_112, vertices_304, vertices_592, vertices_608, vertices_416, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_451), (false, vertices_285), (false, vertices_121), (false, vertices_433), (false, vertices_737), (true, vertices_14), (true, vertices_262), (true, vertices_518), (true, vertices_522), (true, vertices_642), (true, vertices_770), (true, vertices_52), (true, vertices_532), (true, vertices_292), (true, vertices_548), (true, vertices_772), (true, vertices_536), (true, vertices_584), (true, vertices_592), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_451) then 17 else
  if p.val = (false, vertices_285) then 19 else
  if p.val = (false, vertices_121) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 6 7 8 930 386 1
cert_row_4 1 0 2 5 6 8 714 74 3
cert_row_4 2 0 1 2 3 8 542 14 3
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 2 0 1 2 3 14 542 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 714
cert_cover_5 3 1 0 2 5 6 74 714 3
cert_coverFacet 4 930
cert_cover_5 4 0 0 4 6 7 386 930 1
cert_coverFacet 5 628
cert_cover_5 5 3 1 3 4 5 52 628 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1028

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_1029.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1029

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 295, 589, 117, 905, 865, 526, 54, 662, 426, 650, 242, 596, 976, 480, 263, 13, 37, 69, 265, 521, 97, 289, 577, 769, 14, 22, 38, 518, 138, 266, 522, 50, 146, 162, 290, 642, 524, 52, 84, 532, 580, 392, 648, 112, 208, 592, 656, 224, 352, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_295, vertices_589, vertices_117, vertices_905, vertices_865, vertices_526, vertices_54, vertices_662, vertices_426, vertices_650, vertices_242, vertices_596, vertices_976, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_263, vertices_13, vertices_37, vertices_69, vertices_265, vertices_521, vertices_97, vertices_289, vertices_577, vertices_769, vertices_14, vertices_22, vertices_38, vertices_518, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_162, vertices_290, vertices_642, vertices_524, vertices_52, vertices_84, vertices_532, vertices_580, vertices_392, vertices_648, vertices_112, vertices_208, vertices_592, vertices_656, vertices_224, vertices_352, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_295), (false, vertices_589), (false, vertices_117), (false, vertices_905), (false, vertices_865), (true, vertices_22), (true, vertices_518), (true, vertices_138), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_162), (true, vertices_642), (true, vertices_532), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_224), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 16 else
  if p.val = (false, vertices_295) then 17 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_117) then 20 else
  if p.val = (false, vertices_905) then 22 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
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
cert_row_4 0 0 1 3 6 8 662 22 3
cert_row_4 1 0 2 4 6 7 426 138 2
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 54
cert_cover_2 1 1 0 3 4 22 54 3
cert_coverFacet 2 662
cert_cover_5 2 0 0 1 3 6 22 662 3
cert_coverFacet 3 426
cert_cover_5 3 1 0 2 4 6 138 426 2
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 242
cert_cover_5 5 2 0 3 4 5 50 242 3
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 976
cert_cover_5 7 3 3 5 6 7 208 976 3
cert_coverFacet 8 480
cert_cover_2 8 5 4 6 7 224 480 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1029

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_1030.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1030

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 659, 557, 233, 625, 465, 302, 526, 598, 278, 410, 340, 484, 612, 424, 643, 41, 137, 521, 81, 145, 529, 97, 545, 193, 14, 22, 262, 518, 138, 266, 522, 146, 274, 530, 44, 524, 84, 276, 100, 292, 548, 324, 580, 168, 296, 392, 336, 592, 400, 224, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_659, vertices_557, vertices_233, vertices_625, vertices_465, vertices_302, vertices_526, vertices_598, vertices_278, vertices_410, vertices_340, vertices_484, vertices_612, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_643, vertices_41, vertices_137, vertices_521, vertices_81, vertices_145, vertices_529, vertices_97, vertices_545, vertices_193, vertices_14, vertices_22, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_44, vertices_524, vertices_84, vertices_276, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_168, vertices_296, vertices_392, vertices_336, vertices_592, vertices_400, vertices_224, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_659), (false, vertices_557), (false, vertices_233), (false, vertices_625), (false, vertices_465), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_274), (true, vertices_84), (true, vertices_276), (true, vertices_100), (true, vertices_292), (true, vertices_324), (true, vertices_580), (true, vertices_296), (true, vertices_392), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 22 3
cert_row_4 1 0 2 3 6 7 410 138 2
cert_row_4 2 0 1 2 4 7 302 14 3
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 8 3 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 2 0 1 2 4 14 302 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 598
cert_cover_5 2 0 0 1 3 5 22 598 3
cert_coverFacet 3 278
cert_cover_2 3 1 0 3 7 22 278 3
cert_coverFacet 4 410
cert_cover_5 4 1 0 2 3 6 138 410 2
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 100 484 3
cert_coverFacet 7 612
cert_cover_2 7 4 1 5 8 100 612 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1030

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_1031.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1031

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 563, 835, 387, 397, 361, 609, 790, 178, 402, 220, 844, 628, 404, 248, 35, 131, 259, 515, 41, 137, 265, 97, 545, 321, 577, 385, 50, 146, 274, 530, 162, 386, 770, 76, 140, 268, 84, 148, 276, 532, 580, 388, 772, 216, 104, 168, 328, 112, 176, 560, 400, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_563, vertices_835, vertices_387, vertices_397, vertices_361, vertices_609, vertices_790, vertices_178, vertices_402, vertices_220, vertices_844, vertices_628, vertices_404, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_41, vertices_137, vertices_265, vertices_97, vertices_545, vertices_321, vertices_577, vertices_385, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_386, vertices_770, vertices_76, vertices_140, vertices_268, vertices_84, vertices_148, vertices_276, vertices_532, vertices_580, vertices_388, vertices_772, vertices_216, vertices_104, vertices_168, vertices_328, vertices_112, vertices_176, vertices_560, vertices_400, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_563), (false, vertices_835), (false, vertices_387), (false, vertices_397), (false, vertices_361), (false, vertices_609), (true, vertices_146), (true, vertices_274), (true, vertices_76), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_580), (true, vertices_772), (true, vertices_216), (true, vertices_112), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 15 else
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_609) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_216) then 22 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_609), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 5 6 216
cert_row_4 1 0 1 3 7 8 790 274 1
cert_row_4 2 1 2 5 7 8 844 76 3
cert_row_4 3 1 3 4 5 8 628 84 2
cert_rows
cert_pivot_2 6 0 2 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 274 790 1
cert_coverFacet 1 178
cert_cover_2 1 3 0 4 6 50 178 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 220
cert_cover_5 3 0 1 2 3 5 76 220 2
cert_coverFacet 4 844
cert_cover_5 4 2 1 2 5 7 76 844 3
cert_coverFacet 5 628
cert_cover_5 5 3 1 3 4 5 84 628 2
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 248
cert_cover_5 7 0 2 3 4 5 216 248 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1031

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_1032.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1032

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 333, 805, 709, 345, 625, 782, 186, 282, 650, 738, 802, 220, 652, 240, 69, 261, 517, 329, 49, 81, 273, 289, 545, 577, 26, 138, 266, 522, 50, 274, 162, 290, 546, 642, 770, 76, 140, 268, 524, 196, 644, 772, 88, 152, 280, 648, 112, 176, 208, 224, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_333, vertices_805, vertices_709, vertices_345, vertices_625, vertices_782, vertices_186, vertices_282, vertices_650, vertices_738, vertices_802, vertices_220, vertices_652, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_329, vertices_49, vertices_81, vertices_273, vertices_289, vertices_545, vertices_577, vertices_26, vertices_138, vertices_266, vertices_522, vertices_50, vertices_274, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_76, vertices_140, vertices_268, vertices_524, vertices_196, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_648, vertices_112, vertices_176, vertices_208, vertices_224, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_333), (false, vertices_805), (false, vertices_709), (false, vertices_345), (false, vertices_625), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_162), (true, vertices_546), (true, vertices_642), (true, vertices_770), (true, vertices_140), (true, vertices_524), (true, vertices_152), (true, vertices_648), (true, vertices_176), (true, vertices_208), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 16 else
  if p.val = (false, vertices_333) then 21 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 26 1 138 2 266 522 162 546 642 770 140 524 152 648 176 208 224 307 805 709 333 345 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 0 4 5 6 8 738 162 2
cert_row_4 2 0 2 3 4 6 186 26 3
cert_row_4 3 1 2 3 5 6 220 76 2
cert_rows
cert_pivot_2 7 8 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 186
cert_cover_5 1 2 0 2 3 4 26 186 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 738
cert_cover_5 4 1 0 4 5 6 162 738 2
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 220
cert_cover_5 6 3 1 2 3 5 76 220 2
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 240
cert_cover_2 8 4 3 5 6 112 240 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1032

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3573 : Certifies 3573 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1002.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3574 : Certifies 3574 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1003.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3575 : Certifies 3575 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1004.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3576 : Certifies 3576 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1005.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3577 : Certifies 3577 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1006.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3578 : Certifies 3578 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1007.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3579 : Certifies 3579 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1008.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3580 : Certifies 3580 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1009.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3581 : Certifies 3581 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1010.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3582 : Certifies 3582 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1011.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3583 : Certifies 3583 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1012.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3584 : Certifies 3584 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1013.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3585 : Certifies 3585 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1014.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3586 : Certifies 3586 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1015.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3587 : Certifies 3587 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1016.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3588 : Certifies 3588 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1017.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3589 : Certifies 3589 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1019.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3590 : Certifies 3590 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1020.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3591 : Certifies 3591 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1021.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3592 : Certifies 3592 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1022.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3593 : Certifies 3593 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1023.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3594 : Certifies 3594 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1024.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3595 : Certifies 3595 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1025.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3596 : Certifies 3596 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1026.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3597 : Certifies 3597 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1027.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3598 : Certifies 3598 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1028.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3599 : Certifies 3599 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1029.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3600 : Certifies 3600 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1030.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3601 : Certifies 3601 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1031.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3602 : Certifies 3602 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1032.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B118 (j : Fin 30) :
    Certifies (3573 + j.val) := by
  fin_cases j
  · exact projection_3573
  · exact projection_3574
  · exact projection_3575
  · exact projection_3576
  · exact projection_3577
  · exact projection_3578
  · exact projection_3579
  · exact projection_3580
  · exact projection_3581
  · exact projection_3582
  · exact projection_3583
  · exact projection_3584
  · exact projection_3585
  · exact projection_3586
  · exact projection_3587
  · exact projection_3588
  · exact projection_3589
  · exact projection_3590
  · exact projection_3591
  · exact projection_3592
  · exact projection_3593
  · exact projection_3594
  · exact projection_3595
  · exact projection_3596
  · exact projection_3597
  · exact projection_3598
  · exact projection_3599
  · exact projection_3600
  · exact projection_3601
  · exact projection_3602

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
