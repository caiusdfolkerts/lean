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
/- Source: ProjectionCertificates/R_m15e10q1_0778.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0778

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 781, 601, 457, 241, 657, 558, 182, 390, 774, 626, 658, 364, 484, 616, 73, 265, 521, 81, 145, 529, 193, 385, 641, 769, 38, 134, 262, 518, 50, 146, 530, 546, 386, 642, 770, 44, 268, 524, 356, 164, 388, 772, 104, 552, 328, 584, 112, 176, 592, 656, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_781, vertices_601, vertices_457, vertices_241, vertices_657, vertices_558, vertices_182, vertices_390, vertices_774, vertices_626, vertices_658, vertices_364, vertices_484, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_81, vertices_145, vertices_529, vertices_193, vertices_385, vertices_641, vertices_769, vertices_38, vertices_134, vertices_262, vertices_518, vertices_50, vertices_146, vertices_530, vertices_546, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_524, vertices_356, vertices_164, vertices_388, vertices_772, vertices_104, vertices_552, vertices_328, vertices_584, vertices_112, vertices_176, vertices_592, vertices_656, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_781), (false, vertices_601), (false, vertices_457), (false, vertices_241), (false, vertices_657), (true, vertices_38), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_546), (true, vertices_44), (true, vertices_356), (true, vertices_164), (true, vertices_388), (true, vertices_104), (true, vertices_552), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_356) then 19 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 657 2 38 1 134 3 262 518 50 146 530 546 44 164 388 104 552 608 899 781 356 601 457 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 7 356
cert_row_4 1 0 1 2 4 8 558 38 2
cert_row_4 2 0 1 3 4 6 182 38 2
cert_row_4 3 0 3 4 5 8 626 50 3
cert_rows
cert_pivot_2 7 2 1 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 38 558 2
cert_coverFacet 1 182
cert_cover_5 1 2 0 1 3 4 38 182 2
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 626
cert_cover_5 4 3 0 3 4 5 50 626 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 364
cert_cover_5 6 0 1 2 4 5 44 364 3
cert_coverFacet 7 484
cert_cover_5 7 0 1 4 5 6 356 484 3
cert_coverFacet 8 616
cert_cover_2 8 4 2 5 8 104 616 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0778

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0779.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0779

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 523, 195, 835, 557, 817, 481, 206, 526, 598, 60, 220, 564, 440, 976, 11, 67, 131, 515, 41, 521, 161, 289, 545, 193, 321, 769, 14, 70, 518, 138, 522, 194, 578, 28, 44, 204, 524, 52, 84, 532, 548, 56, 152, 168, 304, 560, 208, 592, 400, 784, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_523, vertices_195, vertices_835, vertices_557, vertices_817, vertices_481, vertices_206, vertices_526, vertices_598, vertices_60, vertices_220, vertices_564, vertices_440, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_131, vertices_515, vertices_41, vertices_521, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_769, vertices_14, vertices_70, vertices_518, vertices_138, vertices_522, vertices_194, vertices_578, vertices_28, vertices_44, vertices_204, vertices_524, vertices_52, vertices_84, vertices_532, vertices_548, vertices_56, vertices_152, vertices_168, vertices_304, vertices_560, vertices_208, vertices_592, vertices_400, vertices_784, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_523), (false, vertices_195), (false, vertices_835), (false, vertices_557), (false, vertices_817), (false, vertices_481), (true, vertices_14), (true, vertices_70), (true, vertices_518), (true, vertices_28), (true, vertices_204), (true, vertices_52), (true, vertices_84), (true, vertices_532), (true, vertices_56), (true, vertices_152), (true, vertices_208), (true, vertices_592), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 15 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_817) then 22 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_70) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_204) then 19 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 70 2
cert_row_2 1 1 2 5 6 204
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 598
cert_cover_5 2 0 0 1 3 5 70 598 2
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 220
cert_cover_5 4 1 1 2 3 5 28 220 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 440
cert_cover_5 6 2 2 3 4 6 56 440 3
cert_coverFacet 7 976
cert_cover_5 7 3 3 5 6 7 208 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0779

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0780.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0780

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 341, 709, 665, 281, 777, 241, 558, 358, 186, 282, 778, 370, 612, 744, 69, 261, 517, 25, 265, 521, 81, 145, 273, 193, 641, 769, 38, 262, 518, 26, 42, 266, 522, 50, 274, 354, 770, 100, 548, 324, 580, 152, 280, 168, 552, 648, 776, 112, 176, 336, 224, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_341, vertices_709, vertices_665, vertices_281, vertices_777, vertices_241, vertices_558, vertices_358, vertices_186, vertices_282, vertices_778, vertices_370, vertices_612, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_25, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_193, vertices_641, vertices_769, vertices_38, vertices_262, vertices_518, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_354, vertices_770, vertices_100, vertices_548, vertices_324, vertices_580, vertices_152, vertices_280, vertices_168, vertices_552, vertices_648, vertices_776, vertices_112, vertices_176, vertices_336, vertices_224, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_341), (false, vertices_709), (false, vertices_665), (false, vertices_281), (false, vertices_777), (false, vertices_241), (true, vertices_38), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_354), (true, vertices_100), (true, vertices_548), (true, vertices_168), (true, vertices_552), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_50) then 7 else
  if p.val = (true, vertices_274) then 8 else
  if p.val = (true, vertices_354) then 16 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 281 1 777 38 26 42 266 522 50 274 100 548 168 552 608 775 354 341 709 665 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 5 7 354
cert_row_4 1 0 1 2 4 8 558 38 2
cert_row_4 2 0 2 3 4 6 186 26 3
cert_row_4 3 2 4 5 6 8 744 168 2
cert_rows
cert_pivot_2 7 1 0 2
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 38 558 2
cert_coverFacet 1 358
cert_cover_5 1 0 0 1 4 5 38 358 3
cert_coverFacet 2 186
cert_cover_5 2 2 0 2 3 4 26 186 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 370
cert_cover_5 5 0 0 3 4 5 50 370 3
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 168 744 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0780

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0781.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0781

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 299, 51, 653, 781, 213, 325, 369, 806, 538, 778, 626, 740, 356, 728, 11, 19, 35, 525, 69, 133, 261, 137, 265, 49, 81, 145, 289, 321, 26, 266, 522, 50, 530, 290, 546, 770, 100, 292, 548, 196, 324, 644, 772, 152, 536, 648, 776, 112, 208, 592, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_299, vertices_51, vertices_653, vertices_781, vertices_213, vertices_325, vertices_369, vertices_806, vertices_538, vertices_778, vertices_626, vertices_740, vertices_356, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_35, vertices_525, vertices_69, vertices_133, vertices_261, vertices_137, vertices_265, vertices_49, vertices_81, vertices_145, vertices_289, vertices_321, vertices_26, vertices_266, vertices_522, vertices_50, vertices_530, vertices_290, vertices_546, vertices_770, vertices_100, vertices_292, vertices_548, vertices_196, vertices_324, vertices_644, vertices_772, vertices_152, vertices_536, vertices_648, vertices_776, vertices_112, vertices_208, vertices_592, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_299), (false, vertices_51), (false, vertices_653), (false, vertices_781), (false, vertices_213), (false, vertices_325), (false, vertices_369), (true, vertices_522), (true, vertices_530), (true, vertices_546), (true, vertices_770), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_536), (true, vertices_592), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 14 else
  if p.val = (false, vertices_299) then 15 else
  if p.val = (false, vertices_51) then 0 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_325) then 1 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 20 => Sum.inl 2
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
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_4 1 0 3 4 5 8 626 50 3
cert_row_4 2 1 4 5 6 8 740 100 3
cert_row_4 3 2 3 5 6 8 728 152 2
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 626
cert_cover_5 3 1 0 3 4 5 50 626 3
cert_coverFacet 4 740
cert_cover_5 4 2 1 4 5 6 100 740 3
cert_coverFacet 5 356
cert_cover_2 5 4 1 5 7 100 356 3
cert_coverFacet 6 728
cert_cover_5 6 3 2 3 5 6 152 728 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0781

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0782.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0782

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [211, 29, 525, 597, 409, 841, 481, 158, 174, 566, 594, 226, 866, 556, 936, 13, 21, 517, 25, 265, 521, 81, 145, 193, 321, 577, 385, 142, 22, 38, 82, 146, 530, 98, 162, 546, 194, 578, 28, 44, 524, 532, 548, 152, 168, 552, 392, 776, 592, 224, 352, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_29, vertices_525, vertices_597, vertices_409, vertices_841, vertices_481, vertices_158, vertices_174, vertices_566, vertices_594, vertices_226, vertices_866, vertices_556, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_517, vertices_25, vertices_265, vertices_521, vertices_81, vertices_145, vertices_193, vertices_321, vertices_577, vertices_385, vertices_142, vertices_22, vertices_38, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_28, vertices_44, vertices_524, vertices_532, vertices_548, vertices_152, vertices_168, vertices_552, vertices_392, vertices_776, vertices_592, vertices_224, vertices_352, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_29), (false, vertices_525), (false, vertices_597), (false, vertices_409), (false, vertices_841), (false, vertices_481), (true, vertices_142), (true, vertices_22), (true, vertices_38), (true, vertices_530), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_578), (true, vertices_44), (true, vertices_548), (true, vertices_168), (true, vertices_552), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 15 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_142) then 16 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_38) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_29), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_142), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
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
cert_row_4 0 0 1 3 4 8 566 22 3
cert_row_2 1 0 1 2 6 142
cert_row_4 2 0 4 5 7 8 866 98 3
cert_row_4 3 2 4 6 7 8 936 168 3
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 142 158 3
cert_coverFacet 1 174
cert_cover_5 1 1 0 1 2 4 142 174 3
cert_coverFacet 2 566
cert_cover_5 2 0 0 1 3 4 22 566 3
cert_coverFacet 3 594
cert_cover_2 3 3 0 5 8 82 594 3
cert_coverFacet 4 226
cert_cover_2 4 4 0 5 6 98 226 3
cert_coverFacet 5 866
cert_cover_5 5 2 0 4 5 7 98 866 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 936
cert_cover_5 7 3 2 4 6 7 168 936 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0782

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0783.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0783

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 789, 229, 293, 581, 425, 465, 710, 346, 794, 682, 202, 812, 676, 456, 37, 69, 261, 517, 81, 273, 529, 161, 289, 193, 577, 385, 282, 74, 138, 522, 82, 530, 194, 578, 642, 164, 292, 548, 196, 580, 644, 772, 168, 296, 552, 200, 328, 392, 776, 336, 784, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_789, vertices_229, vertices_293, vertices_581, vertices_425, vertices_465, vertices_710, vertices_346, vertices_794, vertices_682, vertices_202, vertices_812, vertices_676, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_261, vertices_517, vertices_81, vertices_273, vertices_529, vertices_161, vertices_289, vertices_193, vertices_577, vertices_385, vertices_282, vertices_74, vertices_138, vertices_522, vertices_82, vertices_530, vertices_194, vertices_578, vertices_642, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_644, vertices_772, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_392, vertices_776, vertices_336, vertices_784, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_789), (false, vertices_229), (false, vertices_293), (false, vertices_581), (false, vertices_425), (false, vertices_465), (true, vertices_282), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_194), (true, vertices_642), (true, vertices_548), (true, vertices_644), (true, vertices_552), (true, vertices_200), (true, vertices_328), (true, vertices_776), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_581) then 1 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_282) then 16 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 293 1 581 74 138 522 194 642 548 644 552 200 328 776 672 595 282 789 229 425 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 7 282
cert_row_4 1 0 1 5 6 8 710 194 1
cert_row_4 2 0 2 4 6 8 682 138 2
cert_row_4 3 1 2 4 7 8 812 292 1
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 1 0 1 5 6 194 710 1
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 5 282 346 3
cert_coverFacet 2 794
cert_cover_5 2 0 0 2 3 8 282 794 3
cert_coverFacet 3 682
cert_cover_5 3 2 0 2 4 6 138 682 2
cert_coverFacet 4 202
cert_cover_2 4 2 0 5 6 74 202 3
cert_coverFacet 5 812
cert_cover_5 5 3 1 2 4 7 292 812 1
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 456
cert_cover_2 7 5 2 6 7 200 456 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0783

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0784.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0784

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 155, 395, 595, 357, 581, 465, 538, 810, 684, 724, 228, 804, 664, 488, 139, 19, 259, 515, 69, 261, 517, 81, 145, 321, 577, 385, 26, 266, 522, 530, 770, 100, 164, 292, 548, 196, 580, 644, 772, 152, 536, 168, 296, 552, 392, 648, 208, 592, 656, 224, 352, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_155, vertices_395, vertices_595, vertices_357, vertices_581, vertices_465, vertices_538, vertices_810, vertices_684, vertices_724, vertices_228, vertices_804, vertices_664, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_139, vertices_19, vertices_259, vertices_515, vertices_69, vertices_261, vertices_517, vertices_81, vertices_145, vertices_321, vertices_577, vertices_385, vertices_26, vertices_266, vertices_522, vertices_530, vertices_770, vertices_100, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_644, vertices_772, vertices_152, vertices_536, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_208, vertices_592, vertices_656, vertices_224, vertices_352, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_155), (false, vertices_395), (false, vertices_595), (false, vertices_357), (false, vertices_581), (false, vertices_465), (true, vertices_522), (true, vertices_164), (true, vertices_548), (true, vertices_196), (true, vertices_644), (true, vertices_536), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_648), (true, vertices_656), (true, vertices_224), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_155) then 18 else
  if p.val = (false, vertices_395) then 19 else
  if p.val = (false, vertices_595) then 20 else
  if p.val = (false, vertices_357) then 16 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_4 0 0 2 4 7 8 810 266 2
cert_row_4 1 1 3 5 6 8 724 196 1
cert_row_4 2 1 2 4 6 8 684 164 1
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 538
cert_cover_2 0 2 0 3 8 26 538 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 266 810 2
cert_coverFacet 2 684
cert_cover_5 2 2 1 2 4 6 164 684 1
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 196 724 1
cert_coverFacet 4 228
cert_cover_2 4 4 1 5 6 100 228 3
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coverFacet 6 664
cert_cover_2 6 3 2 6 8 152 664 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 168 488 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0784

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0785.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0785

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 397, 309, 613, 645, 569, 281, 710, 346, 538, 458, 626, 228, 420, 496, 37, 133, 261, 517, 25, 137, 265, 521, 49, 273, 545, 641, 26, 330, 138, 522, 82, 530, 194, 578, 642, 100, 164, 292, 196, 580, 388, 644, 280, 536, 392, 112, 304, 560, 336, 224, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_397, vertices_309, vertices_613, vertices_645, vertices_569, vertices_281, vertices_710, vertices_346, vertices_538, vertices_458, vertices_626, vertices_228, vertices_420, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_517, vertices_25, vertices_137, vertices_265, vertices_521, vertices_49, vertices_273, vertices_545, vertices_641, vertices_26, vertices_330, vertices_138, vertices_522, vertices_82, vertices_530, vertices_194, vertices_578, vertices_642, vertices_100, vertices_164, vertices_292, vertices_196, vertices_580, vertices_388, vertices_644, vertices_280, vertices_536, vertices_392, vertices_112, vertices_304, vertices_560, vertices_336, vertices_224, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_397), (false, vertices_309), (false, vertices_613), (false, vertices_645), (false, vertices_569), (false, vertices_281), (true, vertices_26), (true, vertices_330), (true, vertices_82), (true, vertices_530), (true, vertices_194), (true, vertices_578), (true, vertices_164), (true, vertices_196), (true, vertices_112), (true, vertices_336), (true, vertices_224), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_309) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_569) then 22 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_330) then 16 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 645 1 281 26 82 530 194 578 164 196 112 336 224 416 448 651 330 397 309 613 569
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 7 330
cert_row_4 1 0 1 5 6 8 710 194 1
cert_row_4 2 0 3 4 5 8 626 82 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 1 0 1 5 6 194 710 1
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 5 26 346 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 458
cert_cover_5 3 0 0 2 5 6 330 458 3
cert_coverFacet 4 626
cert_cover_5 4 2 0 3 4 5 82 626 2
cert_coverFacet 5 228
cert_cover_2 5 4 1 5 6 100 228 3
cert_coverFacet 6 420
cert_cover_2 6 4 1 6 7 164 420 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0785

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0786.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0786

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [39, 519, 675, 301, 653, 409, 481, 542, 342, 358, 626, 284, 664, 976, 736, 7, 35, 515, 13, 37, 517, 137, 265, 161, 289, 385, 641, 22, 38, 326, 518, 82, 530, 98, 546, 28, 268, 524, 276, 292, 152, 280, 536, 648, 336, 592, 400, 656, 224, 352, 608, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_39, vertices_519, vertices_675, vertices_301, vertices_653, vertices_409, vertices_481, vertices_542, vertices_342, vertices_358, vertices_626, vertices_284, vertices_664, vertices_976, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_35, vertices_515, vertices_13, vertices_37, vertices_517, vertices_137, vertices_265, vertices_161, vertices_289, vertices_385, vertices_641, vertices_22, vertices_38, vertices_326, vertices_518, vertices_82, vertices_530, vertices_98, vertices_546, vertices_28, vertices_268, vertices_524, vertices_276, vertices_292, vertices_152, vertices_280, vertices_536, vertices_648, vertices_336, vertices_592, vertices_400, vertices_656, vertices_224, vertices_352, vertices_608, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_39), (false, vertices_519), (false, vertices_675), (false, vertices_301), (false, vertices_653), (false, vertices_409), (false, vertices_481), (true, vertices_22), (true, vertices_326), (true, vertices_82), (true, vertices_530), (true, vertices_98), (true, vertices_28), (true, vertices_276), (true, vertices_536), (true, vertices_336), (true, vertices_592), (true, vertices_656), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_39) then 0 else
  if p.val = (false, vertices_519) then 1 else
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_326) then 16 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_53 0 39 1 519 22 82 530 98 28 276 536 336 592 656 608 704 675 326 301 653 409 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 22 2
cert_row_2 1 0 1 5 7 326
cert_row_4 2 0 3 4 5 8 626 82 2
cert_row_4 3 3 5 6 7 8 976 336 2
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 22 542 2
cert_coverFacet 1 342
cert_cover_5 1 1 0 1 3 5 22 342 3
cert_coverFacet 2 358
cert_cover_5 2 1 0 1 4 5 38 358 3
cert_coverFacet 3 626
cert_cover_5 3 2 0 3 4 5 82 626 2
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 664
cert_cover_2 5 3 2 6 8 152 664 3
cert_coverFacet 6 976
cert_cover_5 6 3 3 5 6 7 336 976 2
cert_coverFacet 7 736
cert_cover_2 7 5 4 6 8 224 736 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0786

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0787.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0787

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 541, 77, 613, 457, 721, 401, 302, 558, 538, 914, 738, 418, 332, 484, 13, 69, 517, 25, 73, 265, 145, 273, 529, 193, 577, 385, 46, 26, 266, 522, 274, 530, 162, 290, 546, 386, 642, 76, 268, 524, 100, 292, 548, 324, 536, 328, 400, 656, 224, 608, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_541, vertices_77, vertices_613, vertices_457, vertices_721, vertices_401, vertices_302, vertices_558, vertices_538, vertices_914, vertices_738, vertices_418, vertices_332, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_25, vertices_73, vertices_265, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_46, vertices_26, vertices_266, vertices_522, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_76, vertices_268, vertices_524, vertices_100, vertices_292, vertices_548, vertices_324, vertices_536, vertices_328, vertices_400, vertices_656, vertices_224, vertices_608, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_541), (false, vertices_77), (false, vertices_613), (false, vertices_457), (false, vertices_721), (false, vertices_401), (true, vertices_46), (true, vertices_522), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_268), (true, vertices_292), (true, vertices_324), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 15 else
  if p.val = (false, vertices_541) then 18 else
  if p.val = (false, vertices_77) then 0 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (true, vertices_46) then 16 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 77 1 401 522 530 162 290 546 386 642 268 292 324 224 416 283 46 541 613 457 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 3 6 7 8 914 274 2
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 7 46 302 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 8 46 558 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 914
cert_cover_5 3 1 0 3 6 7 274 914 2
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 162 738 2
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 332
cert_cover_2 6 2 1 5 7 76 332 3
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 100 484 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0787

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0788.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0788

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 147, 707, 613, 313, 361, 465, 902, 794, 402, 572, 108, 460, 780, 708, 19, 131, 515, 297, 49, 145, 273, 97, 545, 193, 321, 577, 146, 274, 530, 386, 642, 770, 44, 76, 268, 524, 100, 548, 196, 580, 388, 644, 772, 56, 280, 536, 104, 328, 776, 560, 400, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_147, vertices_707, vertices_613, vertices_313, vertices_361, vertices_465, vertices_902, vertices_794, vertices_402, vertices_572, vertices_108, vertices_460, vertices_780, vertices_708] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_515, vertices_297, vertices_49, vertices_145, vertices_273, vertices_97, vertices_545, vertices_193, vertices_321, vertices_577, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_268, vertices_524, vertices_100, vertices_548, vertices_196, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_280, vertices_536, vertices_104, vertices_328, vertices_776, vertices_560, vertices_400, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_147), (false, vertices_707), (false, vertices_613), (false, vertices_313), (false, vertices_361), (false, vertices_465), (true, vertices_274), (true, vertices_386), (true, vertices_770), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_196), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_536), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 15 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_313) then 20 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_776) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_4 0 1 2 3 4 8 572 44 2
cert_row_4 1 0 2 3 7 8 794 274 1
cert_row_4 2 0 1 6 7 8 902 386 1
cert_row_4 3 1 2 5 6 7 460 76 3
cert_rows
cert_pivot_2 4 3 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 2 0 1 6 7 386 902 1
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 274 794 1
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 572
cert_cover_5 3 0 1 2 3 4 44 572 2
cert_coverFacet 4 108
cert_cover_2 4 2 1 4 5 44 108 3
cert_coverFacet 5 460
cert_cover_5 5 3 1 2 5 6 76 460 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0788

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0789.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0789

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 597, 149, 677, 361, 425, 465, 782, 106, 682, 330, 850, 412, 652, 788, 21, 133, 517, 297, 81, 145, 97, 161, 545, 321, 577, 385, 42, 74, 266, 522, 98, 546, 322, 578, 770, 140, 268, 524, 148, 276, 532, 644, 772, 104, 168, 328, 392, 648, 336, 592, 400, 784, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_597, vertices_149, vertices_677, vertices_361, vertices_425, vertices_465, vertices_782, vertices_106, vertices_682, vertices_330, vertices_850, vertices_412, vertices_652, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_297, vertices_81, vertices_145, vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_42, vertices_74, vertices_266, vertices_522, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_644, vertices_772, vertices_104, vertices_168, vertices_328, vertices_392, vertices_648, vertices_336, vertices_592, vertices_400, vertices_784, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_597), (false, vertices_149), (false, vertices_677), (false, vertices_361), (false, vertices_425), (false, vertices_465), (true, vertices_42), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_322), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_772), (true, vertices_648), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 15 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_784) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_4 0 0 2 4 6 8 682 42 3
cert_row_4 1 0 3 5 7 8 850 322 1
cert_row_4 2 0 1 2 7 8 782 266 1
cert_row_4 3 1 2 3 6 7 412 140 2
cert_rows
cert_pivot_2 4 5 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 266 782 1
cert_coverFacet 1 106
cert_cover_2 1 2 0 4 5 42 106 3
cert_coverFacet 2 682
cert_cover_5 2 0 0 2 4 6 42 682 3
cert_coverFacet 3 330
cert_cover_2 3 2 0 5 7 74 330 3
cert_coverFacet 4 850
cert_cover_5 4 1 0 3 5 7 322 850 1
cert_coverFacet 5 412
cert_cover_5 5 3 1 2 3 6 140 412 2
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0789

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0790.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0790

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 677, 793, 425, 713, 118, 550, 710, 602, 306, 786, 460, 372, 420, 344, 137, 265, 521, 161, 289, 545, 641, 769, 38, 70, 518, 50, 82, 274, 530, 290, 546, 578, 770, 116, 164, 292, 548, 196, 324, 388, 644, 88, 280, 536, 200, 328, 584, 392, 304, 336, 784, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_677, vertices_793, vertices_425, vertices_713, vertices_118, vertices_550, vertices_710, vertices_602, vertices_306, vertices_786, vertices_460, vertices_372, vertices_420, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_38, vertices_70, vertices_518, vertices_50, vertices_82, vertices_274, vertices_530, vertices_290, vertices_546, vertices_578, vertices_770, vertices_116, vertices_164, vertices_292, vertices_548, vertices_196, vertices_324, vertices_388, vertices_644, vertices_88, vertices_280, vertices_536, vertices_200, vertices_328, vertices_584, vertices_392, vertices_304, vertices_336, vertices_784, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_677), (false, vertices_793), (false, vertices_425), (false, vertices_713), (true, vertices_38), (true, vertices_70), (true, vertices_518), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_578), (true, vertices_116), (true, vertices_292), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_88), (true, vertices_328), (true, vertices_304), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_793) then 22 else
  if p.val = (false, vertices_425) then 23 else
  if p.val = (false, vertices_713) then 24 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_116) then 20 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_336) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_116), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 4 5 116
cert_row_4 1 0 2 3 5 8 602 82 1
cert_row_4 2 0 1 5 6 8 710 70 3
cert_row_4 3 1 2 5 6 7 460 196 1
cert_rows
cert_pivot_2 4 3 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 0 0 1 3 4 38 118 2
cert_coverFacet 1 550
cert_cover_2 1 1 0 4 8 38 550 3
cert_coverFacet 2 710
cert_cover_5 2 2 0 1 5 6 70 710 3
cert_coverFacet 3 602
cert_cover_5 3 1 0 2 3 5 82 602 1
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 460
cert_cover_5 6 3 1 2 5 6 196 460 1
cert_coverFacet 7 372
cert_cover_5 7 0 1 3 4 7 116 372 3
cert_coverFacet 8 420
cert_cover_2 8 4 1 6 7 164 420 3
cert_coverFacet 9 344
cert_cover_2 9 3 2 5 7 88 344 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0790

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0792.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0792

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 837, 681, 721, 481, 30, 302, 598, 774, 666, 554, 284, 340, 248, 376, 161, 289, 545, 193, 321, 577, 641, 769, 14, 22, 262, 518, 26, 42, 522, 530, 290, 546, 770, 28, 268, 84, 276, 324, 580, 772, 120, 152, 280, 168, 296, 552, 648, 208, 336, 592, 656, 224, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_837, vertices_681, vertices_721, vertices_481, vertices_30, vertices_302, vertices_598, vertices_774, vertices_666, vertices_554, vertices_284, vertices_340, vertices_248, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_518, vertices_26, vertices_42, vertices_522, vertices_530, vertices_290, vertices_546, vertices_770, vertices_28, vertices_268, vertices_84, vertices_276, vertices_324, vertices_580, vertices_772, vertices_120, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_648, vertices_208, vertices_336, vertices_592, vertices_656, vertices_224, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_837), (false, vertices_681), (false, vertices_721), (false, vertices_481), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_530), (true, vertices_28), (true, vertices_268), (true, vertices_84), (true, vertices_276), (true, vertices_120), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 20 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_120) then 22 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_296) then 14 else
  if p.val = (true, vertices_336) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_120), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 7 302 14 3
cert_row_2 1 2 3 4 5 120
cert_row_4 2 0 1 3 5 8 598 22 3
cert_row_4 3 0 2 3 6 8 666 26 3
cert_rows
cert_pivot_2 7 4 1 0
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 302
cert_cover_5 1 0 0 1 2 4 14 302 3
cert_coverFacet 2 598
cert_cover_5 2 2 0 1 3 5 22 598 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 666
cert_cover_5 4 3 0 2 3 6 26 666 3
cert_coverFacet 5 554
cert_cover_2 5 2 0 4 8 42 554 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coverFacet 8 248
cert_cover_5 8 1 2 3 4 6 120 248 3
cert_coverFacet 9 376
cert_cover_5 9 1 2 3 4 7 120 376 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0792

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0793.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0793

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 99, 419, 771, 789, 233, 465, 618, 802, 156, 284, 812, 716, 724, 440, 35, 67, 259, 515, 81, 273, 529, 97, 161, 193, 385, 769, 98, 290, 546, 578, 770, 28, 140, 268, 524, 148, 276, 532, 708, 772, 152, 280, 104, 168, 296, 552, 200, 584, 208, 592, 400, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_99, vertices_419, vertices_771, vertices_789, vertices_233, vertices_465, vertices_618, vertices_802, vertices_156, vertices_284, vertices_812, vertices_716, vertices_724, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_259, vertices_515, vertices_81, vertices_273, vertices_529, vertices_97, vertices_161, vertices_193, vertices_385, vertices_769, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_28, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_708, vertices_772, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_584, vertices_208, vertices_592, vertices_400, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_99), (false, vertices_419), (false, vertices_771), (false, vertices_789), (false, vertices_233), (false, vertices_465), (true, vertices_546), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_708), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_552), (true, vertices_584), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_99) then 0 else
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_708) then 19 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
cert_nodeAtPriority_44 99 771 546 28 140 268 524 148 152 280 296 552 584 800 595 419 789 708 233 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 8 618 98 1
cert_row_2 1 1 5 6 8 708
cert_row_4 2 1 2 4 7 8 812 268 2
cert_row_4 3 2 3 4 6 7 440 152 2
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 618
cert_cover_5 0 0 0 2 4 5 98 618 1
cert_coverFacet 1 802
cert_cover_2 1 4 0 7 8 290 802 3
cert_coverFacet 2 156
cert_cover_2 2 2 1 3 6 28 156 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 812
cert_cover_5 4 2 1 2 4 7 268 812 2
cert_coverFacet 5 716
cert_cover_5 5 1 1 2 5 6 140 716 2
cert_coverFacet 6 724
cert_cover_5 6 1 1 3 5 6 148 724 2
cert_coverFacet 7 440
cert_cover_5 7 3 2 3 4 6 152 440 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0793

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0794.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0794

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [27, 587, 115, 229, 709, 185, 905, 838, 410, 778, 338, 372, 676, 804, 944, 11, 19, 67, 197, 25, 137, 521, 49, 97, 161, 577, 641, 26, 266, 522, 82, 274, 322, 578, 770, 100, 164, 292, 548, 324, 580, 644, 772, 152, 392, 776, 112, 176, 304, 336, 400, 672, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_27, vertices_587, vertices_115, vertices_229, vertices_709, vertices_185, vertices_905, vertices_838, vertices_410, vertices_778, vertices_338, vertices_372, vertices_676, vertices_804, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_67, vertices_197, vertices_25, vertices_137, vertices_521, vertices_49, vertices_97, vertices_161, vertices_577, vertices_641, vertices_26, vertices_266, vertices_522, vertices_82, vertices_274, vertices_322, vertices_578, vertices_770, vertices_100, vertices_164, vertices_292, vertices_548, vertices_324, vertices_580, vertices_644, vertices_772, vertices_152, vertices_392, vertices_776, vertices_112, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_27), (false, vertices_587), (false, vertices_115), (false, vertices_229), (false, vertices_709), (false, vertices_185), (false, vertices_905), (true, vertices_266), (true, vertices_274), (true, vertices_322), (true, vertices_770), (true, vertices_292), (true, vertices_548), (true, vertices_324), (true, vertices_772), (true, vertices_304), (true, vertices_336), (true, vertices_400), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_27) then 0 else
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_115) then 16 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_905) then 22 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_27), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 26 3
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 1 3 4 5 7 372 100 1
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 6 26 410 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 372
cert_cover_5 4 2 1 3 4 5 100 372 1
cert_coverFacet 5 676
cert_cover_2 5 4 1 6 8 164 676 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 944
cert_cover_5 7 3 3 4 6 7 176 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0794

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0795.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0795

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 781, 789, 361, 681, 433, 214, 618, 594, 226, 674, 604, 332, 404, 484, 773, 41, 265, 521, 145, 273, 529, 161, 289, 641, 82, 146, 530, 98, 162, 546, 194, 578, 642, 76, 268, 524, 84, 148, 276, 532, 196, 324, 388, 104, 552, 328, 584, 592, 400, 224, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_781, vertices_789, vertices_361, vertices_681, vertices_433, vertices_214, vertices_618, vertices_594, vertices_226, vertices_674, vertices_604, vertices_332, vertices_404, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_773, vertices_41, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_641, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_76, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_388, vertices_104, vertices_552, vertices_328, vertices_584, vertices_592, vertices_400, vertices_224, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_781), (false, vertices_789), (false, vertices_361), (false, vertices_681), (false, vertices_433), (true, vertices_82), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_578), (true, vertices_76), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_584), (true, vertices_592), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 82 1 98 2 162 546 194 578 76 84 148 196 324 388 584 592 224 659 781 789 361 681 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 4 5 6 7 484 196 1
cert_row_4 1 0 1 3 5 6 214 82 1
cert_row_4 2 0 2 4 5 8 618 98 1
cert_row_4 3 1 2 3 5 8 604 76 2
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 1 0 1 3 5 82 214 1
cert_coverFacet 1 618
cert_cover_5 1 2 0 2 4 5 98 618 1
cert_coverFacet 2 594
cert_cover_2 2 3 0 5 8 82 594 3
cert_coverFacet 3 226
cert_cover_2 3 4 0 5 6 98 226 3
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 604
cert_cover_5 5 3 1 2 3 5 76 604 2
cert_coverFacet 6 332
cert_cover_2 6 2 1 5 7 76 332 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 484
cert_cover_5 8 0 1 4 5 6 196 484 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0795

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0796.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0796

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 805, 453, 645, 345, 241, 305, 654, 602, 458, 626, 226, 396, 780, 824, 133, 261, 517, 49, 81, 273, 161, 289, 545, 193, 321, 641, 74, 138, 522, 594, 98, 162, 546, 194, 642, 140, 268, 524, 388, 644, 772, 88, 280, 536, 328, 392, 776, 112, 304, 560, 224, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_805, vertices_453, vertices_645, vertices_345, vertices_241, vertices_305, vertices_654, vertices_602, vertices_458, vertices_626, vertices_226, vertices_396, vertices_780, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_49, vertices_81, vertices_273, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_74, vertices_138, vertices_522, vertices_594, vertices_98, vertices_162, vertices_546, vertices_194, vertices_642, vertices_140, vertices_268, vertices_524, vertices_388, vertices_644, vertices_772, vertices_88, vertices_280, vertices_536, vertices_328, vertices_392, vertices_776, vertices_112, vertices_304, vertices_560, vertices_224, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_805), (false, vertices_453), (false, vertices_645), (false, vertices_345), (false, vertices_241), (false, vertices_305), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_594), (true, vertices_98), (true, vertices_194), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_536), (true, vertices_392), (true, vertices_776), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_594) then 16 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_560) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 645 1 305 74 138 522 98 194 140 268 524 536 392 776 560 675 594 805 453 345 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_4 1 0 2 5 6 7 458 74 3
cert_row_2 2 0 3 5 8 594
cert_row_4 3 2 3 4 7 8 824 280 2
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 602
cert_cover_5 1 2 0 2 3 5 74 602 2
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 6 74 458 3
cert_coverFacet 3 626
cert_cover_5 3 2 0 3 4 5 594 626 2
cert_coverFacet 4 226
cert_cover_2 4 4 0 5 6 98 226 3
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 824
cert_cover_5 7 3 2 3 4 7 280 824 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0796

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0797.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0797

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 835, 387, 589, 341, 149, 433, 682, 818, 418, 236, 652, 244, 632, 848, 131, 259, 515, 21, 69, 133, 517, 145, 273, 321, 577, 385, 162, 290, 546, 386, 642, 770, 76, 140, 524, 84, 148, 228, 644, 104, 168, 552, 584, 648, 112, 176, 304, 560, 336, 592, 784, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_835, vertices_387, vertices_589, vertices_341, vertices_149, vertices_433, vertices_682, vertices_818, vertices_418, vertices_236, vertices_652, vertices_244, vertices_632, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_21, vertices_69, vertices_133, vertices_517, vertices_145, vertices_273, vertices_321, vertices_577, vertices_385, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_84, vertices_148, vertices_228, vertices_644, vertices_104, vertices_168, vertices_552, vertices_584, vertices_648, vertices_112, vertices_176, vertices_304, vertices_560, vertices_336, vertices_592, vertices_784, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_835), (false, vertices_387), (false, vertices_589), (false, vertices_341), (false, vertices_149), (false, vertices_433), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_140), (true, vertices_228), (true, vertices_104), (true, vertices_168), (true, vertices_552), (true, vertices_648), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 19 17 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_341) then 20 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_228) then 21 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_784) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_228), by decide +kernel⟩
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
cert_row_2 0 1 4 5 6 228
cert_row_4 1 0 2 4 6 8 682 162 1
cert_row_4 2 0 3 4 7 8 818 290 1
cert_row_4 3 2 3 4 5 8 632 104 1
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 682
cert_cover_5 0 1 0 2 4 6 162 682 1
cert_coverFacet 1 818
cert_cover_5 1 2 0 3 4 7 290 818 1
cert_coverFacet 2 418
cert_cover_2 2 4 0 6 7 162 418 3
cert_coverFacet 3 236
cert_cover_5 3 0 1 2 4 5 76 236 2
cert_coverFacet 4 652
cert_cover_2 4 2 1 6 8 140 652 3
cert_coverFacet 5 244
cert_cover_5 5 0 1 3 4 5 84 244 2
cert_coverFacet 6 632
cert_cover_5 6 3 2 3 4 5 104 632 1
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0797

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0798.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0798

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 789, 809, 433, 737, 342, 534, 710, 346, 154, 234, 844, 408, 616, 424, 145, 273, 529, 161, 289, 545, 641, 769, 22, 70, 518, 26, 74, 138, 338, 146, 530, 194, 642, 276, 532, 324, 580, 772, 152, 280, 104, 168, 296, 552, 328, 584, 392, 776, 400, 224, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_789, vertices_809, vertices_433, vertices_737, vertices_342, vertices_534, vertices_710, vertices_346, vertices_154, vertices_234, vertices_844, vertices_408, vertices_616, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_22, vertices_70, vertices_518, vertices_26, vertices_74, vertices_138, vertices_338, vertices_146, vertices_530, vertices_194, vertices_642, vertices_276, vertices_532, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_552, vertices_328, vertices_584, vertices_392, vertices_776, vertices_400, vertices_224, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_789), (false, vertices_809), (false, vertices_433), (false, vertices_737), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_26), (true, vertices_74), (true, vertices_138), (true, vertices_338), (true, vertices_194), (true, vertices_324), (true, vertices_580), (true, vertices_152), (true, vertices_280), (true, vertices_104), (true, vertices_168), (true, vertices_328), (true, vertices_584), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_338) then 18 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_584) then 14 else
  if p.val = (true, vertices_392) then 15 else
  0
cert_priority
cert_nodeAtPriority_64 22 70 518 26 74 138 194 324 580 152 280 104 168 328 584 392 659 338 789 809 433 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 7 338
cert_row_4 1 0 2 4 5 6 234 74 2
cert_row_4 2 0 1 5 6 8 710 70 3
cert_row_4 3 1 2 5 7 8 844 324 1
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 22 342 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 710
cert_cover_5 2 2 0 1 5 6 70 710 3
cert_coverFacet 3 346
cert_cover_5 3 0 0 2 3 5 26 346 3
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 234
cert_cover_5 5 1 0 2 4 5 74 234 2
cert_coverFacet 6 844
cert_cover_5 6 3 1 2 5 7 324 844 1
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 616
cert_cover_2 8 4 2 5 8 104 616 3
cert_coverFacet 9 424
cert_cover_2 9 4 2 6 7 168 424 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0798

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0799.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0799

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 781, 213, 405, 613, 713, 806, 666, 778, 370, 562, 402, 340, 356, 752, 149, 69, 261, 517, 137, 265, 521, 193, 577, 385, 138, 266, 522, 50, 146, 274, 530, 290, 546, 386, 770, 84, 276, 100, 292, 548, 324, 772, 648, 776, 112, 560, 208, 336, 400, 656, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_781, vertices_213, vertices_405, vertices_613, vertices_713, vertices_806, vertices_666, vertices_778, vertices_370, vertices_562, vertices_402, vertices_340, vertices_356, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_149, vertices_69, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_193, vertices_577, vertices_385, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_770, vertices_84, vertices_276, vertices_100, vertices_292, vertices_548, vertices_324, vertices_772, vertices_648, vertices_776, vertices_112, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_781), (false, vertices_213), (false, vertices_405), (false, vertices_613), (false, vertices_713), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_292), (true, vertices_324), (true, vertices_112), (true, vertices_560), (true, vertices_336), (true, vertices_656), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_213) then 21 else
  if p.val = (false, vertices_405) then 22 else
  if p.val = (false, vertices_613) then 23 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
cert_nodeAtPriority_42 522 1 50 2 146 274 530 290 546 770 292 324 112 560 336 656 352 395 781 713 213 405 613
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_4 1 0 2 3 6 8 666 138 2
cert_row_4 2 0 3 4 5 7 370 50 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 666
cert_cover_5 1 1 0 2 3 6 138 666 2
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 370
cert_cover_5 3 2 0 3 4 5 50 370 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 356
cert_cover_2 7 4 1 5 7 100 356 3
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 112 752 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0799

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0800.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0800

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 589, 213, 421, 773, 177, 849, 782, 618, 426, 626, 786, 204, 396, 248, 69, 133, 261, 517, 49, 81, 145, 273, 161, 289, 577, 769, 42, 266, 522, 50, 274, 530, 610, 290, 770, 76, 140, 268, 524, 196, 388, 772, 104, 168, 200, 584, 392, 112, 176, 208, 592, 784, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_589, vertices_213, vertices_421, vertices_773, vertices_177, vertices_849, vertices_782, vertices_618, vertices_426, vertices_626, vertices_786, vertices_204, vertices_396, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_517, vertices_49, vertices_81, vertices_145, vertices_273, vertices_161, vertices_289, vertices_577, vertices_769, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_610, vertices_290, vertices_770, vertices_76, vertices_140, vertices_268, vertices_524, vertices_196, vertices_388, vertices_772, vertices_104, vertices_168, vertices_200, vertices_584, vertices_392, vertices_112, vertices_176, vertices_208, vertices_592, vertices_784, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_589), (false, vertices_213), (false, vertices_421), (false, vertices_773), (false, vertices_177), (false, vertices_849), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_530), (true, vertices_610), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_104), (true, vertices_168), (true, vertices_200), (true, vertices_392), (true, vertices_112)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 15 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_177) then 1 else
  if p.val = (false, vertices_849) then 23 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_610) then 16 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_112) then 13 else
  0
cert_priority
cert_nodeAtPriority_15 0 773 1 177 42 266 522 530 770 140 268 104 168 200 392 112 307 610 589 213 421 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_2 1 0 4 5 8 610
cert_row_4 2 0 2 4 6 7 426 42 3
cert_row_4 3 2 3 4 5 6 248 104 1
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 618
cert_cover_5 1 1 0 2 4 5 42 618 3
cert_coverFacet 2 426
cert_cover_5 2 2 0 2 4 6 42 426 3
cert_coverFacet 3 626
cert_cover_5 3 1 0 3 4 5 50 626 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 204
cert_cover_2 5 2 1 5 6 76 204 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 248
cert_cover_5 7 3 2 3 4 5 104 248 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0800

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0801.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0801

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 213, 421, 837, 297, 777, 737, 598, 218, 538, 234, 610, 796, 404, 440, 69, 133, 261, 41, 265, 521, 161, 289, 545, 193, 577, 769, 26, 42, 202, 522, 82, 530, 98, 546, 578, 84, 148, 276, 532, 580, 388, 772, 152, 280, 536, 168, 296, 776, 208, 400, 224, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_213, vertices_421, vertices_837, vertices_297, vertices_777, vertices_737, vertices_598, vertices_218, vertices_538, vertices_234, vertices_610, vertices_796, vertices_404, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_41, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_769, vertices_26, vertices_42, vertices_202, vertices_522, vertices_82, vertices_530, vertices_98, vertices_546, vertices_578, vertices_84, vertices_148, vertices_276, vertices_532, vertices_580, vertices_388, vertices_772, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_776, vertices_208, vertices_400, vertices_224, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_213), (false, vertices_421), (false, vertices_837), (false, vertices_297), (false, vertices_777), (false, vertices_737), (true, vertices_26), (true, vertices_202), (true, vertices_82), (true, vertices_530), (true, vertices_98), (true, vertices_578), (true, vertices_276), (true, vertices_532), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 15 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_202) then 16 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
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
cert_row_4 0 2 3 4 6 7 440 152 2
cert_row_2 1 0 2 5 6 202
cert_row_4 2 0 1 3 5 8 598 82 1
cert_row_4 3 1 2 3 7 8 796 276 1
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 2 0 1 3 5 82 598 1
cert_coverFacet 1 218
cert_cover_5 1 1 0 2 3 5 26 218 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 234
cert_cover_5 3 1 0 2 4 5 42 234 3
cert_coverFacet 4 610
cert_cover_2 4 4 0 5 8 98 610 3
cert_coverFacet 5 796
cert_cover_5 5 3 1 2 3 7 276 796 1
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 440
cert_cover_5 7 0 2 3 4 6 152 440 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0801

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0802.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0802

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 173, 333, 549, 773, 217, 481, 790, 346, 722, 738, 354, 156, 284, 692, 13, 37, 261, 517, 73, 137, 161, 289, 545, 193, 321, 769, 82, 274, 530, 98, 290, 546, 706, 322, 770, 28, 140, 268, 148, 276, 532, 164, 548, 772, 88, 152, 280, 328, 208, 656, 224, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_173, vertices_333, vertices_549, vertices_773, vertices_217, vertices_481, vertices_790, vertices_346, vertices_722, vertices_738, vertices_354, vertices_156, vertices_284, vertices_692] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_261, vertices_517, vertices_73, vertices_137, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_769, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_706, vertices_322, vertices_770, vertices_28, vertices_140, vertices_268, vertices_148, vertices_276, vertices_532, vertices_164, vertices_548, vertices_772, vertices_88, vertices_152, vertices_280, vertices_328, vertices_208, vertices_656, vertices_224, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_173), (false, vertices_333), (false, vertices_549), (false, vertices_773), (false, vertices_217), (false, vertices_481), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_706), (true, vertices_322), (true, vertices_28), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_280), (true, vertices_656), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_173) then 18 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_773) then 1 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_706) then 16 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_53 0 549 1 773 82 274 530 98 322 28 148 276 532 280 656 672 803 706 173 333 217 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 7 346 82 1
cert_row_2 1 0 5 6 8 706
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 1 3 4 6 8 692 148 2
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 5 82 346 1
cert_coverFacet 2 722
cert_cover_5 2 1 0 3 5 6 82 722 3
cert_coverFacet 3 738
cert_cover_5 3 1 0 4 5 6 98 738 3
cert_coverFacet 4 354
cert_cover_2 4 4 0 5 7 98 354 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 692
cert_cover_5 7 3 1 3 4 6 148 692 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0802

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0803.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0803

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 77, 525, 789, 453, 433, 721, 558, 426, 458, 738, 316, 332, 564, 688, 13, 69, 261, 517, 73, 521, 145, 273, 529, 193, 577, 385, 42, 74, 394, 522, 162, 546, 194, 578, 44, 76, 268, 524, 52, 276, 532, 548, 324, 296, 328, 176, 304, 560, 656, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_77, vertices_525, vertices_789, vertices_453, vertices_433, vertices_721, vertices_558, vertices_426, vertices_458, vertices_738, vertices_316, vertices_332, vertices_564, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_517, vertices_73, vertices_521, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_42, vertices_74, vertices_394, vertices_522, vertices_162, vertices_546, vertices_194, vertices_578, vertices_44, vertices_76, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_548, vertices_324, vertices_296, vertices_328, vertices_176, vertices_304, vertices_560, vertices_656, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_77), (false, vertices_525), (false, vertices_789), (false, vertices_453), (false, vertices_433), (false, vertices_721), (true, vertices_42), (true, vertices_394), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_44), (true, vertices_268), (true, vertices_52), (true, vertices_548), (true, vertices_296), (true, vertices_328), (true, vertices_560), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_77) then 0 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_394) then 16 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_77), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 6 8 738 162 2
cert_row_2 1 0 2 6 7 394
cert_row_4 2 0 1 2 4 8 558 42 1
cert_row_4 3 1 2 3 4 7 316 44 2
cert_rows
cert_pivot_2 5 6 0 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 2 0 1 2 4 42 558 1
cert_coverFacet 1 426
cert_cover_5 1 1 0 2 4 6 42 426 3
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 6 74 458 3
cert_coverFacet 3 738
cert_cover_5 3 0 0 4 5 6 162 738 2
cert_coverFacet 4 316
cert_cover_5 4 3 1 2 3 4 44 316 2
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0803

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0804.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0804

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 787, 227, 387, 457, 369, 561, 398, 166, 774, 796, 716, 740, 632, 344, 35, 131, 259, 515, 49, 273, 529, 97, 545, 193, 321, 385, 38, 134, 262, 518, 162, 386, 770, 140, 268, 524, 164, 548, 708, 772, 88, 280, 536, 200, 328, 584, 392, 112, 560, 336, 784, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_787, vertices_227, vertices_387, vertices_457, vertices_369, vertices_561, vertices_398, vertices_166, vertices_774, vertices_796, vertices_716, vertices_740, vertices_632, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_49, vertices_273, vertices_529, vertices_97, vertices_545, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_262, vertices_518, vertices_162, vertices_386, vertices_770, vertices_140, vertices_268, vertices_524, vertices_164, vertices_548, vertices_708, vertices_772, vertices_88, vertices_280, vertices_536, vertices_200, vertices_328, vertices_584, vertices_392, vertices_112, vertices_560, vertices_336, vertices_784, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_787), (false, vertices_227), (false, vertices_387), (false, vertices_457), (false, vertices_369), (false, vertices_561), (true, vertices_134), (true, vertices_262), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_164), (true, vertices_708), (true, vertices_772), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_584), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 15 else
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_227) then 17 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_561) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_708) then 19 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
cert_nodeAtPriority_47 387 561 134 262 140 268 524 164 772 88 280 536 584 608 551 787 227 708 457 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_2 1 1 5 6 8 708
cert_row_4 2 1 2 3 7 8 796 268 2
cert_row_4 3 2 3 4 5 8 632 88 2
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 166
cert_cover_2 1 1 0 4 6 38 166 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 796
cert_cover_5 3 2 1 2 3 7 268 796 2
cert_coverFacet 4 716
cert_cover_5 4 1 1 2 5 6 140 716 2
cert_coverFacet 5 740
cert_cover_5 5 1 1 4 5 6 164 740 2
cert_coverFacet 6 632
cert_cover_5 6 3 2 3 4 5 88 632 2
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0804

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0805.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0805

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 285, 525, 805, 361, 713, 225, 406, 534, 422, 550, 722, 604, 344, 496, 13, 261, 517, 73, 265, 521, 97, 161, 289, 545, 193, 641, 22, 38, 390, 518, 146, 530, 162, 546, 642, 28, 524, 276, 532, 292, 548, 88, 280, 328, 584, 208, 336, 592, 400, 224, 352, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_285, vertices_525, vertices_805, vertices_361, vertices_713, vertices_225, vertices_406, vertices_534, vertices_422, vertices_550, vertices_722, vertices_604, vertices_344, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_641, vertices_22, vertices_38, vertices_390, vertices_518, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_28, vertices_524, vertices_276, vertices_532, vertices_292, vertices_548, vertices_88, vertices_280, vertices_328, vertices_584, vertices_208, vertices_336, vertices_592, vertices_400, vertices_224, vertices_352, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_285), (false, vertices_525), (false, vertices_805), (false, vertices_361), (false, vertices_713), (false, vertices_225), (true, vertices_22), (true, vertices_38), (true, vertices_390), (true, vertices_518), (true, vertices_146), (true, vertices_530), (true, vertices_532), (true, vertices_88), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_38) then 3 else
  if p.val = (true, vertices_390) then 16 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
cert_nodeAtPriority_25 0 525 1 225 22 38 518 146 530 532 88 208 336 592 400 416 675 390 285 805 361 713
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 5 8 604 28 3
cert_row_2 1 0 1 6 7 390
cert_row_4 2 0 3 5 6 8 722 146 2
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
cert_coverFacet 4 722
cert_cover_5 4 2 0 3 5 6 146 722 2
cert_coverFacet 5 604
cert_cover_5 5 0 1 2 3 5 28 604 3
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 208 496 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0805

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0806.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0806

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 557, 141, 53, 405, 369, 929, 590, 346, 410, 962, 92, 156, 628, 864, 13, 21, 37, 133, 137, 521, 49, 273, 289, 545, 385, 641, 282, 74, 138, 522, 322, 578, 386, 642, 28, 76, 140, 524, 52, 84, 148, 548, 580, 88, 152, 112, 336, 400, 352, 608, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_557, vertices_141, vertices_53, vertices_405, vertices_369, vertices_929, vertices_590, vertices_346, vertices_410, vertices_962, vertices_92, vertices_156, vertices_628, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_37, vertices_133, vertices_137, vertices_521, vertices_49, vertices_273, vertices_289, vertices_545, vertices_385, vertices_641, vertices_282, vertices_74, vertices_138, vertices_522, vertices_322, vertices_578, vertices_386, vertices_642, vertices_28, vertices_76, vertices_140, vertices_524, vertices_52, vertices_84, vertices_148, vertices_548, vertices_580, vertices_88, vertices_152, vertices_112, vertices_336, vertices_400, vertices_352, vertices_608, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_557), (false, vertices_141), (false, vertices_53), (false, vertices_405), (false, vertices_369), (false, vertices_929), (true, vertices_282), (true, vertices_74), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_28), (true, vertices_76), (true, vertices_84), (true, vertices_580), (true, vertices_88), (true, vertices_152), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_53) then 1 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (false, vertices_929) then 24 else
  if p.val = (true, vertices_282) then 16 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_53), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_282), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
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
cert_row_2 1 0 2 3 7 282
cert_row_4 2 0 1 2 5 8 590 74 1
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 6 7 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 2 0 1 2 5 74 590 1
cert_coverFacet 1 346
cert_cover_5 1 1 0 2 3 5 282 346 3
cert_coverFacet 2 410
cert_cover_5 2 1 0 2 3 6 282 410 3
cert_coverFacet 3 962
cert_cover_5 3 0 0 5 6 7 322 962 2
cert_coverFacet 4 92
cert_cover_2 4 2 1 3 5 28 92 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 628
cert_cover_5 6 3 1 3 4 5 52 628 3
cert_coverFacet 7 864
cert_cover_2 7 5 4 7 8 352 864 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0806

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0807.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0807

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 779, 355, 643, 345, 617, 673, 662, 294, 774, 796, 468, 484, 600, 752, 35, 131, 259, 515, 73, 265, 521, 97, 161, 545, 321, 641, 38, 134, 262, 518, 290, 642, 770, 148, 276, 532, 164, 292, 452, 772, 88, 280, 536, 584, 776, 208, 336, 592, 656, 224, 352, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_779, vertices_355, vertices_643, vertices_345, vertices_617, vertices_673, vertices_662, vertices_294, vertices_774, vertices_796, vertices_468, vertices_484, vertices_600, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_321, vertices_641, vertices_38, vertices_134, vertices_262, vertices_518, vertices_290, vertices_642, vertices_770, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_452, vertices_772, vertices_88, vertices_280, vertices_536, vertices_584, vertices_776, vertices_208, vertices_336, vertices_592, vertices_656, vertices_224, vertices_352, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_779), (false, vertices_355), (false, vertices_643), (false, vertices_345), (false, vertices_617), (false, vertices_673), (true, vertices_262), (true, vertices_518), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_452), (true, vertices_772), (true, vertices_536), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 15 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_355) then 17 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_673) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_452) then 19 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_224) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_167), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(true, vertices_452), by decide +kernel⟩
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
cert_row_4 0 0 1 3 6 8 662 134 2
cert_row_4 1 1 2 3 7 8 796 276 1
cert_row_2 2 1 5 6 7 452
cert_row_4 3 3 4 5 6 8 752 208 1
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 134 662 2
cert_coverFacet 1 294
cert_cover_2 1 1 0 4 7 38 294 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 796
cert_cover_5 3 1 1 2 3 7 276 796 1
cert_coverFacet 4 468
cert_cover_5 4 2 1 3 5 6 148 468 2
cert_coverFacet 5 484
cert_cover_5 5 2 1 4 5 6 164 484 2
cert_coverFacet 6 600
cert_cover_2 6 3 2 5 8 88 600 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 208 752 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0807

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0811.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0811

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 173, 333, 613, 425, 849, 678, 666, 466, 786, 418, 604, 652, 216, 456, 13, 37, 69, 169, 265, 289, 545, 321, 577, 769, 146, 274, 530, 162, 290, 546, 386, 642, 770, 76, 140, 524, 164, 548, 580, 644, 88, 152, 536, 200, 328, 392, 648, 208, 336, 592, 784, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_173, vertices_333, vertices_613, vertices_425, vertices_849, vertices_678, vertices_666, vertices_466, vertices_786, vertices_418, vertices_604, vertices_652, vertices_216, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_169, vertices_265, vertices_289, vertices_545, vertices_321, vertices_577, vertices_769, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_164, vertices_548, vertices_580, vertices_644, vertices_88, vertices_152, vertices_536, vertices_200, vertices_328, vertices_392, vertices_648, vertices_208, vertices_336, vertices_592, vertices_784, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_173), (false, vertices_333), (false, vertices_613), (false, vertices_425), (false, vertices_849), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_524), (true, vertices_644), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_200), (true, vertices_648), (true, vertices_208), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_173) then 21 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 146 1 274 2 530 162 386 642 524 644 88 152 536 200 648 208 448 803 333 613 173 425 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 162 1
cert_row_4 1 0 3 5 6 7 466 146 2
cert_row_4 2 0 2 3 6 8 666 146 1
cert_row_4 3 1 2 3 5 8 604 76 2
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 162 678 1
cert_coverFacet 1 666
cert_cover_5 1 2 0 2 3 6 146 666 1
cert_coverFacet 2 466
cert_cover_5 2 1 0 3 5 6 146 466 2
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 604
cert_cover_5 5 3 1 2 3 5 76 604 2
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0811

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3363 : Certifies 3363 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0778.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3364 : Certifies 3364 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0779.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3365 : Certifies 3365 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0780.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3366 : Certifies 3366 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0781.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3367 : Certifies 3367 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0782.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3368 : Certifies 3368 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0783.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3369 : Certifies 3369 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0784.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3370 : Certifies 3370 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0785.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3371 : Certifies 3371 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0786.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3372 : Certifies 3372 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0787.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3373 : Certifies 3373 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0788.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3374 : Certifies 3374 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0789.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3375 : Certifies 3375 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0790.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3376 : Certifies 3376 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0792.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3377 : Certifies 3377 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0793.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3378 : Certifies 3378 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0794.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3379 : Certifies 3379 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0795.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3380 : Certifies 3380 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0796.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3381 : Certifies 3381 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0797.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3382 : Certifies 3382 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0798.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3383 : Certifies 3383 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0799.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3384 : Certifies 3384 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0800.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3385 : Certifies 3385 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0801.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3386 : Certifies 3386 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0802.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3387 : Certifies 3387 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0803.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3388 : Certifies 3388 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0804.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3389 : Certifies 3389 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0805.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3390 : Certifies 3390 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0806.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3391 : Certifies 3391 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0807.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3392 : Certifies 3392 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0811.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B111 (j : Fin 30) :
    Certifies (3363 + j.val) := by
  fin_cases j
  · exact projection_3363
  · exact projection_3364
  · exact projection_3365
  · exact projection_3366
  · exact projection_3367
  · exact projection_3368
  · exact projection_3369
  · exact projection_3370
  · exact projection_3371
  · exact projection_3372
  · exact projection_3373
  · exact projection_3374
  · exact projection_3375
  · exact projection_3376
  · exact projection_3377
  · exact projection_3378
  · exact projection_3379
  · exact projection_3380
  · exact projection_3381
  · exact projection_3382
  · exact projection_3383
  · exact projection_3384
  · exact projection_3385
  · exact projection_3386
  · exact projection_3387
  · exact projection_3388
  · exact projection_3389
  · exact projection_3390
  · exact projection_3391
  · exact projection_3392

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
