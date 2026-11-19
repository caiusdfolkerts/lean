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
/- Source: ProjectionCertificates/R_m15e10q1_0843.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0843

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 405, 677, 57, 281, 809, 241, 334, 710, 122, 554, 778, 738, 452, 472, 133, 261, 517, 25, 41, 265, 49, 145, 273, 161, 545, 769, 70, 262, 518, 42, 74, 266, 522, 98, 546, 706, 770, 196, 324, 388, 644, 56, 88, 280, 552, 328, 776, 112, 208, 400, 224, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_405, vertices_677, vertices_57, vertices_281, vertices_809, vertices_241, vertices_334, vertices_710, vertices_122, vertices_554, vertices_778, vertices_738, vertices_452, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_41, vertices_265, vertices_49, vertices_145, vertices_273, vertices_161, vertices_545, vertices_769, vertices_70, vertices_262, vertices_518, vertices_42, vertices_74, vertices_266, vertices_522, vertices_98, vertices_546, vertices_706, vertices_770, vertices_196, vertices_324, vertices_388, vertices_644, vertices_56, vertices_88, vertices_280, vertices_552, vertices_328, vertices_776, vertices_112, vertices_208, vertices_400, vertices_224, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_405), (false, vertices_677), (false, vertices_57), (false, vertices_281), (false, vertices_809), (false, vertices_241), (true, vertices_70), (true, vertices_42), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_98), (true, vertices_546), (true, vertices_706), (true, vertices_196), (true, vertices_324), (true, vertices_88), (true, vertices_328), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_706) then 16 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 57 1 281 70 42 74 266 522 98 546 196 324 88 328 448 775 706 405 677 809 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 6 8 706
cert_row_4 1 0 1 2 5 7 334 70 2
cert_row_4 2 0 2 3 4 5 122 42 2
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 8 1 0 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 1 0 1 2 5 70 334 2
cert_coverFacet 1 710
cert_cover_5 1 0 0 1 5 6 70 710 3
cert_coverFacet 2 122
cert_cover_5 2 2 0 2 3 4 42 122 2
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 738
cert_cover_5 5 0 0 4 5 6 98 738 3
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 88 472 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0843

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0844.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0844

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 117, 357, 345, 665, 425, 561, 54, 534, 422, 838, 906, 562, 604, 840, 101, 25, 137, 265, 49, 81, 529, 161, 289, 545, 321, 641, 22, 38, 262, 518, 50, 530, 162, 546, 386, 642, 770, 52, 84, 532, 292, 324, 580, 88, 536, 328, 584, 392, 648, 776, 560, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_117, vertices_357, vertices_345, vertices_665, vertices_425, vertices_561, vertices_54, vertices_534, vertices_422, vertices_838, vertices_906, vertices_562, vertices_604, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_101, vertices_25, vertices_137, vertices_265, vertices_49, vertices_81, vertices_529, vertices_161, vertices_289, vertices_545, vertices_321, vertices_641, vertices_22, vertices_38, vertices_262, vertices_518, vertices_50, vertices_530, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_532, vertices_292, vertices_324, vertices_580, vertices_88, vertices_536, vertices_328, vertices_584, vertices_392, vertices_648, vertices_776, vertices_560, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_117), (false, vertices_357), (false, vertices_345), (false, vertices_665), (false, vertices_425), (false, vertices_561), (true, vertices_22), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_530), (true, vertices_386), (true, vertices_770), (true, vertices_532), (true, vertices_580), (true, vertices_584), (true, vertices_776), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_117) then 17 else
  if p.val = (false, vertices_357) then 18 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
cert_nodeAtPriority_48 0 561 2 22 1 38 262 518 50 530 386 770 532 580 584 776 832 675 117 357 345 665 425
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 7 422 38 3
cert_row_4 1 0 2 6 7 8 906 386 1
cert_row_4 2 0 1 5 7 8 838 262 2
cert_row_4 3 1 2 3 5 8 604 84 1
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 54
cert_cover_2 0 1 0 3 4 22 54 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 422
cert_cover_5 2 0 0 1 4 6 38 422 3
cert_coverFacet 3 838
cert_cover_5 3 2 0 1 5 7 262 838 2
cert_coverFacet 4 906
cert_cover_5 4 1 0 2 6 7 386 906 1
cert_coverFacet 5 562
cert_cover_2 5 3 0 4 8 50 562 3
cert_coverFacet 6 604
cert_cover_5 6 3 1 2 3 5 84 604 1
cert_coverFacet 7 840
cert_cover_2 7 5 2 7 8 328 840 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0844

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0845.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0845

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 589, 677, 453, 433, 833, 542, 314, 842, 178, 658, 674, 220, 660, 472, 69, 133, 517, 161, 289, 545, 321, 577, 385, 769, 26, 266, 522, 50, 146, 530, 162, 290, 546, 642, 770, 28, 76, 524, 148, 532, 196, 644, 216, 280, 328, 584, 176, 304, 400, 656, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_589, vertices_677, vertices_453, vertices_433, vertices_833, vertices_542, vertices_314, vertices_842, vertices_178, vertices_658, vertices_674, vertices_220, vertices_660, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_769, vertices_26, vertices_266, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_28, vertices_76, vertices_524, vertices_148, vertices_532, vertices_196, vertices_644, vertices_216, vertices_280, vertices_328, vertices_584, vertices_176, vertices_304, vertices_400, vertices_656, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_589), (false, vertices_677), (false, vertices_453), (false, vertices_433), (false, vertices_833), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_642), (true, vertices_28), (true, vertices_148), (true, vertices_532), (true, vertices_216), (true, vertices_280), (true, vertices_328), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_162) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_216) then 22 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
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
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 220
cert_cover_5 6 0 1 2 3 5 28 220 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 472
cert_cover_5 8 0 2 3 5 7 216 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0845

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0846.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0846

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 781, 677, 453, 849, 558, 122, 586, 178, 466, 674, 188, 412, 600, 792, 133, 261, 517, 193, 321, 577, 641, 769, 42, 74, 522, 50, 82, 146, 162, 546, 194, 578, 642, 156, 44, 268, 524, 164, 548, 388, 56, 88, 280, 536, 584, 776, 176, 336, 592, 400, 784, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_781, vertices_677, vertices_453, vertices_849, vertices_558, vertices_122, vertices_586, vertices_178, vertices_466, vertices_674, vertices_188, vertices_412, vertices_600, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_42, vertices_74, vertices_522, vertices_50, vertices_82, vertices_146, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_156, vertices_44, vertices_268, vertices_524, vertices_164, vertices_548, vertices_388, vertices_56, vertices_88, vertices_280, vertices_536, vertices_584, vertices_776, vertices_176, vertices_336, vertices_592, vertices_400, vertices_784, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_781), (false, vertices_677), (false, vertices_453), (false, vertices_849), (true, vertices_42), (true, vertices_74), (true, vertices_522), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_162), (true, vertices_546), (true, vertices_156), (true, vertices_44), (true, vertices_56), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_584), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 21 18 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_453) then 23 else
  if p.val = (false, vertices_849) then 25 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_156) then 20 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 42 1
cert_row_2 1 1 2 3 6 156
cert_row_4 2 0 2 3 4 5 122 42 2
cert_row_4 3 0 3 5 6 7 466 82 3
cert_rows
cert_pivot_2 8 1 2 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 42 558 1
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 4 42 122 2
cert_coverFacet 2 586
cert_cover_2 2 2 0 5 8 74 586 3
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 466
cert_cover_5 4 3 0 3 5 6 82 466 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 188
cert_cover_5 6 1 1 2 3 4 156 188 3
cert_coverFacet 7 412
cert_cover_5 7 1 1 2 3 7 156 412 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coverFacet 9 792
cert_cover_2 9 3 2 7 8 280 792 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0846

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0847.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0847

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 781, 617, 457, 369, 398, 182, 534, 774, 626, 418, 220, 604, 432, 464, 73, 265, 521, 97, 289, 545, 321, 769, 22, 134, 262, 518, 50, 530, 162, 290, 546, 386, 770, 92, 140, 268, 524, 148, 532, 772, 200, 584, 392, 112, 176, 304, 208, 336, 592, 400, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_781, vertices_617, vertices_457, vertices_369, vertices_398, vertices_182, vertices_534, vertices_774, vertices_626, vertices_418, vertices_220, vertices_604, vertices_432, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_97, vertices_289, vertices_545, vertices_321, vertices_769, vertices_22, vertices_134, vertices_262, vertices_518, vertices_50, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_92, vertices_140, vertices_268, vertices_524, vertices_148, vertices_532, vertices_772, vertices_200, vertices_584, vertices_392, vertices_112, vertices_176, vertices_304, vertices_208, vertices_336, vertices_592, vertices_400, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_781), (false, vertices_617), (false, vertices_457), (false, vertices_369), (true, vertices_22), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_530), (true, vertices_162), (true, vertices_386), (true, vertices_92), (true, vertices_140), (true, vertices_148), (true, vertices_532), (true, vertices_176), (true, vertices_208), (true, vertices_592), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_92) then 20 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_2 1 1 2 3 5 92
cert_row_4 2 0 1 3 4 6 182 22 3
cert_row_4 3 0 3 4 5 8 626 50 3
cert_rows
cert_pivot_2 7 2 1 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 182
cert_cover_5 1 2 0 1 3 4 22 182 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 626
cert_cover_5 4 3 0 3 4 5 50 626 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 220
cert_cover_5 6 1 1 2 3 6 92 220 3
cert_coverFacet 7 604
cert_cover_5 7 1 1 2 3 8 92 604 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0847

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0848.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0848

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 709, 665, 809, 457, 118, 598, 570, 354, 802, 316, 404, 660, 484, 408, 137, 265, 521, 193, 321, 577, 641, 769, 86, 50, 530, 98, 290, 546, 322, 578, 770, 52, 148, 276, 532, 100, 292, 196, 580, 388, 644, 56, 152, 280, 536, 296, 552, 392, 400, 656, 352, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_709, vertices_665, vertices_809, vertices_457, vertices_118, vertices_598, vertices_570, vertices_354, vertices_802, vertices_316, vertices_404, vertices_660, vertices_484, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_86, vertices_50, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_52, vertices_148, vertices_276, vertices_532, vertices_100, vertices_292, vertices_196, vertices_580, vertices_388, vertices_644, vertices_56, vertices_152, vertices_280, vertices_536, vertices_296, vertices_552, vertices_392, vertices_400, vertices_656, vertices_352, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_709), (false, vertices_665), (false, vertices_809), (false, vertices_457), (true, vertices_86), (true, vertices_50), (true, vertices_530), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_100), (true, vertices_292), (true, vertices_388), (true, vertices_56), (true, vertices_280), (true, vertices_400), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_809) then 23 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (true, vertices_86) then 18 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_352) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 50 1
cert_row_2 1 0 1 3 5 86
cert_row_4 2 1 2 3 4 7 316 52 1
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 8 0 2 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 1 0 1 3 4 86 118 3
cert_coverFacet 1 598
cert_cover_5 1 1 0 1 3 8 86 598 3
cert_coverFacet 2 570
cert_cover_5 2 0 0 2 3 4 50 570 1
cert_coverFacet 3 354
cert_cover_2 3 4 0 5 7 98 354 3
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 316
cert_cover_5 5 2 1 2 3 4 52 316 1
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 484
cert_cover_5 8 3 1 4 5 6 100 484 3
cert_coverFacet 9 408
cert_cover_2 9 3 2 6 7 152 408 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0848

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0849.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0849

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 805, 681, 849, 481, 94, 558, 598, 202, 650, 60, 436, 788, 184, 472, 161, 289, 545, 193, 321, 577, 641, 769, 14, 86, 518, 74, 138, 522, 194, 578, 642, 28, 44, 52, 276, 532, 292, 548, 772, 56, 88, 152, 168, 552, 200, 648, 176, 336, 592, 400, 784, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_805, vertices_681, vertices_849, vertices_481, vertices_94, vertices_558, vertices_598, vertices_202, vertices_650, vertices_60, vertices_436, vertices_788, vertices_184, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_14, vertices_86, vertices_518, vertices_74, vertices_138, vertices_522, vertices_194, vertices_578, vertices_642, vertices_28, vertices_44, vertices_52, vertices_276, vertices_532, vertices_292, vertices_548, vertices_772, vertices_56, vertices_88, vertices_152, vertices_168, vertices_552, vertices_200, vertices_648, vertices_176, vertices_336, vertices_592, vertices_400, vertices_784, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_805), (false, vertices_681), (false, vertices_849), (false, vertices_481), (true, vertices_14), (true, vertices_86), (true, vertices_518), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_28), (true, vertices_44), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_200), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_86) then 18 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
cert_nodeAtPriority_64 14 518 74 138 522 28 44 52 276 532 56 88 152 200 176 400 707 86 805 681 849 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 14 3
cert_row_2 1 0 1 3 5 86
cert_row_4 2 1 3 4 6 7 436 52 3
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 8 0 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 3 14 94 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 4 14 558 3
cert_coverFacet 2 598
cert_cover_5 2 1 0 1 3 8 86 598 3
cert_coverFacet 3 202
cert_cover_2 3 2 0 5 6 74 202 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 436
cert_cover_5 6 2 1 3 4 6 52 436 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 184
cert_cover_2 8 3 2 4 6 56 184 3
cert_coverFacet 9 472
cert_cover_5 9 3 2 3 5 6 88 472 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0849

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0850.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0850

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 677, 665, 433, 849, 110, 558, 602, 482, 834, 92, 156, 652, 468, 228, 145, 273, 529, 161, 289, 545, 641, 769, 46, 74, 522, 98, 290, 546, 322, 578, 770, 28, 76, 140, 524, 84, 148, 100, 164, 548, 196, 644, 88, 152, 536, 648, 336, 592, 400, 224, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_677, vertices_665, vertices_433, vertices_849, vertices_110, vertices_558, vertices_602, vertices_482, vertices_834, vertices_92, vertices_156, vertices_652, vertices_468, vertices_228] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_46, vertices_74, vertices_522, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_76, vertices_140, vertices_524, vertices_84, vertices_148, vertices_100, vertices_164, vertices_548, vertices_196, vertices_644, vertices_88, vertices_152, vertices_536, vertices_648, vertices_336, vertices_592, vertices_400, vertices_224, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_677), (false, vertices_665), (false, vertices_433), (false, vertices_849), (true, vertices_46), (true, vertices_74), (true, vertices_522), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_28), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_84), (true, vertices_148), (true, vertices_100), (true, vertices_196), (true, vertices_88), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_849) then 25 else
  if p.val = (true, vertices_46) then 18 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_196) then 12 else
  if p.val = (true, vertices_88) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
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
cert_row_2 1 0 1 2 4 46
cert_row_4 2 0 4 5 6 7 482 98 3
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 8 2 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 5 46 110 3
cert_coverFacet 1 558
cert_cover_5 1 1 0 1 2 8 46 558 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 5 74 602 2
cert_coverFacet 3 482
cert_cover_5 3 2 0 4 5 6 98 482 3
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 92
cert_cover_2 5 2 1 3 5 28 92 3
cert_coverFacet 6 156
cert_cover_2 6 2 1 3 6 28 156 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 468
cert_cover_5 8 3 1 3 5 6 84 468 3
cert_coverFacet 9 228
cert_cover_2 9 4 1 5 6 100 228 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0850

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0851.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0851

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 675, 195, 323, 565, 457, 433, 710, 842, 316, 604, 428, 204, 676, 792, 67, 131, 259, 515, 49, 273, 529, 161, 545, 193, 321, 385, 194, 322, 578, 642, 770, 28, 300, 76, 140, 52, 532, 164, 548, 196, 580, 644, 280, 536, 200, 328, 584, 392, 776, 304, 784, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_675, vertices_195, vertices_323, vertices_565, vertices_457, vertices_433, vertices_710, vertices_842, vertices_316, vertices_604, vertices_428, vertices_204, vertices_676, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_49, vertices_273, vertices_529, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_300, vertices_76, vertices_140, vertices_52, vertices_532, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_280, vertices_536, vertices_200, vertices_328, vertices_584, vertices_392, vertices_776, vertices_304, vertices_784, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_675), (false, vertices_195), (false, vertices_323), (false, vertices_565), (false, vertices_457), (false, vertices_433), (true, vertices_578), (true, vertices_28), (true, vertices_300), (true, vertices_76), (true, vertices_140), (true, vertices_164), (true, vertices_196), (true, vertices_580), (true, vertices_644), (true, vertices_280), (true, vertices_536), (true, vertices_584), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_323) then 1 else
  if p.val = (false, vertices_565) then 18 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_300) then 19 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_776) then 13 else
  0
cert_priority
cert_nodeAtPriority_44 195 323 578 28 76 140 164 196 580 644 280 536 584 776 787 675 565 300 457 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 7 300
cert_row_4 1 0 1 5 6 8 710 194 1
cert_row_4 2 0 2 5 7 8 842 322 1
cert_row_4 3 1 2 3 5 8 604 28 3
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 1 0 1 5 6 194 710 1
cert_coverFacet 1 842
cert_cover_5 1 2 0 2 5 7 322 842 1
cert_coverFacet 2 316
cert_cover_5 2 0 1 2 3 4 28 316 3
cert_coverFacet 3 604
cert_cover_5 3 3 1 2 3 5 28 604 3
cert_coverFacet 4 428
cert_cover_5 4 0 1 2 4 6 300 428 3
cert_coverFacet 5 204
cert_cover_2 5 2 1 5 6 76 204 3
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0851

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0852.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0852

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 355, 675, 421, 345, 409, 657, 806, 842, 188, 604, 396, 780, 564, 688, 35, 67, 515, 281, 81, 145, 529, 161, 289, 321, 385, 641, 290, 546, 322, 578, 770, 28, 140, 268, 524, 52, 532, 164, 292, 548, 388, 772, 88, 152, 328, 584, 392, 776, 176, 560, 592, 656, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_355, vertices_675, vertices_421, vertices_345, vertices_409, vertices_657, vertices_806, vertices_842, vertices_188, vertices_604, vertices_396, vertices_780, vertices_564, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_515, vertices_281, vertices_81, vertices_145, vertices_529, vertices_161, vertices_289, vertices_321, vertices_385, vertices_641, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_140, vertices_268, vertices_524, vertices_52, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_88, vertices_152, vertices_328, vertices_584, vertices_392, vertices_776, vertices_176, vertices_560, vertices_592, vertices_656, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_355), (false, vertices_675), (false, vertices_421), (false, vertices_345), (false, vertices_409), (false, vertices_657), (true, vertices_770), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_532), (true, vertices_548), (true, vertices_772), (true, vertices_584), (true, vertices_776), (true, vertices_176), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_355) then 16 else
  if p.val = (false, vertices_675) then 17 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_560) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 4 6 188 28 3
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 2 5 7 8 842 322 1
cert_row_4 3 1 2 3 5 8 604 28 3
cert_rows
cert_pivot_2 6 4 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 842
cert_cover_5 1 2 0 2 5 7 322 842 1
cert_coverFacet 2 188
cert_cover_5 2 0 1 2 3 4 28 188 3
cert_coverFacet 3 604
cert_cover_5 3 3 1 2 3 5 28 604 3
cert_coverFacet 4 396
cert_cover_2 4 2 1 6 7 140 396 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0852

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0853.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0853

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 789, 905, 465, 737, 62, 342, 358, 538, 682, 610, 540, 300, 780, 488, 81, 273, 529, 193, 577, 385, 641, 769, 22, 38, 326, 26, 42, 522, 82, 530, 98, 546, 578, 28, 44, 268, 524, 276, 532, 292, 772, 536, 168, 296, 392, 648, 776, 336, 224, 352, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_789, vertices_905, vertices_465, vertices_737, vertices_62, vertices_342, vertices_358, vertices_538, vertices_682, vertices_610, vertices_540, vertices_300, vertices_780, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_22, vertices_38, vertices_326, vertices_26, vertices_42, vertices_522, vertices_82, vertices_530, vertices_98, vertices_546, vertices_578, vertices_28, vertices_44, vertices_268, vertices_524, vertices_276, vertices_532, vertices_292, vertices_772, vertices_536, vertices_168, vertices_296, vertices_392, vertices_648, vertices_776, vertices_336, vertices_224, vertices_352, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_789), (false, vertices_905), (false, vertices_465), (false, vertices_737), (true, vertices_22), (true, vertices_38), (true, vertices_326), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_98), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_292), (true, vertices_536), (true, vertices_168), (true, vertices_296), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 17 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_905) then 22 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_326) then 18 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_296) then 14 else
  if p.val = (true, vertices_352) then 15 else
  0
cert_priority
cert_nodeAtPriority_64 22 38 26 42 522 98 546 28 44 268 524 292 536 168 296 352 595 326 789 905 465 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 4 62 22 2
cert_row_2 1 0 1 5 7 326
cert_row_4 2 0 2 4 6 8 682 42 3
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 22 62 2
cert_coverFacet 1 342
cert_cover_5 1 1 0 1 3 5 22 342 3
cert_coverFacet 2 358
cert_cover_5 2 1 0 1 4 5 38 358 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 682
cert_cover_5 4 2 0 2 4 6 42 682 3
cert_coverFacet 5 610
cert_cover_2 5 4 0 5 8 98 610 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 300
cert_cover_2 7 2 1 4 7 44 300 3
cert_coverFacet 8 780
cert_cover_2 8 2 1 7 8 268 780 3
cert_coverFacet 9 488
cert_cover_5 9 3 2 4 5 6 168 488 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0853

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0854.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0854

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 155, 539, 451, 781, 357, 393, 690, 706, 820, 740, 472, 792, 240, 368, 27, 67, 131, 515, 69, 261, 517, 137, 265, 521, 321, 385, 146, 530, 194, 578, 642, 100, 292, 548, 580, 772, 152, 280, 536, 392, 776, 112, 176, 304, 560, 208, 336, 784, 224, 352, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_155, vertices_539, vertices_451, vertices_781, vertices_357, vertices_393, vertices_690, vertices_706, vertices_820, vertices_740, vertices_472, vertices_792, vertices_240, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_67, vertices_131, vertices_515, vertices_69, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_321, vertices_385, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_100, vertices_292, vertices_548, vertices_580, vertices_772, vertices_152, vertices_280, vertices_536, vertices_392, vertices_776, vertices_112, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_784, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_155), (false, vertices_539), (false, vertices_451), (false, vertices_781), (false, vertices_357), (false, vertices_393), (true, vertices_642), (true, vertices_548), (true, vertices_280), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_208), (true, vertices_336), (true, vertices_784), (true, vertices_224), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 14 22 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 15 else
  if p.val = (false, vertices_155) then 19 else
  if p.val = (false, vertices_539) then 20 else
  if p.val = (false, vertices_451) then 21 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_112) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 8 690 146 2
cert_row_4 1 2 3 5 6 7 472 152 2
cert_row_4 2 1 3 4 7 8 820 292 1
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 690
cert_cover_5 0 0 0 3 4 6 146 690 2
cert_coverFacet 1 706
cert_cover_2 1 5 0 6 8 194 706 3
cert_coverFacet 2 820
cert_cover_5 2 2 1 3 4 7 292 820 1
cert_coverFacet 3 740
cert_cover_5 3 3 1 4 5 6 100 740 3
cert_coverFacet 4 472
cert_cover_5 4 1 2 3 5 6 152 472 2
cert_coverFacet 5 792
cert_cover_2 5 3 2 7 8 280 792 3
cert_coverFacet 6 240
cert_cover_2 6 4 3 5 6 112 240 3
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0854

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0855.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0855

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 333, 181, 597, 389, 121, 297, 454, 710, 842, 690, 802, 660, 824, 600, 21, 69, 133, 261, 41, 73, 265, 49, 81, 161, 289, 385, 198, 162, 290, 546, 322, 578, 386, 642, 770, 148, 532, 324, 580, 388, 644, 56, 88, 536, 296, 328, 584, 776, 176, 560, 592, 656, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_333, vertices_181, vertices_597, vertices_389, vertices_121, vertices_297, vertices_454, vertices_710, vertices_842, vertices_690, vertices_802, vertices_660, vertices_824, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_133, vertices_261, vertices_41, vertices_73, vertices_265, vertices_49, vertices_81, vertices_161, vertices_289, vertices_385, vertices_198, vertices_162, vertices_290, vertices_546, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_148, vertices_532, vertices_324, vertices_580, vertices_388, vertices_644, vertices_56, vertices_88, vertices_536, vertices_296, vertices_328, vertices_584, vertices_776, vertices_176, vertices_560, vertices_592, vertices_656, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_333), (false, vertices_181), (false, vertices_597), (false, vertices_389), (false, vertices_121), (false, vertices_297), (true, vertices_198), (true, vertices_546), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_644), (true, vertices_536), (true, vertices_584), (true, vertices_776), (true, vertices_560), (true, vertices_656), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 15 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_121) then 22 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (true, vertices_198) then 16 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 389 1 297 546 322 578 642 770 644 536 584 776 560 656 800 419 198 333 181 597 121
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_4 1 0 2 5 7 8 842 322 1
cert_row_4 2 0 3 4 6 8 690 162 1
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 1 5 0 2
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
cert_coverFacet 6 824
cert_cover_5 6 3 2 3 4 7 56 824 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0855

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0856.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0856

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 789, 617, 369, 721, 662, 390, 774, 682, 418, 220, 348, 428, 360, 712, 81, 273, 529, 97, 289, 545, 577, 769, 134, 262, 518, 162, 290, 546, 386, 642, 770, 92, 140, 268, 148, 276, 532, 388, 772, 104, 168, 296, 552, 200, 328, 584, 648, 208, 336, 656, 352, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_789, vertices_617, vertices_369, vertices_721, vertices_662, vertices_390, vertices_774, vertices_682, vertices_418, vertices_220, vertices_348, vertices_428, vertices_360, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_577, vertices_769, vertices_134, vertices_262, vertices_518, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_92, vertices_140, vertices_268, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_648, vertices_208, vertices_336, vertices_656, vertices_352, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_789), (false, vertices_617), (false, vertices_369), (false, vertices_721), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_92), (true, vertices_140), (true, vertices_268), (true, vertices_148), (true, vertices_388), (true, vertices_168), (true, vertices_296), (true, vertices_200), (true, vertices_328), (true, vertices_648), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 23 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_92) then 20 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 5 92
cert_row_4 1 0 1 3 6 8 662 134 2
cert_row_4 2 0 2 4 6 8 682 162 1
cert_row_4 3 1 2 4 6 7 428 140 2
cert_rows
cert_pivot_2 5 3 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 134 662 2
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 682
cert_cover_5 3 2 0 2 4 6 162 682 1
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 220
cert_cover_5 5 0 1 2 3 6 92 220 3
cert_coverFacet 6 348
cert_cover_5 6 0 1 2 3 7 92 348 3
cert_coverFacet 7 428
cert_cover_5 7 3 1 2 4 6 140 428 2
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coverFacet 9 712
cert_cover_2 9 5 2 6 8 200 712 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0856

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0857.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0857

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 837, 793, 681, 457, 614, 186, 410, 114, 338, 674, 450, 572, 372, 788, 137, 265, 521, 193, 321, 577, 641, 769, 154, 50, 82, 274, 98, 162, 546, 194, 322, 578, 386, 642, 52, 276, 532, 100, 548, 324, 580, 772, 56, 280, 536, 168, 552, 392, 112, 336, 784, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_837, vertices_793, vertices_681, vertices_457, vertices_614, vertices_186, vertices_410, vertices_114, vertices_338, vertices_674, vertices_450, vertices_572, vertices_372, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_154, vertices_50, vertices_82, vertices_274, vertices_98, vertices_162, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_52, vertices_276, vertices_532, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_56, vertices_280, vertices_536, vertices_168, vertices_552, vertices_392, vertices_112, vertices_336, vertices_784, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_837), (false, vertices_793), (false, vertices_681), (false, vertices_457), (true, vertices_154), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_322), (true, vertices_386), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_100), (true, vertices_548), (true, vertices_56), (true, vertices_112), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_793) then 22 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (true, vertices_154) then 18 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_548) then 12 else
  if p.val = (true, vertices_56) then 13 else
  if p.val = (true, vertices_112) then 14 else
  if p.val = (true, vertices_336) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 0 1 4 5 8 614 98 1
cert_row_4 2 1 2 3 4 8 572 52 1
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 6 0 2 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 1 0 1 4 5 98 614 1
cert_coverFacet 1 186
cert_cover_5 1 0 0 2 3 4 154 186 3
cert_coverFacet 2 410
cert_cover_5 2 0 0 2 3 7 154 410 3
cert_coverFacet 3 114
cert_cover_2 3 3 0 4 5 50 114 3
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 450
cert_cover_2 6 5 0 6 7 194 450 3
cert_coverFacet 7 572
cert_cover_5 7 2 1 2 3 4 52 572 1
cert_coverFacet 8 372
cert_cover_5 8 3 1 3 4 5 52 372 3
cert_coverFacet 9 788
cert_cover_2 9 3 1 7 8 276 788 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0857

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0858.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0858

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 397, 805, 709, 465, 353, 542, 122, 810, 722, 156, 780, 660, 376, 408, 133, 261, 517, 97, 289, 545, 193, 321, 577, 385, 26, 42, 522, 82, 530, 98, 546, 578, 28, 140, 268, 524, 148, 532, 644, 772, 120, 152, 280, 296, 392, 776, 208, 336, 400, 656, 352, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_397, vertices_805, vertices_709, vertices_465, vertices_353, vertices_542, vertices_122, vertices_810, vertices_722, vertices_156, vertices_780, vertices_660, vertices_376, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_26, vertices_42, vertices_522, vertices_82, vertices_530, vertices_98, vertices_546, vertices_578, vertices_28, vertices_140, vertices_268, vertices_524, vertices_148, vertices_532, vertices_644, vertices_772, vertices_120, vertices_152, vertices_280, vertices_296, vertices_392, vertices_776, vertices_208, vertices_336, vertices_400, vertices_656, vertices_352, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_397), (false, vertices_805), (false, vertices_709), (false, vertices_465), (false, vertices_353), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_82), (true, vertices_530), (true, vertices_28), (true, vertices_524), (true, vertices_148), (true, vertices_532), (true, vertices_120), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_776), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (false, vertices_353) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_120) then 22 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(true, vertices_120), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 26 1
cert_row_4 1 0 2 4 7 8 810 42 3
cert_row_2 2 2 3 4 5 120
cert_row_4 3 0 3 5 6 8 722 82 3
cert_rows
cert_pivot_2 1 7 2 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 26 542 1
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 4 26 122 3
cert_coverFacet 2 810
cert_cover_5 2 1 0 2 4 7 42 810 3
cert_coverFacet 3 722
cert_cover_5 3 3 0 3 5 6 82 722 3
cert_coverFacet 4 156
cert_cover_2 4 2 1 3 6 28 156 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 376
cert_cover_5 7 2 2 3 4 7 120 376 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0858

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0859.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0859

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 789, 681, 457, 777, 721, 54, 278, 230, 454, 626, 572, 428, 780, 736, 137, 265, 521, 81, 273, 529, 193, 321, 641, 769, 22, 38, 198, 262, 50, 82, 274, 98, 322, 44, 268, 524, 52, 276, 532, 164, 388, 772, 168, 552, 392, 776, 560, 592, 224, 608, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_789, vertices_681, vertices_457, vertices_777, vertices_721, vertices_54, vertices_278, vertices_230, vertices_454, vertices_626, vertices_572, vertices_428, vertices_780, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_81, vertices_273, vertices_529, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_38, vertices_198, vertices_262, vertices_50, vertices_82, vertices_274, vertices_98, vertices_322, vertices_44, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_164, vertices_388, vertices_772, vertices_168, vertices_552, vertices_392, vertices_776, vertices_560, vertices_592, vertices_224, vertices_608, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_789), (false, vertices_681), (false, vertices_457), (false, vertices_777), (false, vertices_721), (true, vertices_22), (true, vertices_38), (true, vertices_198), (true, vertices_262), (true, vertices_50), (true, vertices_98), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_164), (true, vertices_388), (true, vertices_560), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 16 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_198) then 17 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 777 22 38 262 50 98 44 268 524 52 164 388 560 224 608 339 198 789 681 457 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 6 7 428 44 3
cert_row_2 1 0 1 5 6 198
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 1 2 3 4 8 572 44 2
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 54
cert_cover_2 0 1 0 3 4 22 54 3
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 230
cert_cover_5 2 1 0 1 4 5 38 230 3
cert_coverFacet 3 454
cert_cover_5 3 1 0 1 5 7 198 454 3
cert_coverFacet 4 626
cert_cover_5 4 2 0 3 4 5 50 626 3
cert_coverFacet 5 572
cert_cover_5 5 3 1 2 3 4 44 572 2
cert_coverFacet 6 428
cert_cover_5 6 0 1 2 4 6 44 428 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 736
cert_cover_2 8 5 4 6 8 224 736 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0859

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0860.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0860

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [59, 339, 675, 771, 901, 113, 481, 782, 282, 554, 604, 284, 468, 740, 632, 19, 35, 259, 515, 49, 81, 97, 161, 321, 385, 641, 769, 26, 42, 266, 522, 274, 546, 770, 28, 268, 524, 84, 276, 196, 580, 388, 644, 772, 56, 600, 280, 552, 112, 336, 224, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_59, vertices_339, vertices_675, vertices_771, vertices_901, vertices_113, vertices_481, vertices_782, vertices_282, vertices_554, vertices_604, vertices_284, vertices_468, vertices_740, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_515, vertices_49, vertices_81, vertices_97, vertices_161, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_546, vertices_770, vertices_28, vertices_268, vertices_524, vertices_84, vertices_276, vertices_196, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_600, vertices_280, vertices_552, vertices_112, vertices_336, vertices_224, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_59), (false, vertices_339), (false, vertices_675), (false, vertices_771), (false, vertices_901), (false, vertices_113), (false, vertices_481), (true, vertices_266), (true, vertices_522), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_276), (true, vertices_196), (true, vertices_580), (true, vertices_600), (true, vertices_280), (true, vertices_552), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_59) then 15 else
  if p.val = (false, vertices_339) then 16 else
  if p.val = (false, vertices_675) then 17 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_113) then 1 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_600) then 21 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_600), by decide +kernel⟩
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
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_2 1 2 3 5 8 600
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 1 4 5 6 8 740 196 1
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 604
cert_cover_5 3 1 1 2 3 5 28 604 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 468
cert_cover_5 5 2 1 3 5 6 84 468 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 196 740 1
cert_coverFacet 7 632
cert_cover_5 7 1 2 3 4 5 56 632 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0860

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0861.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0861

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [79, 781, 229, 549, 425, 201, 817, 526, 118, 534, 714, 722, 564, 920, 496, 13, 37, 69, 517, 73, 137, 265, 161, 289, 545, 193, 769, 14, 22, 70, 518, 74, 522, 82, 530, 706, 524, 52, 532, 100, 548, 200, 392, 648, 776, 112, 304, 560, 208, 400, 656, 784, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_79, vertices_781, vertices_229, vertices_549, vertices_425, vertices_201, vertices_817, vertices_526, vertices_118, vertices_534, vertices_714, vertices_722, vertices_564, vertices_920, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_517, vertices_73, vertices_137, vertices_265, vertices_161, vertices_289, vertices_545, vertices_193, vertices_769, vertices_14, vertices_22, vertices_70, vertices_518, vertices_74, vertices_522, vertices_82, vertices_530, vertices_706, vertices_524, vertices_52, vertices_532, vertices_100, vertices_548, vertices_200, vertices_392, vertices_648, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_400, vertices_656, vertices_784, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_79), (false, vertices_781), (false, vertices_229), (false, vertices_549), (false, vertices_425), (false, vertices_201), (false, vertices_817), (true, vertices_22), (true, vertices_518), (true, vertices_522), (true, vertices_82), (true, vertices_530), (true, vertices_706), (true, vertices_52), (true, vertices_532), (true, vertices_648), (true, vertices_112), (true, vertices_208), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_79) then 15 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_706) then 16 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_656) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 549 1 201 22 518 522 82 530 52 532 648 112 208 400 656 79 706 781 229 425 817
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 5 118 22 3
cert_row_2 1 0 5 6 8 706
cert_row_4 2 2 3 6 7 8 920 392 1
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 118
cert_cover_5 1 0 0 1 3 4 22 118 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 714
cert_cover_5 3 1 0 2 5 6 74 714 3
cert_coverFacet 4 722
cert_cover_5 4 1 0 3 5 6 82 722 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 920
cert_cover_5 6 2 2 3 6 7 392 920 1
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0861

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0862.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0862

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 587, 451, 557, 269, 217, 409, 914, 738, 124, 284, 692, 788, 616, 240, 67, 259, 515, 13, 261, 517, 153, 73, 265, 521, 193, 385, 194, 578, 386, 642, 770, 28, 44, 268, 52, 276, 532, 548, 772, 88, 280, 104, 552, 584, 112, 176, 208, 400, 656, 784, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_587, vertices_451, vertices_557, vertices_269, vertices_217, vertices_409, vertices_914, vertices_738, vertices_124, vertices_284, vertices_692, vertices_788, vertices_616, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_13, vertices_261, vertices_517, vertices_153, vertices_73, vertices_265, vertices_521, vertices_193, vertices_385, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_52, vertices_276, vertices_532, vertices_548, vertices_772, vertices_88, vertices_280, vertices_104, vertices_552, vertices_584, vertices_112, vertices_176, vertices_208, vertices_400, vertices_656, vertices_784, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_587), (false, vertices_451), (false, vertices_557), (false, vertices_269), (false, vertices_217), (false, vertices_409), (true, vertices_642), (true, vertices_28), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_104), (true, vertices_112), (true, vertices_176), (true, vertices_656), (true, vertices_784), (true, vertices_224), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_587) then 16 else
  if p.val = (false, vertices_451) then 17 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_52) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 6 7 8 914 386 1
cert_row_4 1 0 4 5 6 8 738 194 1
cert_row_4 2 1 2 3 4 5 124 28 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 7 0 2 1
cert_heightProof 4
cert_coverFacet 0 914
cert_cover_5 0 0 0 3 6 7 386 914 1
cert_coverFacet 1 738
cert_cover_5 1 1 0 4 5 6 194 738 1
cert_coverFacet 2 124
cert_cover_5 2 2 1 2 3 4 28 124 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 692
cert_cover_5 4 3 1 3 4 6 52 692 3
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 616
cert_cover_2 6 4 2 5 8 104 616 3
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0862

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0863.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0863

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 677, 389, 57, 409, 809, 241, 334, 710, 122, 554, 778, 738, 468, 344, 133, 261, 517, 25, 41, 265, 49, 145, 161, 545, 385, 769, 70, 262, 518, 42, 74, 266, 522, 98, 546, 706, 770, 196, 324, 388, 644, 56, 88, 280, 552, 328, 776, 112, 208, 336, 400, 224, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_677, vertices_389, vertices_57, vertices_409, vertices_809, vertices_241, vertices_334, vertices_710, vertices_122, vertices_554, vertices_778, vertices_738, vertices_468, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_41, vertices_265, vertices_49, vertices_145, vertices_161, vertices_545, vertices_385, vertices_769, vertices_70, vertices_262, vertices_518, vertices_42, vertices_74, vertices_266, vertices_522, vertices_98, vertices_546, vertices_706, vertices_770, vertices_196, vertices_324, vertices_388, vertices_644, vertices_56, vertices_88, vertices_280, vertices_552, vertices_328, vertices_776, vertices_112, vertices_208, vertices_336, vertices_400, vertices_224, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_677), (false, vertices_389), (false, vertices_57), (false, vertices_409), (false, vertices_809), (false, vertices_241), (true, vertices_70), (true, vertices_42), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_98), (true, vertices_546), (true, vertices_706), (true, vertices_196), (true, vertices_324), (true, vertices_88), (true, vertices_328), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_57) then 1 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_706) then 16 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_336) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_57), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_706), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 6 8 706
cert_row_4 1 0 2 3 4 5 122 42 2
cert_row_4 2 0 1 2 5 7 334 70 2
cert_row_4 3 1 3 5 6 7 468 196 1
cert_rows
cert_pivot_2 8 4 0 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 2 0 1 2 5 70 334 2
cert_coverFacet 1 710
cert_cover_5 1 0 0 1 5 6 70 710 3
cert_coverFacet 2 122
cert_cover_5 2 1 0 2 3 4 42 122 2
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 738
cert_cover_5 5 0 0 4 5 6 98 738 3
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 196 468 1
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0863

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0865.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0865

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 653, 53, 405, 613, 393, 817, 710, 218, 346, 650, 866, 244, 408, 368, 21, 37, 133, 517, 137, 265, 521, 49, 273, 545, 385, 769, 90, 138, 266, 522, 194, 322, 578, 642, 770, 52, 148, 100, 196, 580, 644, 152, 280, 392, 648, 112, 304, 208, 336, 400, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_653, vertices_53, vertices_405, vertices_613, vertices_393, vertices_817, vertices_710, vertices_218, vertices_346, vertices_650, vertices_866, vertices_244, vertices_408, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_133, vertices_517, vertices_137, vertices_265, vertices_521, vertices_49, vertices_273, vertices_545, vertices_385, vertices_769, vertices_90, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_52, vertices_148, vertices_100, vertices_196, vertices_580, vertices_644, vertices_152, vertices_280, vertices_392, vertices_648, vertices_112, vertices_304, vertices_208, vertices_336, vertices_400, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_653), (false, vertices_53), (false, vertices_405), (false, vertices_613), (false, vertices_393), (false, vertices_817), (true, vertices_90), (true, vertices_138), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_196), (true, vertices_152), (true, vertices_280), (true, vertices_112), (true, vertices_208), (true, vertices_336), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_53) then 0 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_393) then 1 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (true, vertices_90) then 16 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
cert_nodeAtPriority_15 0 53 1 393 138 194 322 578 642 196 152 280 112 208 336 352 779 90 653 405 613 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 4 5 7 8 866 322 1
cert_row_4 2 0 1 5 6 8 710 194 1
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 2 0 1 5 6 194 710 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 6 90 218 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 7 90 346 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 866
cert_cover_5 4 1 0 4 5 7 322 866 1
cert_coverFacet 5 244
cert_cover_5 5 3 1 3 4 5 52 244 3
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0865

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0866.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0866

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [31, 519, 779, 597, 185, 393, 913, 302, 358, 582, 962, 60, 244, 488, 720, 7, 11, 515, 21, 517, 25, 137, 265, 145, 529, 385, 769, 14, 294, 70, 518, 266, 322, 578, 770, 28, 44, 52, 84, 100, 580, 56, 168, 296, 392, 176, 208, 592, 656, 224, 352, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_31, vertices_519, vertices_779, vertices_597, vertices_185, vertices_393, vertices_913, vertices_302, vertices_358, vertices_582, vertices_962, vertices_60, vertices_244, vertices_488, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_25, vertices_137, vertices_265, vertices_145, vertices_529, vertices_385, vertices_769, vertices_14, vertices_294, vertices_70, vertices_518, vertices_266, vertices_322, vertices_578, vertices_770, vertices_28, vertices_44, vertices_52, vertices_84, vertices_100, vertices_580, vertices_56, vertices_168, vertices_296, vertices_392, vertices_176, vertices_208, vertices_592, vertices_656, vertices_224, vertices_352, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_31), (false, vertices_519), (false, vertices_779), (false, vertices_597), (false, vertices_185), (false, vertices_393), (false, vertices_913), (true, vertices_294), (true, vertices_70), (true, vertices_322), (true, vertices_578), (true, vertices_44), (true, vertices_52), (true, vertices_100), (true, vertices_296), (true, vertices_208), (true, vertices_224), (true, vertices_352), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_31) then 15 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_393) then 1 else
  if p.val = (false, vertices_913) then 23 else
  if p.val = (true, vertices_294) then 17 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_448) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_23 519 393 70 322 578 44 52 100 296 208 224 352 448 704 31 779 294 597 185 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 322 2
cert_row_2 1 0 1 4 7 294
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 8 0 1 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 1 0 1 2 4 14 302 3
cert_coverFacet 1 358
cert_cover_5 1 1 0 1 4 5 294 358 3
cert_coverFacet 2 582
cert_cover_2 2 1 0 5 8 70 582 3
cert_coverFacet 3 962
cert_cover_5 3 0 0 5 6 7 322 962 2
cert_coverFacet 4 60
cert_cover_2 4 2 1 3 4 28 60 3
cert_coverFacet 5 244
cert_cover_5 5 2 1 3 4 5 52 244 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 168 488 2
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0866

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0867.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0867

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 779, 179, 675, 409, 713, 54, 614, 774, 460, 588, 780, 372, 752, 464, 19, 163, 259, 515, 137, 265, 521, 145, 273, 641, 22, 38, 262, 518, 50, 546, 770, 76, 268, 524, 52, 276, 100, 324, 580, 772, 200, 584, 392, 776, 112, 176, 208, 336, 400, 608, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_779, vertices_179, vertices_675, vertices_409, vertices_713, vertices_54, vertices_614, vertices_774, vertices_460, vertices_588, vertices_780, vertices_372, vertices_752, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_163, vertices_259, vertices_515, vertices_137, vertices_265, vertices_521, vertices_145, vertices_273, vertices_641, vertices_22, vertices_38, vertices_262, vertices_518, vertices_50, vertices_546, vertices_770, vertices_76, vertices_268, vertices_524, vertices_52, vertices_276, vertices_100, vertices_324, vertices_580, vertices_772, vertices_200, vertices_584, vertices_392, vertices_776, vertices_112, vertices_176, vertices_208, vertices_336, vertices_400, vertices_608, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_779), (false, vertices_179), (false, vertices_675), (false, vertices_409), (false, vertices_713), (true, vertices_38), (true, vertices_518), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_100), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_112), (true, vertices_208), (true, vertices_336), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 15 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 16 else
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_179) then 19 else
  if p.val = (false, vertices_675) then 20 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_713) then 23 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 1 38 0 518 2 76 268 524 52 100 324 580 772 112 208 336 608 448 279 779 179 675 409 713
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 8 614 38 3
cert_row_4 1 1 2 5 6 7 460 76 3
cert_row_4 2 1 3 4 5 7 372 52 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 54
cert_cover_2 0 1 0 3 4 22 54 3
cert_coverFacet 1 614
cert_cover_5 1 0 0 1 4 5 38 614 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 460
cert_cover_5 3 1 1 2 5 6 76 460 3
cert_coverFacet 4 588
cert_cover_2 4 2 1 5 8 76 588 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 372
cert_cover_5 6 2 1 3 4 5 52 372 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0867

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0868.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0868

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 557, 397, 165, 793, 721, 401, 230, 362, 810, 850, 706, 108, 332, 468, 13, 37, 133, 265, 521, 145, 273, 529, 161, 545, 385, 641, 298, 98, 162, 546, 194, 322, 578, 642, 770, 44, 76, 268, 100, 164, 196, 324, 388, 104, 552, 328, 776, 208, 336, 592, 400, 784, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_557, vertices_397, vertices_165, vertices_793, vertices_721, vertices_401, vertices_230, vertices_362, vertices_810, vertices_850, vertices_706, vertices_108, vertices_332, vertices_468] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_133, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_161, vertices_545, vertices_385, vertices_641, vertices_298, vertices_98, vertices_162, vertices_546, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_44, vertices_76, vertices_268, vertices_100, vertices_164, vertices_196, vertices_324, vertices_388, vertices_104, vertices_552, vertices_328, vertices_776, vertices_208, vertices_336, vertices_592, vertices_400, vertices_784, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_557), (false, vertices_397), (false, vertices_165), (false, vertices_793), (false, vertices_721), (false, vertices_401), (true, vertices_298), (true, vertices_98), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_76), (true, vertices_100), (true, vertices_196), (true, vertices_324), (true, vertices_104), (true, vertices_328), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (true, vertices_298) then 16 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_336) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 165 1 401 98 194 322 578 770 76 100 196 324 104 328 336 675 298 557 397 793 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 7 298
cert_row_4 1 0 1 4 5 6 230 98 1
cert_row_4 2 0 3 5 7 8 850 322 1
cert_row_4 3 1 3 5 6 7 468 196 1
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 1 0 1 4 5 98 230 1
cert_coverFacet 1 362
cert_cover_5 1 0 0 2 4 5 298 362 3
cert_coverFacet 2 810
cert_cover_5 2 0 0 2 4 8 298 810 3
cert_coverFacet 3 850
cert_cover_5 3 2 0 3 5 7 322 850 1
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 332
cert_cover_2 6 2 1 5 7 76 332 3
cert_coverFacet 7 468
cert_cover_5 7 3 1 3 5 6 196 468 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0868

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0869.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0869

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 653, 213, 789, 425, 777, 337, 614, 198, 646, 682, 370, 418, 628, 824, 21, 133, 517, 137, 265, 521, 81, 273, 193, 321, 385, 769, 70, 134, 518, 98, 162, 290, 546, 194, 322, 386, 642, 84, 532, 612, 196, 644, 168, 296, 552, 648, 776, 112, 304, 560, 336, 784, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_653, vertices_213, vertices_789, vertices_425, vertices_777, vertices_337, vertices_614, vertices_198, vertices_646, vertices_682, vertices_370, vertices_418, vertices_628, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_137, vertices_265, vertices_521, vertices_81, vertices_273, vertices_193, vertices_321, vertices_385, vertices_769, vertices_70, vertices_134, vertices_518, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_386, vertices_642, vertices_84, vertices_532, vertices_612, vertices_196, vertices_644, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_112, vertices_304, vertices_560, vertices_336, vertices_784, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_653), (false, vertices_213), (false, vertices_789), (false, vertices_425), (false, vertices_777), (false, vertices_337), (true, vertices_70), (true, vertices_134), (true, vertices_518), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_612), (true, vertices_552), (true, vertices_112), (true, vertices_304), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 19 16 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_337) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_642) then 9 else
  if p.val = (true, vertices_612) then 22 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_560) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 8 612
cert_row_4 1 0 2 4 6 8 682 162 1
cert_row_4 2 0 3 4 5 7 370 98 1
cert_row_4 3 2 3 4 7 8 824 296 1
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 0 0 1 4 5 70 614 2
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 682
cert_cover_5 3 1 0 2 4 6 162 682 1
cert_coverFacet 4 370
cert_cover_5 4 2 0 3 4 5 98 370 1
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 628
cert_cover_5 6 0 1 3 4 5 84 628 2
cert_coverFacet 7 824
cert_cover_5 7 3 2 3 4 7 296 824 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0869

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0870.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0870

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 661, 793, 361, 681, 417, 86, 790, 838, 210, 482, 620, 244, 676, 840, 41, 265, 521, 145, 273, 529, 161, 289, 385, 641, 22, 70, 774, 82, 146, 274, 194, 322, 386, 84, 148, 532, 100, 164, 548, 580, 644, 104, 552, 328, 584, 776, 208, 784, 224, 352, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_661, vertices_793, vertices_361, vertices_681, vertices_417, vertices_86, vertices_790, vertices_838, vertices_210, vertices_482, vertices_620, vertices_244, vertices_676, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_385, vertices_641, vertices_22, vertices_70, vertices_774, vertices_82, vertices_146, vertices_274, vertices_194, vertices_322, vertices_386, vertices_84, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_104, vertices_552, vertices_328, vertices_584, vertices_776, vertices_208, vertices_784, vertices_224, vertices_352, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_661), (false, vertices_793), (false, vertices_361), (false, vertices_681), (false, vertices_417), (true, vertices_22), (true, vertices_70), (true, vertices_774), (true, vertices_82), (true, vertices_194), (true, vertices_322), (true, vertices_84), (true, vertices_100), (true, vertices_164), (true, vertices_548), (true, vertices_580), (true, vertices_584), (true, vertices_208), (true, vertices_224), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_774) then 17 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_4 0 1 2 4 5 8 620 100 1
cert_row_2 1 0 1 7 8 774
cert_row_4 2 0 4 5 6 7 482 194 1
cert_row_4 3 1 3 4 5 6 244 84 2
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 790
cert_cover_5 1 1 0 1 3 7 22 790 3
cert_coverFacet 2 838
cert_cover_5 2 1 0 1 5 7 70 838 3
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 482
cert_cover_5 4 2 0 4 5 6 194 482 1
cert_coverFacet 5 620
cert_cover_5 5 0 1 2 4 5 100 620 1
cert_coverFacet 6 244
cert_cover_5 6 3 1 3 4 5 84 244 2
cert_coverFacet 7 676
cert_cover_2 7 4 1 6 8 164 676 3
cert_coverFacet 8 840
cert_cover_2 8 5 2 7 8 328 840 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0870

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0872.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0872

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 653, 269, 837, 345, 233, 609, 790, 666, 434, 866, 284, 540, 216, 496, 13, 261, 517, 73, 137, 265, 97, 161, 545, 321, 577, 641, 146, 274, 530, 162, 290, 546, 642, 770, 28, 268, 524, 276, 532, 772, 88, 152, 280, 536, 200, 648, 432, 208, 336, 224, 352, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_653, vertices_269, vertices_837, vertices_345, vertices_233, vertices_609, vertices_790, vertices_666, vertices_434, vertices_866, vertices_284, vertices_540, vertices_216, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_641, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_276, vertices_532, vertices_772, vertices_88, vertices_152, vertices_280, vertices_536, vertices_200, vertices_648, vertices_432, vertices_208, vertices_336, vertices_224, vertices_352, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_653), (false, vertices_269), (false, vertices_837), (false, vertices_345), (false, vertices_233), (false, vertices_609), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_770), (true, vertices_28), (true, vertices_276), (true, vertices_532), (true, vertices_152), (true, vertices_536), (true, vertices_432), (true, vertices_208), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_609) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_432) then 23 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_609), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_4 1 0 2 3 6 8 666 146 1
cert_row_2 2 3 4 6 7 432
cert_row_4 3 0 4 5 7 8 866 290 2
cert_rows
cert_pivot_2 1 2 3 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 666
cert_cover_5 1 1 0 2 3 6 146 666 1
cert_coverFacet 2 434
cert_cover_5 2 2 0 3 4 6 146 434 2
cert_coverFacet 3 866
cert_cover_5 3 3 0 4 5 7 290 866 2
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 496
cert_cover_5 7 2 3 4 5 6 432 496 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0872

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0873.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0873

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 709, 665, 809, 457, 614, 410, 242, 306, 802, 450, 572, 244, 660, 312, 137, 265, 521, 193, 321, 577, 641, 769, 50, 146, 274, 98, 290, 546, 194, 322, 578, 386, 770, 52, 148, 532, 100, 548, 196, 580, 644, 56, 152, 280, 536, 296, 552, 392, 240, 304, 656, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_709, vertices_665, vertices_809, vertices_457, vertices_614, vertices_410, vertices_242, vertices_306, vertices_802, vertices_450, vertices_572, vertices_244, vertices_660, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_50, vertices_146, vertices_274, vertices_98, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_52, vertices_148, vertices_532, vertices_100, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_152, vertices_280, vertices_536, vertices_296, vertices_552, vertices_392, vertices_240, vertices_304, vertices_656, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_709), (false, vertices_665), (false, vertices_809), (false, vertices_457), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_194), (true, vertices_386), (true, vertices_52), (true, vertices_148), (true, vertices_532), (true, vertices_100), (true, vertices_548), (true, vertices_56), (true, vertices_280), (true, vertices_240), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 20 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_548) then 12 else
  if p.val = (true, vertices_56) then 13 else
  if p.val = (true, vertices_280) then 14 else
  if p.val = (true, vertices_240) then 25 else
  if p.val = (true, vertices_304) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 146 1
cert_row_2 1 3 4 5 6 240
cert_row_4 2 0 1 4 5 8 614 98 1
cert_row_4 3 1 2 3 4 8 572 52 1
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 2 0 1 4 5 98 614 1
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 6 146 410 1
cert_coverFacet 2 242
cert_cover_5 2 1 0 3 4 5 50 242 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 572
cert_cover_5 6 3 1 2 3 4 52 572 1
cert_coverFacet 7 244
cert_cover_5 7 1 1 3 4 5 52 244 3
cert_coverFacet 8 660
cert_cover_2 8 3 1 6 8 148 660 3
cert_coverFacet 9 312
cert_cover_2 9 3 2 4 7 56 312 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0873

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0874.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0874

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 677, 809, 433, 849, 598, 230, 646, 346, 154, 234, 620, 408, 424, 840, 145, 273, 529, 161, 289, 545, 641, 769, 70, 134, 518, 26, 74, 138, 82, 146, 530, 226, 642, 100, 164, 548, 580, 644, 152, 280, 104, 168, 296, 552, 328, 584, 392, 776, 336, 592, 400, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_677, vertices_809, vertices_433, vertices_849, vertices_598, vertices_230, vertices_646, vertices_346, vertices_154, vertices_234, vertices_620, vertices_408, vertices_424, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_70, vertices_134, vertices_518, vertices_26, vertices_74, vertices_138, vertices_82, vertices_146, vertices_530, vertices_226, vertices_642, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_552, vertices_328, vertices_584, vertices_392, vertices_776, vertices_336, vertices_592, vertices_400, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_677), (false, vertices_809), (false, vertices_433), (false, vertices_849), (true, vertices_70), (true, vertices_134), (true, vertices_518), (true, vertices_26), (true, vertices_74), (true, vertices_138), (true, vertices_82), (true, vertices_226), (true, vertices_100), (true, vertices_580), (true, vertices_152), (true, vertices_280), (true, vertices_104), (true, vertices_168), (true, vertices_328), (true, vertices_584), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_849) then 25 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_82) then 6 else
  if p.val = (true, vertices_226) then 18 else
  if p.val = (true, vertices_100) then 7 else
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
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_226), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_2 0 0 4 5 6 226
cert_row_4 1 0 2 3 5 7 346 26 3
cert_row_4 2 0 1 3 5 8 598 70 2
cert_row_4 3 1 2 4 5 8 620 100 1
cert_rows
cert_pivot_2 6 7 0 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 2 0 1 3 5 70 598 2
cert_coverFacet 1 230
cert_cover_5 1 0 0 1 4 5 70 230 2
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 346
cert_cover_5 3 1 0 2 3 5 26 346 3
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 234
cert_cover_5 5 0 0 2 4 5 74 234 2
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 100 620 1
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coverFacet 9 840
cert_cover_2 9 5 2 7 8 328 840 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0874

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3423 : Certifies 3423 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0843.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3424 : Certifies 3424 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0844.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3425 : Certifies 3425 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0845.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3426 : Certifies 3426 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0846.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3427 : Certifies 3427 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0847.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3428 : Certifies 3428 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0848.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3429 : Certifies 3429 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0849.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3430 : Certifies 3430 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0850.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3431 : Certifies 3431 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0851.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3432 : Certifies 3432 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0852.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3433 : Certifies 3433 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0853.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3434 : Certifies 3434 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0854.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3435 : Certifies 3435 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0855.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3436 : Certifies 3436 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0856.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3437 : Certifies 3437 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0857.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3438 : Certifies 3438 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0858.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3439 : Certifies 3439 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0859.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3440 : Certifies 3440 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0860.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3441 : Certifies 3441 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0861.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3442 : Certifies 3442 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0862.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3443 : Certifies 3443 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0863.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3444 : Certifies 3444 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0865.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3445 : Certifies 3445 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0866.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3446 : Certifies 3446 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0867.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3447 : Certifies 3447 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0868.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3448 : Certifies 3448 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0869.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3449 : Certifies 3449 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0870.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3450 : Certifies 3450 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0872.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3451 : Certifies 3451 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0873.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3452 : Certifies 3452 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0874.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B113 (j : Fin 30) :
    Certifies (3423 + j.val) := by
  fin_cases j
  · exact projection_3423
  · exact projection_3424
  · exact projection_3425
  · exact projection_3426
  · exact projection_3427
  · exact projection_3428
  · exact projection_3429
  · exact projection_3430
  · exact projection_3431
  · exact projection_3432
  · exact projection_3433
  · exact projection_3434
  · exact projection_3435
  · exact projection_3436
  · exact projection_3437
  · exact projection_3438
  · exact projection_3439
  · exact projection_3440
  · exact projection_3441
  · exact projection_3442
  · exact projection_3443
  · exact projection_3444
  · exact projection_3445
  · exact projection_3446
  · exact projection_3447
  · exact projection_3448
  · exact projection_3449
  · exact projection_3450
  · exact projection_3451
  · exact projection_3452

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
