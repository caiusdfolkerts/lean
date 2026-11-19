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
/- Source: ProjectionCertificates/R_m15e10q1_0716.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0716

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 23, 659, 285, 457, 649, 433, 310, 358, 582, 626, 716, 332, 688, 992, 7, 19, 515, 13, 21, 137, 265, 521, 145, 273, 385, 641, 22, 294, 70, 518, 50, 530, 98, 578, 76, 268, 524, 276, 324, 580, 200, 328, 648, 176, 304, 560, 656, 352, 608, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_23, vertices_659, vertices_285, vertices_457, vertices_649, vertices_433, vertices_310, vertices_358, vertices_582, vertices_626, vertices_716, vertices_332, vertices_688, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_19, vertices_515, vertices_13, vertices_21, vertices_137, vertices_265, vertices_521, vertices_145, vertices_273, vertices_385, vertices_641, vertices_22, vertices_294, vertices_70, vertices_518, vertices_50, vertices_530, vertices_98, vertices_578, vertices_76, vertices_268, vertices_524, vertices_276, vertices_324, vertices_580, vertices_200, vertices_328, vertices_648, vertices_176, vertices_304, vertices_560, vertices_656, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_23), (false, vertices_659), (false, vertices_285), (false, vertices_457), (false, vertices_649), (false, vertices_433), (true, vertices_294), (true, vertices_70), (true, vertices_50), (true, vertices_98), (true, vertices_578), (true, vertices_76), (true, vertices_324), (true, vertices_580), (true, vertices_560), (true, vertices_352), (true, vertices_608), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 15 else
  if p.val = (false, vertices_23) then 0 else
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_285) then 19 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_649) then 1 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (true, vertices_294) then 17 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_23 23 649 70 50 98 578 76 324 580 560 352 608 672 704 527 659 294 285 457 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 8 626 50 3
cert_row_2 1 0 1 4 7 294
cert_row_4 2 1 2 5 6 8 716 76 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 3 0 1 4
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 1 0 1 3 4 22 310 3
cert_coverFacet 1 358
cert_cover_5 1 1 0 1 4 5 294 358 3
cert_coverFacet 2 582
cert_cover_2 2 1 0 5 8 70 582 3
cert_coverFacet 3 626
cert_cover_5 3 0 0 3 4 5 50 626 3
cert_coverFacet 4 716
cert_cover_5 4 2 1 2 5 6 76 716 3
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 688
cert_cover_2 6 4 3 6 8 176 688 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 352 992 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0716

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0717.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0717

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 563, 355, 387, 229, 549, 457, 794, 306, 898, 604, 204, 908, 628, 376, 35, 131, 259, 515, 37, 133, 517, 97, 545, 193, 321, 385, 50, 274, 530, 290, 386, 642, 770, 76, 140, 524, 596, 100, 548, 196, 644, 88, 280, 536, 200, 328, 392, 776, 112, 304, 560, 352, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_563, vertices_355, vertices_387, vertices_229, vertices_549, vertices_457, vertices_794, vertices_306, vertices_898, vertices_604, vertices_204, vertices_908, vertices_628, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_37, vertices_133, vertices_517, vertices_97, vertices_545, vertices_193, vertices_321, vertices_385, vertices_50, vertices_274, vertices_530, vertices_290, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_596, vertices_100, vertices_548, vertices_196, vertices_644, vertices_88, vertices_280, vertices_536, vertices_200, vertices_328, vertices_392, vertices_776, vertices_112, vertices_304, vertices_560, vertices_352, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_563), (false, vertices_355), (false, vertices_387), (false, vertices_229), (false, vertices_549), (false, vertices_457), (true, vertices_274), (true, vertices_770), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_596), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_776), (true, vertices_112), (true, vertices_304), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_355) then 17 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_549) then 1 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_596) then 20 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_549), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_4 0 0 2 3 7 8 794 274 1
cert_row_4 1 1 2 6 7 8 908 140 3
cert_row_2 2 1 3 5 8 596
cert_row_4 3 2 3 4 5 7 376 88 2
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 794
cert_cover_5 0 0 0 2 3 7 274 794 1
cert_coverFacet 1 306
cert_cover_2 1 3 0 4 7 50 306 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 604
cert_cover_5 3 2 1 2 3 5 76 604 2
cert_coverFacet 4 204
cert_cover_2 4 2 1 5 6 76 204 3
cert_coverFacet 5 908
cert_cover_5 5 1 1 2 6 7 140 908 3
cert_coverFacet 6 628
cert_cover_5 6 2 1 3 4 5 596 628 2
cert_coverFacet 7 376
cert_cover_5 7 3 2 3 4 5 88 376 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0717

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0718.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0718

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 23, 563, 285, 457, 649, 913, 310, 358, 582, 738, 716, 332, 496, 688, 7, 19, 515, 13, 21, 137, 265, 521, 273, 529, 385, 641, 22, 294, 70, 518, 50, 98, 546, 578, 76, 268, 524, 276, 324, 580, 200, 328, 648, 176, 304, 560, 400, 656, 224, 352, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_23, vertices_563, vertices_285, vertices_457, vertices_649, vertices_913, vertices_310, vertices_358, vertices_582, vertices_738, vertices_716, vertices_332, vertices_496, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_19, vertices_515, vertices_13, vertices_21, vertices_137, vertices_265, vertices_521, vertices_273, vertices_529, vertices_385, vertices_641, vertices_22, vertices_294, vertices_70, vertices_518, vertices_50, vertices_98, vertices_546, vertices_578, vertices_76, vertices_268, vertices_524, vertices_276, vertices_324, vertices_580, vertices_200, vertices_328, vertices_648, vertices_176, vertices_304, vertices_560, vertices_400, vertices_656, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_23), (false, vertices_563), (false, vertices_285), (false, vertices_457), (false, vertices_649), (false, vertices_913), (true, vertices_294), (true, vertices_70), (true, vertices_98), (true, vertices_578), (true, vertices_76), (true, vertices_324), (true, vertices_580), (true, vertices_176), (true, vertices_304), (true, vertices_224), (true, vertices_352), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 15 else
  if p.val = (false, vertices_23) then 0 else
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_285) then 19 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_649) then 1 else
  if p.val = (false, vertices_913) then 23 else
  if p.val = (true, vertices_294) then 17 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_23 23 649 70 98 578 76 324 580 176 304 224 352 672 704 527 563 294 285 457 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 5 6 8 716 76 3
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
cert_coverFacet 4 716
cert_cover_5 4 0 1 2 5 6 76 716 3
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 176 496 2
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0718

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0719.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0719

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 227, 547, 565, 457, 433, 337, 654, 678, 202, 842, 428, 780, 308, 852, 35, 67, 515, 49, 81, 273, 529, 161, 545, 193, 321, 385, 646, 74, 138, 522, 162, 546, 194, 578, 140, 268, 524, 52, 276, 532, 164, 292, 548, 772, 200, 328, 392, 776, 304, 336, 592, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_227, vertices_547, vertices_565, vertices_457, vertices_433, vertices_337, vertices_654, vertices_678, vertices_202, vertices_842, vertices_428, vertices_780, vertices_308, vertices_852] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_515, vertices_49, vertices_81, vertices_273, vertices_529, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_646, vertices_74, vertices_138, vertices_522, vertices_162, vertices_546, vertices_194, vertices_578, vertices_140, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_772, vertices_200, vertices_328, vertices_392, vertices_776, vertices_304, vertices_336, vertices_592, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_227), (false, vertices_547), (false, vertices_565), (false, vertices_457), (false, vertices_433), (false, vertices_337), (true, vertices_646), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_164), (true, vertices_292), (true, vertices_772), (true, vertices_776), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_227) then 16 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_337) then 1 else
  if p.val = (true, vertices_646) then 17 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
cert_nodeAtPriority_23 547 337 74 138 522 140 268 524 276 164 292 772 776 832 595 227 646 565 457 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 6 7 428 140 2
cert_row_2 1 0 1 6 8 646
cert_row_4 2 0 2 5 7 8 842 74 3
cert_row_4 3 1 3 5 7 8 852 276 2
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 646 654 2
cert_coverFacet 1 678
cert_cover_5 1 1 0 1 4 6 646 678 2
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 842
cert_cover_5 3 2 0 2 5 7 74 842 3
cert_coverFacet 4 428
cert_cover_5 4 0 1 2 4 6 140 428 2
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 852
cert_cover_5 7 3 1 3 5 7 276 852 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0719

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0720.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0720

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 115, 147, 803, 781, 665, 561, 342, 406, 354, 716, 396, 212, 868, 752, 19, 35, 131, 259, 137, 265, 521, 49, 145, 529, 545, 769, 278, 82, 146, 98, 290, 322, 386, 140, 268, 524, 84, 148, 196, 324, 580, 388, 772, 392, 648, 112, 560, 208, 656, 352, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_115, vertices_147, vertices_803, vertices_781, vertices_665, vertices_561, vertices_342, vertices_406, vertices_354, vertices_716, vertices_396, vertices_212, vertices_868, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_259, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_529, vertices_545, vertices_769, vertices_278, vertices_82, vertices_146, vertices_98, vertices_290, vertices_322, vertices_386, vertices_140, vertices_268, vertices_524, vertices_84, vertices_148, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_392, vertices_648, vertices_112, vertices_560, vertices_208, vertices_656, vertices_352, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_115), (false, vertices_147), (false, vertices_803), (false, vertices_781), (false, vertices_665), (false, vertices_561), (true, vertices_278), (true, vertices_322), (true, vertices_140), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_388), (true, vertices_208), (true, vertices_352), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_115) then 19 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_803) then 20 else
  if p.val = (false, vertices_781) then 15 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_561) then 1 else
  if p.val = (true, vertices_278) then 16 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 1 147 0 561 322 140 84 148 196 324 580 388 208 352 608 704 781 278 395 115 803 665
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 7 278
cert_row_4 1 1 2 5 6 8 716 140 2
cert_row_4 2 1 4 5 7 8 868 324 1
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 278 342 3
cert_coverFacet 1 406
cert_cover_5 1 0 0 1 3 6 278 406 3
cert_coverFacet 2 354
cert_cover_2 2 4 0 5 7 98 354 3
cert_coverFacet 3 716
cert_cover_5 3 1 1 2 5 6 140 716 2
cert_coverFacet 4 396
cert_cover_2 4 2 1 6 7 140 396 3
cert_coverFacet 5 212
cert_cover_2 5 3 1 5 6 84 212 3
cert_coverFacet 6 868
cert_cover_5 6 2 1 4 5 7 324 868 1
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0720

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0721.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0721

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [39, 519, 611, 301, 653, 409, 929, 542, 342, 358, 722, 284, 664, 496, 736, 7, 35, 515, 13, 37, 517, 137, 265, 289, 545, 385, 641, 22, 38, 326, 518, 82, 530, 98, 578, 28, 268, 524, 276, 292, 152, 280, 536, 648, 208, 336, 400, 656, 224, 352, 608, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_39, vertices_519, vertices_611, vertices_301, vertices_653, vertices_409, vertices_929, vertices_542, vertices_342, vertices_358, vertices_722, vertices_284, vertices_664, vertices_496, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_35, vertices_515, vertices_13, vertices_37, vertices_517, vertices_137, vertices_265, vertices_289, vertices_545, vertices_385, vertices_641, vertices_22, vertices_38, vertices_326, vertices_518, vertices_82, vertices_530, vertices_98, vertices_578, vertices_28, vertices_268, vertices_524, vertices_276, vertices_292, vertices_152, vertices_280, vertices_536, vertices_648, vertices_208, vertices_336, vertices_400, vertices_656, vertices_224, vertices_352, vertices_608, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_39), (false, vertices_519), (false, vertices_611), (false, vertices_301), (false, vertices_653), (false, vertices_409), (false, vertices_929), (true, vertices_22), (true, vertices_326), (true, vertices_82), (true, vertices_530), (true, vertices_28), (true, vertices_276), (true, vertices_536), (true, vertices_208), (true, vertices_336), (true, vertices_656), (true, vertices_224), (true, vertices_352), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_39) then 0 else
  if p.val = (false, vertices_519) then 1 else
  if p.val = (false, vertices_611) then 15 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_929) then 24 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_326) then 16 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_53 0 39 1 519 22 82 530 28 276 536 208 336 656 224 352 704 611 326 301 653 409 929
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 22 2
cert_row_2 1 0 1 5 7 326
cert_row_4 2 0 3 5 6 8 722 82 3
cert_row_4 3 3 4 5 6 7 496 208 1
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 22 542 2
cert_coverFacet 1 342
cert_cover_5 1 1 0 1 3 5 22 342 3
cert_coverFacet 2 358
cert_cover_5 2 1 0 1 4 5 38 358 3
cert_coverFacet 3 722
cert_cover_5 3 2 0 3 5 6 82 722 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 664
cert_cover_2 5 3 2 6 8 152 664 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 208 496 1
cert_coverFacet 7 736
cert_cover_2 7 5 4 6 8 224 736 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0721

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0723.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0723

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 285, 153, 233, 841, 721, 158, 174, 278, 358, 690, 802, 108, 332, 992, 25, 73, 137, 265, 145, 273, 529, 193, 577, 769, 142, 22, 38, 262, 146, 274, 530, 162, 290, 546, 770, 28, 44, 76, 268, 276, 100, 324, 152, 104, 168, 328, 656, 224, 352, 672, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_285, vertices_153, vertices_233, vertices_841, vertices_721, vertices_158, vertices_174, vertices_278, vertices_358, vertices_690, vertices_802, vertices_108, vertices_332, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_769, vertices_142, vertices_22, vertices_38, vertices_262, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_770, vertices_28, vertices_44, vertices_76, vertices_268, vertices_276, vertices_100, vertices_324, vertices_152, vertices_104, vertices_168, vertices_328, vertices_656, vertices_224, vertices_352, vertices_672, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_285), (false, vertices_153), (false, vertices_233), (false, vertices_841), (false, vertices_721), (true, vertices_142), (true, vertices_22), (true, vertices_38), (true, vertices_262), (true, vertices_146), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_44), (true, vertices_76), (true, vertices_100), (true, vertices_324), (true, vertices_352), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_285) then 19 else
  if p.val = (false, vertices_153) then 0 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_142) then 17 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 153 22 38 262 146 162 290 546 44 76 100 324 352 672 800 787 142 285 233 841 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 6 142
cert_row_4 1 0 1 4 5 7 358 38 3
cert_row_4 2 0 3 4 6 8 690 146 2
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 2 1 0 4
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 142 158 3
cert_coverFacet 1 174
cert_cover_5 1 0 0 1 2 4 142 174 3
cert_coverFacet 2 278
cert_cover_2 2 1 0 3 7 22 278 3
cert_coverFacet 3 358
cert_cover_5 3 1 0 1 4 5 38 358 3
cert_coverFacet 4 690
cert_cover_5 4 2 0 3 4 6 146 690 2
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 108
cert_cover_2 6 2 1 4 5 44 108 3
cert_coverFacet 7 332
cert_cover_2 7 2 1 5 7 76 332 3
cert_coverFacet 8 992
cert_cover_5 8 3 4 5 6 7 224 992 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0723

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0724.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0724

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [27, 107, 659, 547, 157, 713, 865, 286, 302, 818, 108, 204, 404, 484, 976, 11, 19, 35, 515, 25, 73, 137, 145, 97, 545, 577, 641, 270, 26, 42, 274, 530, 290, 546, 28, 44, 76, 140, 148, 276, 100, 292, 196, 388, 104, 200, 400, 656, 784, 352, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_27, vertices_107, vertices_659, vertices_547, vertices_157, vertices_713, vertices_865, vertices_286, vertices_302, vertices_818, vertices_108, vertices_204, vertices_404, vertices_484, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_35, vertices_515, vertices_25, vertices_73, vertices_137, vertices_145, vertices_97, vertices_545, vertices_577, vertices_641, vertices_270, vertices_26, vertices_42, vertices_274, vertices_530, vertices_290, vertices_546, vertices_28, vertices_44, vertices_76, vertices_140, vertices_148, vertices_276, vertices_100, vertices_292, vertices_196, vertices_388, vertices_104, vertices_200, vertices_400, vertices_656, vertices_784, vertices_352, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_27), (false, vertices_107), (false, vertices_659), (false, vertices_547), (false, vertices_157), (false, vertices_713), (false, vertices_865), (true, vertices_270), (true, vertices_274), (true, vertices_290), (true, vertices_44), (true, vertices_76), (true, vertices_276), (true, vertices_100), (true, vertices_292), (true, vertices_196), (true, vertices_388), (true, vertices_400), (true, vertices_784), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_27) then 0 else
  if p.val = (false, vertices_107) then 15 else
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_547) then 1 else
  if p.val = (false, vertices_157) then 19 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_865) then 24 else
  if p.val = (true, vertices_270) then 17 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_27), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_270), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 7 270
cert_row_4 1 0 3 4 7 8 818 274 2
cert_row_4 2 1 4 5 6 7 484 100 3
cert_row_4 3 3 5 6 7 8 976 400 1
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 270 286 3
cert_coverFacet 1 302
cert_cover_5 1 0 0 1 2 4 270 302 3
cert_coverFacet 2 818
cert_cover_5 2 1 0 3 4 7 274 818 2
cert_coverFacet 3 108
cert_cover_2 3 2 1 4 5 44 108 3
cert_coverFacet 4 204
cert_cover_2 4 2 1 5 6 76 204 3
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 484
cert_cover_5 6 2 1 4 5 6 100 484 3
cert_coverFacet 7 976
cert_cover_5 7 3 3 5 6 7 400 976 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0724

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0725.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0725

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 229, 793, 681, 393, 865, 94, 206, 282, 394, 370, 668, 116, 820, 676, 137, 265, 521, 97, 161, 545, 193, 321, 385, 769, 78, 26, 138, 266, 82, 274, 194, 322, 386, 28, 140, 52, 84, 532, 100, 164, 548, 196, 644, 280, 536, 392, 648, 112, 304, 784, 352, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_229, vertices_793, vertices_681, vertices_393, vertices_865, vertices_94, vertices_206, vertices_282, vertices_394, vertices_370, vertices_668, vertices_116, vertices_820, vertices_676] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_78, vertices_26, vertices_138, vertices_266, vertices_82, vertices_274, vertices_194, vertices_322, vertices_386, vertices_28, vertices_140, vertices_52, vertices_84, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_644, vertices_280, vertices_536, vertices_392, vertices_648, vertices_112, vertices_304, vertices_784, vertices_352, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_229), (false, vertices_793), (false, vertices_681), (false, vertices_393), (false, vertices_865), (true, vertices_78), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_82), (true, vertices_274), (true, vertices_28), (true, vertices_140), (true, vertices_52), (true, vertices_84), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_112), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_644) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_304) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 393 26 138 266 82 274 28 140 52 84 532 548 644 112 304 451 78 229 793 681 865
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 6 8 668 28 3
cert_row_2 1 0 1 2 5 78
cert_row_4 2 0 3 4 5 7 370 82 2
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 3 78 94 3
cert_coverFacet 1 206
cert_cover_5 1 1 0 1 2 6 78 206 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 370
cert_cover_5 4 2 0 3 4 5 82 370 2
cert_coverFacet 5 668
cert_cover_5 5 0 1 2 3 6 28 668 3
cert_coverFacet 6 116
cert_cover_2 6 3 1 4 5 52 116 3
cert_coverFacet 7 820
cert_cover_5 7 3 1 3 4 7 52 820 3
cert_coverFacet 8 676
cert_cover_2 8 4 1 6 8 164 676 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0725

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0726.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0726

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 229, 805, 645, 457, 369, 542, 346, 394, 650, 818, 188, 652, 564, 248, 37, 133, 517, 97, 289, 193, 321, 385, 641, 769, 26, 138, 266, 522, 274, 530, 386, 642, 770, 28, 140, 524, 52, 532, 164, 548, 644, 184, 88, 200, 328, 392, 648, 112, 304, 560, 336, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_229, vertices_805, vertices_645, vertices_457, vertices_369, vertices_542, vertices_346, vertices_394, vertices_650, vertices_818, vertices_188, vertices_652, vertices_564, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_97, vertices_289, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_28, vertices_140, vertices_524, vertices_52, vertices_532, vertices_164, vertices_548, vertices_644, vertices_184, vertices_88, vertices_200, vertices_328, vertices_392, vertices_648, vertices_112, vertices_304, vertices_560, vertices_336, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_229), (false, vertices_805), (false, vertices_645), (false, vertices_457), (false, vertices_369), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_28), (true, vertices_140), (true, vertices_524), (true, vertices_52), (true, vertices_532), (true, vertices_184), (true, vertices_88), (true, vertices_648), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_52) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_184) then 22 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_560) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_645), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_184), by decide +kernel⟩
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
cert_row_2 0 2 3 4 6 184
cert_row_4 1 0 1 2 3 8 542 26 1
cert_row_4 2 0 2 3 5 7 346 26 3
cert_row_4 3 0 3 4 7 8 818 274 2
cert_rows
cert_pivot_2 6 1 2 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 1 0 1 2 3 26 542 1
cert_coverFacet 1 346
cert_cover_5 1 2 0 2 3 5 26 346 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 818
cert_cover_5 4 3 0 3 4 7 274 818 2
cert_coverFacet 5 188
cert_cover_5 5 0 1 2 3 4 28 188 3
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 564
cert_cover_2 7 3 1 4 8 52 564 3
cert_coverFacet 8 248
cert_cover_5 8 0 2 3 4 5 184 248 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0726

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0727.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0727

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 837, 361, 681, 393, 625, 30, 398, 598, 774, 154, 690, 316, 372, 184, 41, 137, 265, 97, 545, 321, 577, 385, 641, 769, 14, 22, 262, 518, 26, 138, 146, 530, 386, 642, 770, 28, 268, 308, 84, 324, 580, 772, 56, 152, 168, 296, 392, 112, 176, 560, 592, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_837, vertices_361, vertices_681, vertices_393, vertices_625, vertices_30, vertices_398, vertices_598, vertices_774, vertices_154, vertices_690, vertices_316, vertices_372, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_265, vertices_97, vertices_545, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_518, vertices_26, vertices_138, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_308, vertices_84, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_168, vertices_296, vertices_392, vertices_112, vertices_176, vertices_560, vertices_592, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_837), (false, vertices_361), (false, vertices_681), (false, vertices_393), (false, vertices_625), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_268), (true, vertices_308), (true, vertices_84), (true, vertices_56), (true, vertices_152), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_138) then 6 else
  if p.val = (true, vertices_146) then 7 else
  if p.val = (true, vertices_530) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_308) then 19 else
  if p.val = (true, vertices_84) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_176) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 393 2 14 1 22 3 262 518 26 138 146 530 28 268 84 56 152 176 899 837 308 361 681 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_2 1 1 3 4 7 308
cert_row_4 2 0 1 3 5 8 598 22 3
cert_row_4 3 0 3 4 6 8 690 146 2
cert_rows
cert_pivot_2 2 7 1 0
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 398
cert_cover_5 1 0 0 1 2 6 14 398 3
cert_coverFacet 2 598
cert_cover_5 2 2 0 1 3 5 22 598 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 690
cert_cover_5 5 3 0 3 4 6 146 690 2
cert_coverFacet 6 316
cert_cover_5 6 1 1 2 3 4 28 316 3
cert_coverFacet 7 372
cert_cover_5 7 1 1 3 4 5 308 372 3
cert_coverFacet 8 184
cert_cover_2 8 3 2 4 6 56 184 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0727

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0728.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0728

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 647, 395, 115, 275, 313, 105, 713, 86, 406, 908, 628, 788, 872, 816, 519, 19, 67, 131, 259, 41, 73, 137, 265, 49, 273, 97, 577, 641, 22, 70, 134, 82, 274, 386, 84, 276, 532, 580, 388, 644, 772, 104, 296, 584, 392, 648, 776, 112, 304, 560, 784, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_647, vertices_395, vertices_115, vertices_275, vertices_313, vertices_105, vertices_713, vertices_86, vertices_406, vertices_908, vertices_628, vertices_788, vertices_872, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_519, vertices_19, vertices_67, vertices_131, vertices_259, vertices_41, vertices_73, vertices_137, vertices_265, vertices_49, vertices_273, vertices_97, vertices_577, vertices_641, vertices_22, vertices_70, vertices_134, vertices_82, vertices_274, vertices_386, vertices_84, vertices_276, vertices_532, vertices_580, vertices_388, vertices_644, vertices_772, vertices_104, vertices_296, vertices_584, vertices_392, vertices_648, vertices_776, vertices_112, vertices_304, vertices_560, vertices_784, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_647), (false, vertices_395), (false, vertices_115), (false, vertices_275), (false, vertices_313), (false, vertices_105), (false, vertices_713), (true, vertices_22), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_388), (true, vertices_772), (true, vertices_776), (true, vertices_560), (true, vertices_784), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 14 else
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_395) then 17 else
  if p.val = (false, vertices_115) then 18 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_313) then 20 else
  if p.val = (false, vertices_105) then 1 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_105), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
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
cert_row_4 0 0 1 3 6 7 406 22 3
cert_row_4 1 1 2 6 7 8 908 388 1
cert_row_4 2 1 3 4 5 8 628 84 2
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 406
cert_cover_5 1 0 0 1 3 6 22 406 3
cert_coverFacet 2 908
cert_cover_5 2 1 1 2 6 7 388 908 1
cert_coverFacet 3 628
cert_cover_5 3 2 1 3 4 5 84 628 2
cert_coverFacet 4 788
cert_cover_2 4 3 1 7 8 276 788 3
cert_coverFacet 5 872
cert_cover_5 5 3 2 4 5 7 104 872 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0728

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0729.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0729

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 357, 709, 773, 425, 241, 782, 186, 538, 394, 722, 348, 604, 312, 368, 69, 261, 517, 97, 161, 289, 193, 385, 641, 769, 26, 138, 266, 522, 146, 530, 386, 642, 770, 92, 268, 524, 324, 580, 772, 56, 280, 536, 168, 296, 392, 112, 176, 304, 208, 336, 592, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_357, vertices_709, vertices_773, vertices_425, vertices_241, vertices_782, vertices_186, vertices_538, vertices_394, vertices_722, vertices_348, vertices_604, vertices_312, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_193, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_92, vertices_268, vertices_524, vertices_324, vertices_580, vertices_772, vertices_56, vertices_280, vertices_536, vertices_168, vertices_296, vertices_392, vertices_112, vertices_176, vertices_304, vertices_208, vertices_336, vertices_592, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_357), (false, vertices_709), (false, vertices_773), (false, vertices_425), (false, vertices_241), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_92), (true, vertices_268), (true, vertices_524), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_304), (true, vertices_336), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_92) then 19 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 773 1 26 2 138 3 266 522 146 530 268 524 56 280 536 304 336 592 899 425 92 357 709 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_2 1 1 2 3 5 92
cert_row_4 2 0 2 3 4 6 186 26 3
cert_row_4 3 0 3 5 6 8 722 146 2
cert_rows
cert_pivot_2 7 1 2 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 186
cert_cover_5 1 2 0 2 3 4 26 186 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 722
cert_cover_5 4 3 0 3 5 6 146 722 2
cert_coverFacet 5 348
cert_cover_5 5 1 1 2 3 7 92 348 3
cert_coverFacet 6 604
cert_cover_5 6 1 1 2 3 8 92 604 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0729

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0730.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0730

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 229, 805, 645, 457, 369, 654, 346, 538, 394, 818, 188, 540, 564, 248, 37, 133, 517, 97, 289, 193, 321, 385, 641, 769, 26, 138, 266, 522, 274, 530, 386, 642, 770, 28, 140, 524, 52, 532, 164, 548, 644, 184, 88, 536, 200, 328, 392, 112, 304, 560, 336, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_229, vertices_805, vertices_645, vertices_457, vertices_369, vertices_654, vertices_346, vertices_538, vertices_394, vertices_818, vertices_188, vertices_540, vertices_564, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_97, vertices_289, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_28, vertices_140, vertices_524, vertices_52, vertices_532, vertices_164, vertices_548, vertices_644, vertices_184, vertices_88, vertices_536, vertices_200, vertices_328, vertices_392, vertices_112, vertices_304, vertices_560, vertices_336, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_229), (false, vertices_805), (false, vertices_645), (false, vertices_457), (false, vertices_369), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_28), (true, vertices_140), (true, vertices_524), (true, vertices_52), (true, vertices_532), (true, vertices_184), (true, vertices_88), (true, vertices_536), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_52) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_184) then 22 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_560) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_645), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_184), by decide +kernel⟩
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
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_2 1 2 3 4 6 184
cert_row_4 2 0 2 3 5 7 346 26 3
cert_row_4 3 0 3 4 7 8 818 274 2
cert_rows
cert_pivot_2 1 6 2 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 346
cert_cover_5 1 2 0 2 3 5 26 346 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 818
cert_cover_5 4 3 0 3 4 7 274 818 2
cert_coverFacet 5 188
cert_cover_5 5 1 1 2 3 4 28 188 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 564
cert_cover_2 7 3 1 4 8 52 564 3
cert_coverFacet 8 248
cert_cover_5 8 1 2 3 4 5 184 248 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0730

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0731.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0731

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 709, 233, 809, 393, 625, 286, 142, 598, 646, 394, 818, 188, 244, 312, 41, 137, 265, 97, 545, 193, 577, 385, 641, 769, 14, 22, 134, 518, 138, 266, 274, 530, 386, 642, 770, 28, 140, 180, 84, 196, 580, 644, 56, 280, 168, 296, 392, 112, 304, 560, 592, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_709, vertices_233, vertices_809, vertices_393, vertices_625, vertices_286, vertices_142, vertices_598, vertices_646, vertices_394, vertices_818, vertices_188, vertices_244, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_265, vertices_97, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_134, vertices_518, vertices_138, vertices_266, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_28, vertices_140, vertices_180, vertices_84, vertices_196, vertices_580, vertices_644, vertices_56, vertices_280, vertices_168, vertices_296, vertices_392, vertices_112, vertices_304, vertices_560, vertices_592, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_709), (false, vertices_233), (false, vertices_809), (false, vertices_393), (false, vertices_625), (true, vertices_14), (true, vertices_22), (true, vertices_134), (true, vertices_518), (true, vertices_138), (true, vertices_266), (true, vertices_274), (true, vertices_530), (true, vertices_28), (true, vertices_140), (true, vertices_180), (true, vertices_84), (true, vertices_56), (true, vertices_280), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_274) then 7 else
  if p.val = (true, vertices_530) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_180) then 19 else
  if p.val = (true, vertices_84) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_304) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 393 2 14 1 22 3 134 518 138 266 274 530 28 140 84 56 280 304 899 709 180 233 809 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 4 6 180
cert_row_4 1 0 1 2 3 7 286 14 3
cert_row_4 2 0 1 3 5 8 598 22 3
cert_row_4 3 0 3 4 7 8 818 274 2
cert_rows
cert_pivot_2 6 2 1 0
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 1 0 1 2 3 14 286 3
cert_coverFacet 1 142
cert_cover_2 1 1 0 2 6 14 142 3
cert_coverFacet 2 598
cert_cover_5 2 2 0 1 3 5 22 598 3
cert_coverFacet 3 646
cert_cover_2 3 1 0 6 8 134 646 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 818
cert_cover_5 5 3 0 3 4 7 274 818 2
cert_coverFacet 6 188
cert_cover_5 6 0 1 2 3 4 28 188 3
cert_coverFacet 7 244
cert_cover_5 7 0 1 3 4 5 180 244 3
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0731

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0732.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0732

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [39, 583, 563, 333, 309, 465, 593, 398, 526, 422, 682, 588, 968, 752, 432, 7, 35, 515, 37, 69, 261, 49, 81, 273, 529, 321, 577, 14, 38, 390, 518, 138, 522, 162, 546, 76, 268, 524, 292, 580, 328, 584, 392, 648, 176, 304, 560, 208, 592, 400, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_39, vertices_583, vertices_563, vertices_333, vertices_309, vertices_465, vertices_593, vertices_398, vertices_526, vertices_422, vertices_682, vertices_588, vertices_968, vertices_752, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_35, vertices_515, vertices_37, vertices_69, vertices_261, vertices_49, vertices_81, vertices_273, vertices_529, vertices_321, vertices_577, vertices_14, vertices_38, vertices_390, vertices_518, vertices_138, vertices_522, vertices_162, vertices_546, vertices_76, vertices_268, vertices_524, vertices_292, vertices_580, vertices_328, vertices_584, vertices_392, vertices_648, vertices_176, vertices_304, vertices_560, vertices_208, vertices_592, vertices_400, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_39), (false, vertices_583), (false, vertices_563), (false, vertices_333), (false, vertices_309), (false, vertices_465), (false, vertices_593), (true, vertices_14), (true, vertices_390), (true, vertices_138), (true, vertices_522), (true, vertices_162), (true, vertices_524), (true, vertices_584), (true, vertices_392), (true, vertices_648), (true, vertices_176), (true, vertices_416), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_39) then 0 else
  if p.val = (false, vertices_583) then 15 else
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_309) then 20 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (false, vertices_593) then 1 else
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
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_39), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
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
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
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
cert_row_2 0 0 1 6 7 390
cert_row_4 1 0 2 4 6 8 682 138 2
cert_row_4 2 2 5 6 7 8 968 328 2
cert_row_4 3 3 4 5 6 8 752 176 2
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
cert_coverFacet 6 752
cert_cover_5 6 3 3 4 5 6 176 752 2
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0732

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0733.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0733

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 61, 525, 533, 425, 689, 961, 46, 526, 118, 838, 234, 458, 724, 240, 13, 21, 517, 41, 265, 521, 49, 529, 161, 385, 641, 769, 14, 38, 70, 518, 42, 202, 266, 522, 98, 322, 770, 44, 524, 52, 84, 532, 580, 168, 392, 112, 176, 208, 656, 224, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_61, vertices_525, vertices_533, vertices_425, vertices_689, vertices_961, vertices_46, vertices_526, vertices_118, vertices_838, vertices_234, vertices_458, vertices_724, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_517, vertices_41, vertices_265, vertices_521, vertices_49, vertices_529, vertices_161, vertices_385, vertices_641, vertices_769, vertices_14, vertices_38, vertices_70, vertices_518, vertices_42, vertices_202, vertices_266, vertices_522, vertices_98, vertices_322, vertices_770, vertices_44, vertices_524, vertices_52, vertices_84, vertices_532, vertices_580, vertices_168, vertices_392, vertices_112, vertices_176, vertices_208, vertices_656, vertices_224, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_61), (false, vertices_525), (false, vertices_533), (false, vertices_425), (false, vertices_689), (false, vertices_961), (true, vertices_14), (true, vertices_38), (true, vertices_70), (true, vertices_518), (true, vertices_42), (true, vertices_202), (true, vertices_98), (true, vertices_322), (true, vertices_84), (true, vertices_580), (true, vertices_112), (true, vertices_208), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 21 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_61) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_689) then 22 else
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
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_224) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
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
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
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
cert_row_4 1 0 1 3 4 5 118 38 2
cert_row_4 2 0 1 5 7 8 838 70 3
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 46
cert_cover_2 0 1 0 2 4 14 46 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 118
cert_cover_5 2 1 0 1 3 4 38 118 2
cert_coverFacet 3 838
cert_cover_5 3 2 0 1 5 7 70 838 3
cert_coverFacet 4 234
cert_cover_5 4 0 0 2 4 5 42 234 3
cert_coverFacet 5 458
cert_cover_5 5 0 0 2 5 7 202 458 3
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 84 724 3
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0733

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0734.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0734

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 213, 325, 901, 601, 689, 110, 358, 570, 586, 930, 428, 204, 184, 216, 69, 133, 261, 81, 145, 529, 321, 577, 641, 769, 102, 42, 74, 522, 290, 546, 322, 578, 770, 44, 76, 140, 292, 196, 324, 388, 56, 88, 152, 536, 168, 200, 584, 176, 560, 208, 416, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_213, vertices_325, vertices_901, vertices_601, vertices_689, vertices_110, vertices_358, vertices_570, vertices_586, vertices_930, vertices_428, vertices_204, vertices_184, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_81, vertices_145, vertices_529, vertices_321, vertices_577, vertices_641, vertices_769, vertices_102, vertices_42, vertices_74, vertices_522, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_44, vertices_76, vertices_140, vertices_292, vertices_196, vertices_324, vertices_388, vertices_56, vertices_88, vertices_152, vertices_536, vertices_168, vertices_200, vertices_584, vertices_176, vertices_560, vertices_208, vertices_416, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_213), (false, vertices_325), (false, vertices_901), (false, vertices_601), (false, vertices_689), (true, vertices_102), (true, vertices_42), (true, vertices_74), (true, vertices_522), (true, vertices_290), (true, vertices_546), (true, vertices_44), (true, vertices_76), (true, vertices_140), (true, vertices_292), (true, vertices_56), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_901) then 20 else
  if p.val = (false, vertices_601) then 22 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (true, vertices_102) then 17 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 325 42 74 522 290 546 44 76 140 292 56 152 168 200 416 835 102 213 901 601 689
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 5 102
cert_row_4 1 0 2 3 4 8 570 42 2
cert_row_4 2 0 4 6 7 8 930 290 2
cert_row_4 3 1 2 4 6 7 428 44 3
cert_rows
cert_pivot_2 5 3 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 4 102 110 2
cert_coverFacet 1 358
cert_cover_5 1 0 0 1 4 7 102 358 3
cert_coverFacet 2 570
cert_cover_5 2 1 0 2 3 4 42 570 2
cert_coverFacet 3 586
cert_cover_2 3 2 0 5 8 74 586 3
cert_coverFacet 4 930
cert_cover_5 4 2 0 4 6 7 290 930 2
cert_coverFacet 5 428
cert_cover_5 5 3 1 2 4 6 44 428 3
cert_coverFacet 6 204
cert_cover_2 6 2 1 5 6 76 204 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0734

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0735.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0735

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 149, 789, 709, 185, 369, 225, 782, 122, 346, 554, 738, 156, 284, 684, 21, 133, 517, 49, 145, 273, 97, 161, 193, 321, 577, 769, 90, 42, 266, 522, 98, 546, 322, 578, 770, 28, 140, 268, 524, 148, 276, 644, 772, 56, 152, 280, 168, 552, 112, 336, 224, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_149, vertices_789, vertices_709, vertices_185, vertices_369, vertices_225, vertices_782, vertices_122, vertices_346, vertices_554, vertices_738, vertices_156, vertices_284, vertices_684] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_49, vertices_145, vertices_273, vertices_97, vertices_161, vertices_193, vertices_321, vertices_577, vertices_769, vertices_90, vertices_42, vertices_266, vertices_522, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_644, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_552, vertices_112, vertices_336, vertices_224, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_149), (false, vertices_789), (false, vertices_709), (false, vertices_185), (false, vertices_369), (false, vertices_225), (true, vertices_90), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_98), (true, vertices_546), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_280), (true, vertices_552), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 15 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_90) then 16 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 149 1 225 42 266 522 98 546 28 140 268 524 280 552 672 835 90 789 709 185 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 1 2 4 6 8 684 140 2
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 4 90 122 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 7 90 346 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 98 738 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 684
cert_cover_5 7 3 1 2 4 6 140 684 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0735

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0736.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0736

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 787, 611, 387, 565, 149, 409, 842, 354, 418, 156, 796, 716, 740, 488, 35, 131, 259, 515, 21, 37, 133, 145, 273, 529, 545, 385, 98, 162, 290, 322, 578, 386, 770, 28, 140, 524, 148, 532, 164, 548, 708, 152, 280, 200, 328, 584, 392, 776, 784, 224, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_787, vertices_611, vertices_387, vertices_565, vertices_149, vertices_409, vertices_842, vertices_354, vertices_418, vertices_156, vertices_796, vertices_716, vertices_740, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_21, vertices_37, vertices_133, vertices_145, vertices_273, vertices_529, vertices_545, vertices_385, vertices_98, vertices_162, vertices_290, vertices_322, vertices_578, vertices_386, vertices_770, vertices_28, vertices_140, vertices_524, vertices_148, vertices_532, vertices_164, vertices_548, vertices_708, vertices_152, vertices_280, vertices_200, vertices_328, vertices_584, vertices_392, vertices_776, vertices_784, vertices_224, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_787), (false, vertices_611), (false, vertices_387), (false, vertices_565), (false, vertices_149), (false, vertices_409), (true, vertices_290), (true, vertices_322), (true, vertices_28), (true, vertices_140), (true, vertices_524), (true, vertices_708), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_776), (true, vertices_224), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 15 else
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_708) then 20 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_167), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_708), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_4 0 0 2 5 7 8 842 322 1
cert_row_4 1 1 2 3 7 8 796 28 3
cert_row_2 2 1 5 6 8 708
cert_row_4 3 2 4 5 6 7 488 200 1
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 842
cert_cover_5 0 0 0 2 5 7 322 842 1
cert_coverFacet 1 354
cert_cover_2 1 4 0 5 7 98 354 3
cert_coverFacet 2 418
cert_cover_2 2 4 0 6 7 162 418 3
cert_coverFacet 3 156
cert_cover_2 3 2 1 3 6 28 156 3
cert_coverFacet 4 796
cert_cover_5 4 1 1 2 3 7 28 796 3
cert_coverFacet 5 716
cert_cover_5 5 2 1 2 5 6 140 716 2
cert_coverFacet 6 740
cert_cover_5 6 2 1 4 5 6 164 740 2
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 200 488 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0736

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0737.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0737

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 301, 789, 677, 601, 617, 902, 154, 394, 210, 850, 738, 420, 248, 424, 37, 261, 517, 25, 41, 585, 265, 273, 529, 545, 26, 138, 266, 82, 146, 274, 194, 578, 386, 642, 770, 164, 292, 388, 644, 772, 88, 152, 104, 168, 296, 392, 208, 592, 784, 224, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_301, vertices_789, vertices_677, vertices_601, vertices_617, vertices_902, vertices_154, vertices_394, vertices_210, vertices_850, vertices_738, vertices_420, vertices_248, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_25, vertices_41, vertices_585, vertices_265, vertices_273, vertices_529, vertices_545, vertices_26, vertices_138, vertices_266, vertices_82, vertices_146, vertices_274, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_164, vertices_292, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_104, vertices_168, vertices_296, vertices_392, vertices_208, vertices_592, vertices_784, vertices_224, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_301), (false, vertices_789), (false, vertices_677), (false, vertices_601), (false, vertices_617), (true, vertices_138), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_388), (true, vertices_152), (true, vertices_168), (true, vertices_392), (true, vertices_208), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 16 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_601) then 22 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 138 1 82 2 146 194 578 386 642 770 388 152 168 392 208 224 416 283 301 789 677 601 617
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_4 1 0 3 5 7 8 850 82 3
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 2 3 4 5 6 248 88 2
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 850
cert_cover_5 4 1 0 3 5 7 82 850 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 194 738 1
cert_coverFacet 6 420
cert_cover_2 6 4 1 6 7 164 420 3
cert_coverFacet 7 248
cert_cover_5 7 3 2 3 4 5 88 248 2
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0737

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0738.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0738

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 565, 661, 229, 409, 369, 710, 570, 154, 842, 394, 658, 868, 312, 808, 533, 37, 133, 49, 145, 273, 97, 193, 321, 385, 26, 138, 266, 522, 146, 530, 194, 322, 578, 386, 642, 100, 548, 196, 580, 644, 56, 152, 280, 296, 552, 392, 776, 304, 560, 656, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_565, vertices_661, vertices_229, vertices_409, vertices_369, vertices_710, vertices_570, vertices_154, vertices_842, vertices_394, vertices_658, vertices_868, vertices_312, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_533, vertices_37, vertices_133, vertices_49, vertices_145, vertices_273, vertices_97, vertices_193, vertices_321, vertices_385, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_100, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_152, vertices_280, vertices_296, vertices_552, vertices_392, vertices_776, vertices_304, vertices_560, vertices_656, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_565), (false, vertices_661), (false, vertices_229), (false, vertices_409), (false, vertices_369), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_578), (true, vertices_642), (true, vertices_580), (true, vertices_56), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_565) then 18 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_229) then 20 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_800) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
cert_nodeAtPriority_68 0 26 1 138 266 522 146 530 578 642 580 56 296 552 776 800 832 451 565 661 229 409 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 8 710 194 1
cert_row_4 1 0 2 3 4 8 570 26 3
cert_row_4 2 0 2 5 7 8 842 266 2
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 6 3 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 0 0 1 5 6 194 710 1
cert_coverFacet 1 570
cert_cover_5 1 1 0 2 3 4 26 570 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 842
cert_cover_5 3 2 0 2 5 7 266 842 2
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 868
cert_cover_5 6 3 1 4 5 7 100 868 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0738

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0739.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0739

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 557, 653, 229, 361, 465, 598, 666, 810, 338, 402, 834, 212, 660, 868, 525, 37, 133, 41, 137, 265, 97, 193, 321, 385, 138, 266, 522, 82, 146, 274, 530, 322, 578, 386, 770, 84, 148, 532, 100, 548, 196, 580, 644, 296, 552, 648, 208, 336, 400, 656, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_557, vertices_653, vertices_229, vertices_361, vertices_465, vertices_598, vertices_666, vertices_810, vertices_338, vertices_402, vertices_834, vertices_212, vertices_660, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_525, vertices_37, vertices_133, vertices_41, vertices_137, vertices_265, vertices_97, vertices_193, vertices_321, vertices_385, vertices_138, vertices_266, vertices_522, vertices_82, vertices_146, vertices_274, vertices_530, vertices_322, vertices_578, vertices_386, vertices_770, vertices_84, vertices_148, vertices_532, vertices_100, vertices_548, vertices_196, vertices_580, vertices_644, vertices_296, vertices_552, vertices_648, vertices_208, vertices_336, vertices_400, vertices_656, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_557), (false, vertices_653), (false, vertices_229), (false, vertices_361), (false, vertices_465), (true, vertices_522), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_580), (true, vertices_656), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_229) then 20 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_800) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
cert_nodeAtPriority_68 0 522 1 82 146 274 530 322 578 770 84 148 532 580 656 800 832 395 557 653 229 361 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 138 2
cert_row_4 1 0 1 3 5 8 598 82 1
cert_row_4 2 0 2 4 7 8 810 266 2
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 6 3 0 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 1 0 1 3 5 82 598 1
cert_coverFacet 1 666
cert_cover_5 1 0 0 2 3 6 138 666 2
cert_coverFacet 2 810
cert_cover_5 2 2 0 2 4 7 266 810 2
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 868
cert_cover_5 8 3 1 4 5 7 100 868 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0739

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0740.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0740

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 109, 805, 709, 297, 329, 465, 346, 666, 810, 402, 244, 692, 120, 568, 37, 69, 517, 41, 73, 265, 289, 193, 321, 385, 641, 769, 26, 266, 522, 146, 274, 386, 642, 770, 180, 100, 548, 196, 644, 56, 88, 536, 104, 296, 552, 328, 112, 560, 208, 336, 400, 656, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_109, vertices_805, vertices_709, vertices_297, vertices_329, vertices_465, vertices_346, vertices_666, vertices_810, vertices_402, vertices_244, vertices_692, vertices_120, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_41, vertices_73, vertices_265, vertices_289, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_266, vertices_522, vertices_146, vertices_274, vertices_386, vertices_642, vertices_770, vertices_180, vertices_100, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_536, vertices_104, vertices_296, vertices_552, vertices_328, vertices_112, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_109), (false, vertices_805), (false, vertices_709), (false, vertices_297), (false, vertices_329), (false, vertices_465), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_180), (true, vertices_56), (true, vertices_88), (true, vertices_536), (true, vertices_552), (true, vertices_112), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 16 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_109) then 17 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_180) then 21 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_656) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_180), by decide +kernel⟩
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
cert_row_2 0 1 3 4 6 180
cert_row_4 1 0 2 3 5 7 346 26 3
cert_row_4 2 0 2 3 6 8 666 26 3
cert_row_4 3 0 2 4 7 8 810 266 2
cert_rows
cert_pivot_2 1 5 3 0
cert_heightProof 4
cert_coverFacet 0 346
cert_cover_5 0 1 0 2 3 5 26 346 3
cert_coverFacet 1 666
cert_cover_5 1 2 0 2 3 6 26 666 3
cert_coverFacet 2 810
cert_cover_5 2 3 0 2 4 7 266 810 2
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 244
cert_cover_5 4 0 1 3 4 5 180 244 3
cert_coverFacet 5 692
cert_cover_5 5 0 1 3 4 8 180 692 3
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0740

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0741.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0741

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 155, 275, 675, 309, 613, 177, 602, 650, 850, 484, 836, 472, 744, 432, 19, 131, 259, 515, 37, 261, 517, 49, 145, 273, 161, 545, 26, 138, 522, 594, 274, 642, 770, 100, 292, 324, 580, 772, 88, 152, 200, 584, 648, 176, 304, 336, 400, 224, 608, 416, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_155, vertices_275, vertices_675, vertices_309, vertices_613, vertices_177, vertices_602, vertices_650, vertices_850, vertices_484, vertices_836, vertices_472, vertices_744, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_37, vertices_261, vertices_517, vertices_49, vertices_145, vertices_273, vertices_161, vertices_545, vertices_26, vertices_138, vertices_522, vertices_594, vertices_274, vertices_642, vertices_770, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_88, vertices_152, vertices_200, vertices_584, vertices_648, vertices_176, vertices_304, vertices_336, vertices_400, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_155), (false, vertices_275), (false, vertices_675), (false, vertices_309), (false, vertices_613), (false, vertices_177), (true, vertices_522), (true, vertices_594), (true, vertices_324), (true, vertices_88), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_336), (true, vertices_400), (true, vertices_224), (true, vertices_416), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 14 22 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_155) then 19 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_675) then 20 else
  if p.val = (false, vertices_309) then 16 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_177) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_594) then 21 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_448) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_594), by decide +kernel⟩
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
cert_row_2 0 0 3 5 8 594
cert_row_4 1 1 4 5 6 7 484 100 3
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 2 4 5 6 8 744 200 1
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 602
cert_cover_5 0 0 0 2 3 5 26 602 3
cert_coverFacet 1 650
cert_cover_2 1 2 0 6 8 138 650 3
cert_coverFacet 2 850
cert_cover_5 2 0 0 3 5 7 594 850 3
cert_coverFacet 3 484
cert_cover_5 3 1 1 4 5 6 100 484 3
cert_coverFacet 4 836
cert_cover_2 4 5 1 7 8 324 836 3
cert_coverFacet 5 472
cert_cover_5 5 2 2 3 5 6 88 472 3
cert_coverFacet 6 744
cert_cover_5 6 3 2 4 5 6 200 744 1
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0741

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0742.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0742

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 279, 355, 675, 901, 809, 346, 210, 226, 796, 212, 596, 740, 632, 360, 23, 35, 131, 259, 133, 261, 289, 545, 641, 769, 82, 146, 274, 98, 162, 194, 322, 84, 148, 276, 532, 196, 580, 644, 772, 88, 280, 536, 104, 296, 552, 328, 776, 208, 592, 224, 352, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_279, vertices_355, vertices_675, vertices_901, vertices_809, vertices_346, vertices_210, vertices_226, vertices_796, vertices_212, vertices_596, vertices_740, vertices_632, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_35, vertices_131, vertices_259, vertices_133, vertices_261, vertices_289, vertices_545, vertices_641, vertices_769, vertices_82, vertices_146, vertices_274, vertices_98, vertices_162, vertices_194, vertices_322, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_580, vertices_644, vertices_772, vertices_88, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_328, vertices_776, vertices_208, vertices_592, vertices_224, vertices_352, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_279), (false, vertices_355), (false, vertices_675), (false, vertices_901), (false, vertices_809), (true, vertices_82), (true, vertices_194), (true, vertices_84), (true, vertices_532), (true, vertices_196), (true, vertices_580), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_104), (true, vertices_328), (true, vertices_208), (true, vertices_592), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 15 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 16 else
  if p.val = (false, vertices_279) then 17 else
  if p.val = (false, vertices_355) then 20 else
  if p.val = (false, vertices_675) then 21 else
  if p.val = (false, vertices_901) then 18 else
  if p.val = (false, vertices_809) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 7 346 82 1
cert_row_4 1 1 2 3 7 8 796 276 1
cert_row_4 2 1 4 5 6 8 740 196 1
cert_row_4 3 2 3 4 5 8 632 88 2
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 346
cert_cover_5 0 0 0 2 3 5 82 346 1
cert_coverFacet 1 210
cert_cover_2 1 3 0 5 6 82 210 3
cert_coverFacet 2 226
cert_cover_2 2 4 0 5 6 98 226 3
cert_coverFacet 3 796
cert_cover_5 3 1 1 2 3 7 276 796 1
cert_coverFacet 4 212
cert_cover_2 4 3 1 5 6 84 212 3
cert_coverFacet 5 596
cert_cover_2 5 3 1 5 8 84 596 3
cert_coverFacet 6 740
cert_cover_5 6 2 1 4 5 6 196 740 1
cert_coverFacet 7 632
cert_cover_5 7 3 2 3 4 5 88 632 2
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0742

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0743.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0743

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 163, 451, 677, 665, 841, 393, 118, 182, 410, 338, 796, 340, 660, 868, 35, 67, 131, 137, 265, 521, 161, 545, 321, 577, 385, 641, 54, 82, 146, 274, 98, 162, 322, 386, 84, 148, 276, 532, 100, 164, 548, 324, 644, 772, 152, 280, 536, 392, 776, 336, 656, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_163, vertices_451, vertices_677, vertices_665, vertices_841, vertices_393, vertices_118, vertices_182, vertices_410, vertices_338, vertices_796, vertices_340, vertices_660, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_131, vertices_137, vertices_265, vertices_521, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_641, vertices_54, vertices_82, vertices_146, vertices_274, vertices_98, vertices_162, vertices_322, vertices_386, vertices_84, vertices_148, vertices_276, vertices_532, vertices_100, vertices_164, vertices_548, vertices_324, vertices_644, vertices_772, vertices_152, vertices_280, vertices_536, vertices_392, vertices_776, vertices_336, vertices_656, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_163), (false, vertices_451), (false, vertices_677), (false, vertices_665), (false, vertices_841), (false, vertices_393), (true, vertices_54), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_100), (true, vertices_324), (true, vertices_772), (true, vertices_280), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 15 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_393) then 1 else
  if p.val = (true, vertices_54) then 17 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_336) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 146 1
cert_row_2 1 0 1 3 4 54
cert_row_4 2 1 2 3 7 8 796 276 1
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 6 0 2 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 1 0 1 3 5 54 118 3
cert_coverFacet 1 182
cert_cover_5 1 1 0 1 3 6 54 182 3
cert_coverFacet 2 410
cert_cover_5 2 0 0 2 3 6 146 410 1
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 796
cert_cover_5 4 2 1 2 3 7 276 796 1
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 868
cert_cover_5 7 3 1 4 5 7 100 868 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0743

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0744.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0744

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 779, 387, 589, 85, 149, 457, 241, 818, 482, 674, 348, 796, 692, 368, 131, 259, 515, 21, 69, 133, 517, 73, 265, 521, 81, 145, 193, 385, 162, 290, 546, 386, 642, 770, 284, 76, 524, 84, 148, 532, 644, 328, 776, 112, 176, 304, 560, 336, 784, 224, 352, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_779, vertices_387, vertices_589, vertices_85, vertices_149, vertices_457, vertices_241, vertices_818, vertices_482, vertices_674, vertices_348, vertices_796, vertices_692, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_21, vertices_69, vertices_133, vertices_517, vertices_73, vertices_265, vertices_521, vertices_81, vertices_145, vertices_193, vertices_385, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_284, vertices_76, vertices_524, vertices_84, vertices_148, vertices_532, vertices_644, vertices_328, vertices_776, vertices_112, vertices_176, vertices_304, vertices_560, vertices_336, vertices_784, vertices_224, vertices_352, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_779), (false, vertices_387), (false, vertices_589), (false, vertices_85), (false, vertices_149), (false, vertices_457), (false, vertices_241), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_284), (true, vertices_532), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_352), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_85) then 1 else
  if p.val = (false, vertices_149) then 2 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_284) then 18 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_284), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
cert_row_2 0 1 2 3 7 284
cert_row_4 1 0 4 5 6 7 482 162 2
cert_row_4 2 0 3 4 7 8 818 290 1
cert_row_4 3 1 3 4 6 8 692 148 2
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 818
cert_cover_5 0 2 0 3 4 7 290 818 1
cert_coverFacet 1 482
cert_cover_5 1 1 0 4 5 6 162 482 2
cert_coverFacet 2 674
cert_cover_2 2 4 0 6 8 162 674 3
cert_coverFacet 3 348
cert_cover_5 3 0 1 2 3 5 284 348 3
cert_coverFacet 4 796
cert_cover_5 4 0 1 2 3 8 284 796 3
cert_coverFacet 5 692
cert_cover_5 5 3 1 3 4 6 148 692 2
cert_coverFacet 6 368
cert_cover_2 6 4 3 5 7 112 368 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0744

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0746.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0746

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 301, 557, 601, 457, 369, 678, 714, 178, 338, 594, 402, 450, 908, 436, 45, 73, 265, 521, 49, 81, 529, 289, 545, 321, 50, 82, 146, 274, 530, 162, 546, 194, 322, 578, 386, 642, 268, 524, 164, 292, 548, 388, 644, 200, 584, 392, 648, 176, 304, 336, 592, 400, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_301, vertices_557, vertices_601, vertices_457, vertices_369, vertices_678, vertices_714, vertices_178, vertices_338, vertices_594, vertices_402, vertices_450, vertices_908, vertices_436] (by decide +kernel)
  polygons := literalFinset [vertices_45, vertices_73, vertices_265, vertices_521, vertices_49, vertices_81, vertices_529, vertices_289, vertices_545, vertices_321, vertices_50, vertices_82, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_200, vertices_584, vertices_392, vertices_648, vertices_176, vertices_304, vertices_336, vertices_592, vertices_400, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_301), (false, vertices_557), (false, vertices_601), (false, vertices_457), (false, vertices_369), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_164), (true, vertices_388), (true, vertices_644), (true, vertices_648), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 82 1 146 2 274 162 194 322 578 386 642 164 388 644 648 176 400 563 301 557 601 457 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 194 1
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 1 2 6 7 8 908 268 2
cert_row_4 3 1 3 4 6 7 436 164 1
cert_rows
cert_pivot_2 5 0 2 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 194 714 1
cert_coverFacet 2 178
cert_cover_2 2 3 0 4 6 50 178 3
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 594
cert_cover_2 4 3 0 5 8 82 594 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 450
cert_cover_2 6 5 0 6 7 194 450 3
cert_coverFacet 7 908
cert_cover_5 7 2 1 2 6 7 268 908 2
cert_coverFacet 8 436
cert_cover_5 8 3 1 3 4 6 164 436 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0746

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0747.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0747

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 61, 541, 421, 837, 369, 902, 666, 210, 482, 834, 684, 120, 216, 232, 29, 37, 261, 517, 49, 81, 529, 289, 321, 577, 82, 146, 530, 194, 322, 578, 386, 642, 770, 44, 524, 164, 388, 644, 772, 56, 88, 152, 536, 104, 168, 200, 648, 112, 208, 224, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_61, vertices_541, vertices_421, vertices_837, vertices_369, vertices_902, vertices_666, vertices_210, vertices_482, vertices_834, vertices_684, vertices_120, vertices_216, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_37, vertices_261, vertices_517, vertices_49, vertices_81, vertices_529, vertices_289, vertices_321, vertices_577, vertices_82, vertices_146, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_164, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_536, vertices_104, vertices_168, vertices_200, vertices_648, vertices_112, vertices_208, vertices_224, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_61), (false, vertices_541), (false, vertices_421), (false, vertices_837), (false, vertices_369), (true, vertices_146), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_644), (true, vertices_88), (true, vertices_152), (true, vertices_104), (true, vertices_168), (true, vertices_200), (true, vertices_648), (true, vertices_208), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 16 else
  if p.val = (false, vertices_61) then 18 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 146 2 194 1 322 386 642 770 644 88 152 104 168 200 648 208 224 595 61 541 421 837 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 146 1
cert_row_4 1 0 4 5 6 7 482 194 1
cert_row_4 2 0 1 6 7 8 902 386 1
cert_row_4 3 1 2 4 6 8 684 44 3
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 2 0 1 6 7 386 902 1
cert_coverFacet 1 666
cert_cover_5 1 0 0 2 3 6 146 666 1
cert_coverFacet 2 210
cert_cover_2 2 3 0 5 6 82 210 3
cert_coverFacet 3 482
cert_cover_5 3 1 0 4 5 6 194 482 1
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 684
cert_cover_5 5 3 1 2 4 6 44 684 3
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 232
cert_cover_2 8 4 2 5 6 104 232 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0747

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3303 : Certifies 3303 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0716.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3304 : Certifies 3304 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0717.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3305 : Certifies 3305 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0718.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3306 : Certifies 3306 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0719.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3307 : Certifies 3307 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0720.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3308 : Certifies 3308 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0721.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3309 : Certifies 3309 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0723.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3310 : Certifies 3310 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0724.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3311 : Certifies 3311 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0725.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3312 : Certifies 3312 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0726.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3313 : Certifies 3313 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0727.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3314 : Certifies 3314 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0728.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3315 : Certifies 3315 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0729.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3316 : Certifies 3316 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0730.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3317 : Certifies 3317 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0731.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3318 : Certifies 3318 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0732.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3319 : Certifies 3319 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0733.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3320 : Certifies 3320 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0734.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3321 : Certifies 3321 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0735.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3322 : Certifies 3322 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0736.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3323 : Certifies 3323 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0737.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3324 : Certifies 3324 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0738.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3325 : Certifies 3325 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0739.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3326 : Certifies 3326 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0740.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3327 : Certifies 3327 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0741.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3328 : Certifies 3328 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0742.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3329 : Certifies 3329 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0743.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3330 : Certifies 3330 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0744.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3331 : Certifies 3331 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0746.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3332 : Certifies 3332 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0747.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B109 (j : Fin 30) :
    Certifies (3303 + j.val) := by
  fin_cases j
  · exact projection_3303
  · exact projection_3304
  · exact projection_3305
  · exact projection_3306
  · exact projection_3307
  · exact projection_3308
  · exact projection_3309
  · exact projection_3310
  · exact projection_3311
  · exact projection_3312
  · exact projection_3313
  · exact projection_3314
  · exact projection_3315
  · exact projection_3316
  · exact projection_3317
  · exact projection_3318
  · exact projection_3319
  · exact projection_3320
  · exact projection_3321
  · exact projection_3322
  · exact projection_3323
  · exact projection_3324
  · exact projection_3325
  · exact projection_3326
  · exact projection_3327
  · exact projection_3328
  · exact projection_3329
  · exact projection_3330
  · exact projection_3331
  · exact projection_3332

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
