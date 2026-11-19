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
/- Source: ProjectionCertificates/R_m15e10q1_0273.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0273

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 781, 677, 453, 409, 657, 358, 218, 810, 458, 114, 562, 244, 804, 688, 133, 261, 517, 25, 265, 521, 145, 529, 385, 641, 26, 202, 266, 522, 50, 82, 530, 98, 290, 546, 322, 100, 164, 292, 548, 196, 324, 772, 152, 392, 776, 112, 176, 560, 208, 656, 672, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_781, vertices_677, vertices_453, vertices_409, vertices_657, vertices_358, vertices_218, vertices_810, vertices_458, vertices_114, vertices_562, vertices_244, vertices_804, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_265, vertices_521, vertices_145, vertices_529, vertices_385, vertices_641, vertices_26, vertices_202, vertices_266, vertices_522, vertices_50, vertices_82, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_100, vertices_164, vertices_292, vertices_548, vertices_196, vertices_324, vertices_772, vertices_152, vertices_392, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_656, vertices_672, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_781), (false, vertices_677), (false, vertices_453), (false, vertices_409), (false, vertices_657), (true, vertices_202), (true, vertices_266), (true, vertices_50), (true, vertices_82), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_100), (true, vertices_292), (true, vertices_112), (true, vertices_176), (true, vertices_560), (true, vertices_208), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_409) then 23 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_202) then 17 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
cert_nodeAtPriority_51 657 266 50 82 98 290 546 322 100 292 112 176 560 208 800 539 202 781 677 453 409
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 266 2
cert_row_2 1 0 2 5 6 202
cert_row_4 2 0 1 4 5 7 358 98 1
cert_row_4 3 1 3 4 5 6 244 100 1
cert_rows
cert_pivot_2 8 2 0 1
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 2 0 1 4 5 98 358 1
cert_coverFacet 1 218
cert_cover_5 1 1 0 2 3 5 26 218 3
cert_coverFacet 2 810
cert_cover_5 2 0 0 2 4 7 266 810 2
cert_coverFacet 3 458
cert_cover_5 3 1 0 2 5 7 202 458 3
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 562
cert_cover_2 5 3 0 4 8 50 562 3
cert_coverFacet 6 244
cert_cover_5 6 3 1 3 4 5 100 244 1
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0273

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0274.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0274

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 805, 681, 841, 433, 449, 334, 782, 566, 86, 666, 210, 308, 468, 688, 73, 137, 521, 161, 289, 545, 193, 321, 385, 769, 270, 22, 70, 518, 74, 138, 522, 82, 146, 530, 194, 52, 84, 276, 292, 548, 324, 772, 328, 648, 776, 176, 304, 560, 208, 400, 656, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_805, vertices_681, vertices_841, vertices_433, vertices_449, vertices_334, vertices_782, vertices_566, vertices_86, vertices_666, vertices_210, vertices_308, vertices_468, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_521, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_270, vertices_22, vertices_70, vertices_518, vertices_74, vertices_138, vertices_522, vertices_82, vertices_146, vertices_530, vertices_194, vertices_52, vertices_84, vertices_276, vertices_292, vertices_548, vertices_324, vertices_772, vertices_328, vertices_648, vertices_776, vertices_176, vertices_304, vertices_560, vertices_208, vertices_400, vertices_656, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_805), (false, vertices_681), (false, vertices_841), (false, vertices_433), (false, vertices_449), (true, vertices_270), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_522), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_560), (true, vertices_208), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_270) then 17 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 449 22 70 518 522 82 146 530 52 84 276 324 560 208 656 203 270 805 681 841 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 22 3
cert_row_4 1 0 2 3 6 8 666 138 2
cert_row_2 2 0 1 2 7 270
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 4 8 0 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 2 0 1 2 5 270 334 3
cert_coverFacet 1 782
cert_cover_5 1 2 0 1 2 8 270 782 3
cert_coverFacet 2 566
cert_cover_5 2 0 0 1 3 4 22 566 3
cert_coverFacet 3 86
cert_cover_2 3 1 0 3 5 22 86 3
cert_coverFacet 4 666
cert_cover_5 4 1 0 2 3 6 138 666 2
cert_coverFacet 5 210
cert_cover_2 5 3 0 5 6 82 210 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 468
cert_cover_5 7 3 1 3 5 6 84 468 3
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0274

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0275.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0275

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 589, 805, 453, 433, 705, 782, 314, 602, 178, 658, 802, 220, 412, 720, 69, 261, 517, 161, 289, 545, 193, 577, 385, 641, 26, 266, 522, 50, 146, 530, 162, 290, 546, 642, 770, 156, 76, 268, 524, 196, 388, 772, 88, 280, 584, 176, 304, 208, 592, 400, 656, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_589, vertices_805, vertices_453, vertices_433, vertices_705, vertices_782, vertices_314, vertices_602, vertices_178, vertices_658, vertices_802, vertices_220, vertices_412, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_26, vertices_266, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_156, vertices_76, vertices_268, vertices_524, vertices_196, vertices_388, vertices_772, vertices_88, vertices_280, vertices_584, vertices_176, vertices_304, vertices_208, vertices_592, vertices_400, vertices_656, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_589), (false, vertices_805), (false, vertices_453), (false, vertices_433), (false, vertices_705), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_290), (true, vertices_770), (true, vertices_156), (true, vertices_268), (true, vertices_88), (true, vertices_280), (true, vertices_208), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_156) then 19 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 705 1 26 2 266 3 522 50 146 530 290 770 268 88 280 208 592 656 675 589 156 805 453 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 6 156
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 2 3 4 7 314 26 3
cert_row_4 3 0 2 3 5 8 602 26 3
cert_rows
cert_pivot_2 6 1 4 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 314
cert_cover_5 1 2 0 2 3 4 26 314 3
cert_coverFacet 2 602
cert_cover_5 2 3 0 2 3 5 26 602 3
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 220
cert_cover_5 6 0 1 2 3 5 156 220 3
cert_coverFacet 7 412
cert_cover_5 7 0 1 2 3 7 156 412 3
cert_coverFacet 8 720
cert_cover_2 8 5 3 6 8 208 720 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0275

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0276.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0276

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 535, 837, 313, 625, 481, 654, 454, 570, 154, 402, 740, 408, 424, 680, 23, 261, 517, 49, 273, 529, 97, 289, 321, 577, 134, 262, 518, 26, 138, 522, 146, 274, 530, 386, 196, 324, 580, 644, 56, 152, 280, 168, 296, 552, 392, 648, 560, 400, 224, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_535, vertices_837, vertices_313, vertices_625, vertices_481, vertices_654, vertices_454, vertices_570, vertices_154, vertices_402, vertices_740, vertices_408, vertices_424, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_97, vertices_289, vertices_321, vertices_577, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_196, vertices_324, vertices_580, vertices_644, vertices_56, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_560, vertices_400, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_535), (false, vertices_837), (false, vertices_313), (false, vertices_625), (false, vertices_481), (true, vertices_134), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_386), (true, vertices_196), (true, vertices_644), (true, vertices_152), (true, vertices_168), (true, vertices_552), (true, vertices_392), (true, vertices_648), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 16 else
  if p.val = (false, vertices_535) then 17 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 134 2
cert_row_4 1 0 2 3 4 8 570 26 3
cert_row_4 2 0 1 2 6 8 654 134 2
cert_row_4 3 1 4 5 6 8 740 196 1
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 134 654 2
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 134 454 2
cert_coverFacet 2 570
cert_cover_5 2 1 0 2 3 4 26 570 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 740
cert_cover_5 5 3 1 4 5 6 196 740 1
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coverFacet 8 680
cert_cover_2 8 4 2 6 8 168 680 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0276

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0277.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0277

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 333, 653, 597, 369, 401, 657, 302, 558, 666, 626, 178, 418, 868, 432, 13, 69, 517, 137, 265, 81, 145, 273, 529, 321, 385, 641, 46, 138, 266, 522, 50, 146, 530, 162, 290, 546, 386, 268, 524, 292, 548, 324, 580, 648, 112, 176, 304, 592, 400, 656, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_333, vertices_653, vertices_597, vertices_369, vertices_401, vertices_657, vertices_302, vertices_558, vertices_666, vertices_626, vertices_178, vertices_418, vertices_868, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_137, vertices_265, vertices_81, vertices_145, vertices_273, vertices_529, vertices_321, vertices_385, vertices_641, vertices_46, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_268, vertices_524, vertices_292, vertices_548, vertices_324, vertices_580, vertices_648, vertices_112, vertices_176, vertices_304, vertices_592, vertices_400, vertices_656, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_333), (false, vertices_653), (false, vertices_597), (false, vertices_369), (false, vertices_401), (false, vertices_657), (true, vertices_46), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_292), (true, vertices_548), (true, vertices_176), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (false, vertices_657) then 1 else
  if p.val = (true, vertices_46) then 16 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
cert_nodeAtPriority_15 0 401 1 657 522 50 146 530 162 290 546 292 548 176 608 416 395 46 333 653 597 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 138 2
cert_row_2 1 0 1 2 4 46
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 1 4 5 7 8 868 292 2
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 1 0 1 2 7 46 302 3
cert_coverFacet 1 558
cert_cover_5 1 1 0 1 2 8 46 558 3
cert_coverFacet 2 666
cert_cover_5 2 0 0 2 3 6 138 666 2
cert_coverFacet 3 626
cert_cover_5 3 2 0 3 4 5 50 626 3
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 868
cert_cover_5 6 3 1 4 5 7 292 868 2
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0277

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0278.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0278

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 535, 557, 421, 313, 601, 678, 454, 714, 850, 216, 408, 424, 680, 464, 23, 37, 261, 517, 25, 41, 521, 273, 529, 289, 134, 262, 518, 274, 530, 194, 322, 578, 642, 164, 548, 388, 88, 152, 280, 168, 296, 552, 200, 584, 392, 648, 208, 336, 592, 400, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_535, vertices_557, vertices_421, vertices_313, vertices_601, vertices_678, vertices_454, vertices_714, vertices_850, vertices_216, vertices_408, vertices_424, vertices_680, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_37, vertices_261, vertices_517, vertices_25, vertices_41, vertices_521, vertices_273, vertices_529, vertices_289, vertices_134, vertices_262, vertices_518, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_164, vertices_548, vertices_388, vertices_88, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_200, vertices_584, vertices_392, vertices_648, vertices_208, vertices_336, vertices_592, vertices_400, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_535), (false, vertices_557), (false, vertices_421), (false, vertices_313), (false, vertices_601), (true, vertices_134), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_392), (true, vertices_648), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 16 else
  if p.val = (false, vertices_535) then 17 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 134 2
cert_row_4 1 0 1 5 6 7 454 134 2
cert_row_4 2 0 2 5 6 8 714 194 1
cert_row_4 3 0 3 5 7 8 850 274 2
cert_rows
cert_pivot_2 4 1 2 0
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 134 678 2
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 6 134 454 2
cert_coverFacet 2 714
cert_cover_5 2 2 0 2 5 6 194 714 1
cert_coverFacet 3 850
cert_cover_5 3 3 0 3 5 7 274 850 2
cert_coverFacet 4 216
cert_cover_2 4 3 2 5 6 88 216 3
cert_coverFacet 5 408
cert_cover_2 5 3 2 6 7 152 408 3
cert_coverFacet 6 424
cert_cover_2 6 4 2 6 7 168 424 3
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0278

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0279.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0279

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 109, 589, 421, 313, 905, 598, 198, 794, 338, 482, 898, 228, 632, 368, 77, 37, 133, 517, 41, 265, 521, 289, 385, 641, 70, 134, 518, 82, 274, 530, 194, 322, 386, 642, 770, 100, 164, 196, 580, 56, 280, 536, 104, 584, 776, 112, 304, 336, 592, 224, 352, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_109, vertices_589, vertices_421, vertices_313, vertices_905, vertices_598, vertices_198, vertices_794, vertices_338, vertices_482, vertices_898, vertices_228, vertices_632, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_77, vertices_37, vertices_133, vertices_517, vertices_41, vertices_265, vertices_521, vertices_289, vertices_385, vertices_641, vertices_70, vertices_134, vertices_518, vertices_82, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_100, vertices_164, vertices_196, vertices_580, vertices_56, vertices_280, vertices_536, vertices_104, vertices_584, vertices_776, vertices_112, vertices_304, vertices_336, vertices_592, vertices_224, vertices_352, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_109), (false, vertices_589), (false, vertices_421), (false, vertices_313), (false, vertices_905), (true, vertices_70), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_196), (true, vertices_536), (true, vertices_112), (true, vertices_336), (true, vertices_592), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_905) then 23 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 70 1 82 2 274 530 194 322 386 770 196 536 112 336 592 224 352 647 109 589 421 313 905
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 70 2
cert_row_4 1 0 4 5 6 7 482 194 1
cert_row_4 2 0 2 3 7 8 794 274 1
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 70 598 2
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 794
cert_cover_5 2 2 0 2 3 7 274 794 1
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 482
cert_cover_5 4 1 0 4 5 6 194 482 1
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 632
cert_cover_5 7 3 2 3 4 5 56 632 3
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0279

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0280.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0280

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 535, 899, 357, 709, 457, 570, 154, 714, 402, 316, 628, 408, 360, 616, 23, 259, 515, 69, 261, 517, 193, 321, 385, 641, 26, 138, 522, 146, 274, 530, 386, 642, 52, 276, 532, 100, 292, 580, 56, 152, 280, 104, 296, 552, 200, 328, 584, 392, 560, 400, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_535, vertices_899, vertices_357, vertices_709, vertices_457, vertices_570, vertices_154, vertices_714, vertices_402, vertices_316, vertices_628, vertices_408, vertices_360, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_259, vertices_515, vertices_69, vertices_261, vertices_517, vertices_193, vertices_321, vertices_385, vertices_641, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_52, vertices_276, vertices_532, vertices_100, vertices_292, vertices_580, vertices_56, vertices_152, vertices_280, vertices_104, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_560, vertices_400, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_535), (false, vertices_899), (false, vertices_357), (false, vertices_709), (false, vertices_457), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_52), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_584), (true, vertices_560), (true, vertices_400), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 16 else
  if p.val = (false, vertices_535) then 17 else
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 138 2
cert_row_4 1 0 2 3 4 8 570 26 3
cert_row_4 2 1 2 3 4 7 316 52 1
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 6 0 2 1
cert_heightProof 4
cert_coverFacet 0 570
cert_cover_5 0 1 0 2 3 4 26 570 3
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 714
cert_cover_5 2 0 0 2 5 6 138 714 2
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 316
cert_cover_5 4 2 1 2 3 4 52 316 1
cert_coverFacet 5 628
cert_cover_5 5 3 1 3 4 5 52 628 3
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coverFacet 8 616
cert_cover_2 8 4 2 5 8 104 616 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0280

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0281.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0281

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 775, 301, 205, 841, 721, 174, 310, 242, 402, 898, 232, 360, 880, 912, 519, 13, 133, 261, 73, 265, 193, 577, 641, 769, 38, 134, 262, 50, 146, 274, 162, 386, 642, 770, 44, 140, 292, 104, 168, 296, 200, 328, 112, 304, 208, 592, 400, 656, 784, 224, 352, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_775, vertices_301, vertices_205, vertices_841, vertices_721, vertices_174, vertices_310, vertices_242, vertices_402, vertices_898, vertices_232, vertices_360, vertices_880, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_519, vertices_13, vertices_133, vertices_261, vertices_73, vertices_265, vertices_193, vertices_577, vertices_641, vertices_769, vertices_38, vertices_134, vertices_262, vertices_50, vertices_146, vertices_274, vertices_162, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_292, vertices_104, vertices_168, vertices_296, vertices_200, vertices_328, vertices_112, vertices_304, vertices_208, vertices_592, vertices_400, vertices_656, vertices_784, vertices_224, vertices_352, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_775), (false, vertices_301), (false, vertices_205), (false, vertices_841), (false, vertices_721), (true, vertices_38), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_386), (true, vertices_104), (true, vertices_168), (true, vertices_112), (true, vertices_304), (true, vertices_400), (true, vertices_784), (true, vertices_224), (true, vertices_352), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_301) then 19 else
  if p.val = (false, vertices_205) then 20 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
cert_nodeAtPriority_62 38 50 146 274 162 386 104 168 112 304 400 784 224 352 896 647 775 301 205 841 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 6 174 38 2
cert_row_4 1 0 1 3 4 7 310 38 2
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 0 0 1 2 4 38 174 2
cert_coverFacet 1 310
cert_cover_5 1 1 0 1 3 4 38 310 2
cert_coverFacet 2 242
cert_cover_5 2 2 0 3 4 5 50 242 3
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 232
cert_cover_2 5 4 2 5 6 104 232 3
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coverFacet 7 880
cert_cover_5 7 3 3 4 5 7 112 880 3
cert_coverFacet 8 912
cert_cover_2 8 6 3 7 8 400 912 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0281

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0282.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0282

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 285, 541, 837, 625, 481, 654, 570, 282, 458, 418, 674, 204, 332, 740, 29, 261, 517, 49, 273, 529, 97, 289, 321, 577, 26, 138, 266, 522, 50, 274, 162, 290, 546, 386, 642, 76, 140, 268, 524, 196, 324, 580, 644, 280, 536, 200, 328, 560, 224, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_285, vertices_541, vertices_837, vertices_625, vertices_481, vertices_654, vertices_570, vertices_282, vertices_458, vertices_418, vertices_674, vertices_204, vertices_332, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_97, vertices_289, vertices_321, vertices_577, vertices_26, vertices_138, vertices_266, vertices_522, vertices_50, vertices_274, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_76, vertices_140, vertices_268, vertices_524, vertices_196, vertices_324, vertices_580, vertices_644, vertices_280, vertices_536, vertices_200, vertices_328, vertices_560, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_285), (false, vertices_541), (false, vertices_837), (false, vertices_625), (false, vertices_481), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_162), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_76), (true, vertices_140), (true, vertices_196), (true, vertices_644), (true, vertices_200), (true, vertices_328), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 16 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 26 3
cert_row_4 1 0 2 5 6 7 458 138 2
cert_row_4 2 0 1 2 6 8 654 138 1
cert_row_4 3 1 4 5 6 8 740 196 1
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 138 654 1
cert_coverFacet 1 570
cert_cover_5 1 0 0 2 3 4 26 570 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 458
cert_cover_5 3 1 0 2 5 6 138 458 2
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 204
cert_cover_2 6 2 1 5 6 76 204 3
cert_coverFacet 7 332
cert_cover_2 7 2 1 5 7 76 332 3
cert_coverFacet 8 740
cert_cover_5 8 3 1 4 5 6 196 740 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0282

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0283.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0283

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 535, 651, 419, 357, 677, 602, 154, 402, 620, 852, 216, 232, 680, 496, 23, 131, 259, 515, 37, 261, 517, 161, 289, 641, 26, 138, 522, 146, 274, 530, 386, 276, 532, 100, 548, 324, 580, 88, 152, 104, 168, 552, 200, 584, 648, 208, 336, 592, 400, 224, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_535, vertices_651, vertices_419, vertices_357, vertices_677, vertices_602, vertices_154, vertices_402, vertices_620, vertices_852, vertices_216, vertices_232, vertices_680, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_131, vertices_259, vertices_515, vertices_37, vertices_261, vertices_517, vertices_161, vertices_289, vertices_641, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_276, vertices_532, vertices_100, vertices_548, vertices_324, vertices_580, vertices_88, vertices_152, vertices_104, vertices_168, vertices_552, vertices_200, vertices_584, vertices_648, vertices_208, vertices_336, vertices_592, vertices_400, vertices_224, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_535), (false, vertices_651), (false, vertices_419), (false, vertices_357), (false, vertices_677), (true, vertices_26), (true, vertices_146), (true, vertices_580), (true, vertices_88), (true, vertices_152), (true, vertices_104), (true, vertices_168), (true, vertices_552), (true, vertices_200), (true, vertices_584), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_400), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 15 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 18 else
  if p.val = (false, vertices_535) then 19 else
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_419) then 20 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_677) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_580) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 2 26 0 146 1 580 88 152 104 168 552 200 584 208 336 592 400 224 651 279 535 419 357 677
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_4 1 1 2 4 5 8 620 100 1
cert_row_4 2 1 3 5 7 8 852 276 2
cert_row_4 3 3 4 5 6 7 496 208 1
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 602
cert_cover_5 0 0 0 2 3 5 26 602 3
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 620
cert_cover_5 3 1 1 2 4 5 100 620 1
cert_coverFacet 4 852
cert_cover_5 4 2 1 3 5 7 276 852 2
cert_coverFacet 5 216
cert_cover_2 5 3 2 5 6 88 216 3
cert_coverFacet 6 232
cert_cover_2 6 4 2 5 6 104 232 3
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 208 496 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0283

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0284.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0284

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 589, 809, 457, 433, 705, 782, 310, 534, 178, 722, 802, 220, 412, 596, 73, 265, 521, 161, 289, 545, 193, 577, 385, 641, 22, 262, 518, 50, 146, 530, 162, 290, 546, 642, 770, 156, 76, 268, 524, 84, 276, 532, 580, 200, 392, 776, 176, 304, 208, 592, 400, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_589, vertices_809, vertices_457, vertices_433, vertices_705, vertices_782, vertices_310, vertices_534, vertices_178, vertices_722, vertices_802, vertices_220, vertices_412, vertices_596] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_22, vertices_262, vertices_518, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_156, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_580, vertices_200, vertices_392, vertices_776, vertices_176, vertices_304, vertices_208, vertices_592, vertices_400, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_589), (false, vertices_809), (false, vertices_457), (false, vertices_433), (false, vertices_705), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_290), (true, vertices_770), (true, vertices_156), (true, vertices_268), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_156) then 19 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 705 2 22 1 262 3 518 50 146 530 290 770 268 84 276 532 208 592 675 589 156 809 457 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 22 3
cert_row_4 1 0 1 2 7 8 782 262 2
cert_row_2 2 1 2 3 6 156
cert_row_4 3 0 3 5 6 8 722 146 2
cert_rows
cert_pivot_2 4 7 1 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 262 782 2
cert_coverFacet 1 310
cert_cover_5 1 0 0 1 3 4 22 310 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 722
cert_cover_5 4 3 0 3 5 6 146 722 2
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 220
cert_cover_5 6 2 1 2 3 5 156 220 3
cert_coverFacet 7 412
cert_cover_5 7 2 1 2 3 7 156 412 3
cert_coverFacet 8 596
cert_cover_2 8 3 1 5 8 84 596 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0284

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0285.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0285

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 397, 805, 709, 369, 449, 206, 590, 570, 410, 114, 210, 796, 816, 464, 133, 261, 517, 97, 289, 545, 193, 321, 577, 385, 78, 26, 138, 522, 50, 82, 146, 98, 546, 194, 578, 140, 268, 524, 196, 580, 772, 280, 536, 392, 112, 304, 560, 208, 336, 400, 784, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_397, vertices_805, vertices_709, vertices_369, vertices_449, vertices_206, vertices_590, vertices_570, vertices_410, vertices_114, vertices_210, vertices_796, vertices_816, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_78, vertices_26, vertices_138, vertices_522, vertices_50, vertices_82, vertices_146, vertices_98, vertices_546, vertices_194, vertices_578, vertices_140, vertices_268, vertices_524, vertices_196, vertices_580, vertices_772, vertices_280, vertices_536, vertices_392, vertices_112, vertices_304, vertices_560, vertices_208, vertices_336, vertices_400, vertices_784, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_397), (false, vertices_805), (false, vertices_709), (false, vertices_369), (false, vertices_449), (true, vertices_78), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_524), (true, vertices_280), (true, vertices_536), (true, vertices_560), (true, vertices_208), (true, vertices_400), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_784) then 14 else
  0
cert_priority
cert_nodeAtPriority_19 0 449 1 26 138 522 50 82 146 194 524 280 536 560 208 400 784 611 78 397 805 709 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 2 3 4 8 570 26 3
cert_row_4 2 0 2 3 6 7 410 26 3
cert_row_4 3 1 2 3 7 8 796 268 2
cert_rows
cert_pivot_2 5 4 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 6 78 206 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 570
cert_cover_5 2 1 0 2 3 4 26 570 3
cert_coverFacet 3 410
cert_cover_5 3 2 0 2 3 6 26 410 3
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 210
cert_cover_2 5 3 0 5 6 82 210 3
cert_coverFacet 6 796
cert_cover_5 6 3 1 2 3 7 268 796 2
cert_coverFacet 7 816
cert_cover_2 7 4 3 7 8 304 816 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0285

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0286.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0286

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 285, 541, 361, 681, 625, 214, 426, 402, 226, 354, 908, 596, 404, 740, 29, 41, 265, 521, 81, 273, 529, 97, 545, 321, 82, 146, 274, 98, 162, 290, 194, 322, 386, 268, 524, 84, 148, 276, 532, 196, 580, 388, 644, 168, 296, 392, 648, 592, 400, 224, 352, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_285, vertices_541, vertices_361, vertices_681, vertices_625, vertices_214, vertices_426, vertices_402, vertices_226, vertices_354, vertices_908, vertices_596, vertices_404, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_41, vertices_265, vertices_521, vertices_81, vertices_273, vertices_529, vertices_97, vertices_545, vertices_321, vertices_82, vertices_146, vertices_274, vertices_98, vertices_162, vertices_290, vertices_194, vertices_322, vertices_386, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_580, vertices_388, vertices_644, vertices_168, vertices_296, vertices_392, vertices_648, vertices_592, vertices_400, vertices_224, vertices_352, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_285), (false, vertices_541), (false, vertices_361), (false, vertices_681), (false, vertices_625), (true, vertices_146), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_194), (true, vertices_386), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_580), (true, vertices_388), (true, vertices_644), (true, vertices_392), (true, vertices_400), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 16 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 146 1 98 2 162 290 194 386 84 148 196 580 388 644 392 400 224 339 285 541 361 681 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 82 1
cert_row_4 1 0 2 4 6 7 426 162 1
cert_row_4 2 1 2 6 7 8 908 268 2
cert_row_4 3 1 4 5 6 8 740 196 1
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 82 214 1
cert_coverFacet 1 426
cert_cover_5 1 1 0 2 4 6 162 426 1
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 226
cert_cover_2 3 4 0 5 6 98 226 3
cert_coverFacet 4 354
cert_cover_2 4 4 0 5 7 98 354 3
cert_coverFacet 5 908
cert_cover_5 5 2 1 2 6 7 268 908 2
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 740
cert_cover_5 8 3 1 4 5 6 196 740 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0286

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0287.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0287

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 551, 653, 453, 721, 865, 542, 398, 282, 626, 306, 376, 216, 664, 456, 39, 133, 261, 517, 289, 545, 193, 321, 577, 641, 14, 262, 518, 26, 266, 50, 274, 530, 290, 546, 140, 524, 388, 88, 152, 280, 536, 200, 328, 392, 648, 112, 304, 208, 592, 656, 352, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_551, vertices_653, vertices_453, vertices_721, vertices_865, vertices_542, vertices_398, vertices_282, vertices_626, vertices_306, vertices_376, vertices_216, vertices_664, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_39, vertices_133, vertices_261, vertices_517, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_14, vertices_262, vertices_518, vertices_26, vertices_266, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_140, vertices_524, vertices_388, vertices_88, vertices_152, vertices_280, vertices_536, vertices_200, vertices_328, vertices_392, vertices_648, vertices_112, vertices_304, vertices_208, vertices_592, vertices_656, vertices_352, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_551), (false, vertices_653), (false, vertices_453), (false, vertices_721), (false, vertices_865), (true, vertices_14), (true, vertices_26), (true, vertices_266), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_200), (true, vertices_328), (true, vertices_392), (true, vertices_112), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 16 else
  if p.val = (false, vertices_551) then 17 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_304) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_4 1 0 1 2 3 8 542 14 3
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 2 3 4 5 7 376 88 2
cert_rows
cert_pivot_2 6 1 0 2
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 1 0 1 2 3 14 542 3
cert_coverFacet 1 398
cert_cover_5 1 0 0 1 2 6 14 398 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 626
cert_cover_5 3 2 0 3 4 5 50 626 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 88 376 2
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0287

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0288.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0288

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 301, 781, 181, 709, 233, 662, 794, 362, 210, 338, 706, 820, 240, 368, 269, 37, 133, 517, 41, 73, 521, 161, 193, 577, 74, 266, 522, 82, 146, 274, 530, 194, 322, 578, 642, 52, 148, 532, 292, 644, 772, 104, 296, 776, 112, 176, 304, 208, 336, 784, 224, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_301, vertices_781, vertices_181, vertices_709, vertices_233, vertices_662, vertices_794, vertices_362, vertices_210, vertices_338, vertices_706, vertices_820, vertices_240, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_269, vertices_37, vertices_133, vertices_517, vertices_41, vertices_73, vertices_521, vertices_161, vertices_193, vertices_577, vertices_74, vertices_266, vertices_522, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_52, vertices_148, vertices_532, vertices_292, vertices_644, vertices_772, vertices_104, vertices_296, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_336, vertices_784, vertices_224, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_301), (false, vertices_781), (false, vertices_181), (false, vertices_709), (false, vertices_233), (true, vertices_266), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_642), (true, vertices_532), (true, vertices_112), (true, vertices_304), (true, vertices_208), (true, vertices_336), (true, vertices_784), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 21 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 16 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_181) then 22 else
  if p.val = (false, vertices_709) then 23 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 266 2 82 1 146 274 530 194 322 642 532 112 304 208 336 784 352 587 301 781 233 181 709
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_4 1 0 2 4 5 7 362 74 2
cert_row_4 2 0 2 3 7 8 794 266 2
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 6 5 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 794
cert_cover_5 1 2 0 2 3 7 266 794 2
cert_coverFacet 2 362
cert_cover_5 2 1 0 2 4 5 74 362 2
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 820
cert_cover_5 6 3 1 3 4 7 52 820 3
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0288

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0289.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0289

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 419, 643, 589, 457, 721, 310, 242, 658, 786, 796, 236, 428, 116, 596, 131, 259, 515, 73, 265, 521, 193, 577, 385, 641, 50, 146, 274, 530, 162, 290, 642, 770, 172, 76, 268, 524, 52, 84, 276, 532, 100, 292, 580, 200, 392, 776, 112, 208, 592, 656, 784, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_419, vertices_643, vertices_589, vertices_457, vertices_721, vertices_310, vertices_242, vertices_658, vertices_786, vertices_796, vertices_236, vertices_428, vertices_116, vertices_596] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_73, vertices_265, vertices_521, vertices_193, vertices_577, vertices_385, vertices_641, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_642, vertices_770, vertices_172, vertices_76, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_532, vertices_100, vertices_292, vertices_580, vertices_200, vertices_392, vertices_776, vertices_112, vertices_208, vertices_592, vertices_656, vertices_784, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_419), (false, vertices_643), (false, vertices_589), (false, vertices_457), (false, vertices_721), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_172), (true, vertices_268), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_100), (true, vertices_292), (true, vertices_112), (true, vertices_784), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_419) then 17 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_172) then 20 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_172), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 6 242 50 3
cert_row_2 1 1 2 4 6 172
cert_row_4 2 0 1 3 4 7 310 50 1
cert_row_4 3 1 2 3 7 8 796 268 2
cert_rows
cert_pivot_2 5 6 0 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 2 0 1 3 4 50 310 1
cert_coverFacet 1 242
cert_cover_5 1 0 0 3 4 5 50 242 3
cert_coverFacet 2 658
cert_cover_2 2 3 0 6 8 146 658 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 796
cert_cover_5 4 3 1 2 3 7 268 796 2
cert_coverFacet 5 236
cert_cover_5 5 1 1 2 4 5 172 236 3
cert_coverFacet 6 428
cert_cover_5 6 1 1 2 4 7 172 428 3
cert_coverFacet 7 116
cert_cover_2 7 3 1 4 5 52 116 3
cert_coverFacet 8 596
cert_cover_2 8 3 1 5 8 84 596 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0289

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0290.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0290

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 805, 217, 625, 481, 897, 94, 302, 598, 902, 154, 394, 620, 232, 424, 81, 145, 529, 97, 289, 545, 193, 385, 641, 769, 14, 86, 262, 518, 26, 138, 266, 146, 530, 386, 642, 44, 76, 292, 548, 580, 772, 88, 152, 104, 168, 296, 200, 392, 592, 224, 608, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_805, vertices_217, vertices_625, vertices_481, vertices_897, vertices_94, vertices_302, vertices_598, vertices_902, vertices_154, vertices_394, vertices_620, vertices_232, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_86, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_146, vertices_530, vertices_386, vertices_642, vertices_44, vertices_76, vertices_292, vertices_548, vertices_580, vertices_772, vertices_88, vertices_152, vertices_104, vertices_168, vertices_296, vertices_200, vertices_392, vertices_592, vertices_224, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_805), (false, vertices_217), (false, vertices_625), (false, vertices_481), (false, vertices_897), (true, vertices_14), (true, vertices_86), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_386), (true, vertices_44), (true, vertices_76), (true, vertices_580), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_86) then 17 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 897 14 262 518 26 138 266 386 44 76 580 104 168 296 392 659 86 805 217 625 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 1 6 7 8 902 262 2
cert_row_4 2 0 1 2 4 7 302 14 3
cert_row_4 3 1 2 4 5 8 620 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 14 94 3
cert_coverFacet 1 302
cert_cover_5 1 2 0 1 2 4 14 302 3
cert_coverFacet 2 598
cert_cover_5 2 0 0 1 3 8 86 598 3
cert_coverFacet 3 902
cert_cover_5 3 1 0 1 6 7 262 902 2
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 394
cert_cover_2 5 2 0 6 7 138 394 3
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 44 620 3
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0290

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0291.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0291

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 661, 809, 465, 785, 737, 110, 142, 710, 410, 298, 450, 156, 796, 620, 145, 273, 529, 97, 289, 545, 193, 321, 641, 769, 14, 70, 134, 42, 138, 266, 98, 290, 194, 322, 386, 28, 108, 140, 524, 148, 532, 580, 644, 152, 280, 296, 552, 776, 400, 784, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_661, vertices_809, vertices_465, vertices_785, vertices_737, vertices_110, vertices_142, vertices_710, vertices_410, vertices_298, vertices_450, vertices_156, vertices_796, vertices_620] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_70, vertices_134, vertices_42, vertices_138, vertices_266, vertices_98, vertices_290, vertices_194, vertices_322, vertices_386, vertices_28, vertices_108, vertices_140, vertices_524, vertices_148, vertices_532, vertices_580, vertices_644, vertices_152, vertices_280, vertices_296, vertices_552, vertices_776, vertices_400, vertices_784, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_661), (false, vertices_809), (false, vertices_465), (false, vertices_785), (false, vertices_737), (true, vertices_14), (true, vertices_70), (true, vertices_134), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_194), (true, vertices_386), (true, vertices_28), (true, vertices_108), (true, vertices_140), (true, vertices_524), (true, vertices_580), (true, vertices_152), (true, vertices_280)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 16 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_108) then 19 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_580) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_280) then 14 else
  0
cert_priority
cert_nodeAtPriority_9 0 785 1 14 70 134 42 138 266 194 386 28 140 524 580 152 280 355 661 108 809 465 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 1 5 6 8 710 70 3
cert_row_4 2 0 2 3 6 7 410 138 2
cert_row_4 3 1 2 3 7 8 796 28 3
cert_rows
cert_pivot_2 4 5 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 4 14 110 3
cert_coverFacet 1 142
cert_cover_2 1 1 0 2 6 14 142 3
cert_coverFacet 2 710
cert_cover_5 2 1 0 1 5 6 70 710 3
cert_coverFacet 3 410
cert_cover_5 3 2 0 2 3 6 138 410 2
cert_coverFacet 4 298
cert_cover_2 4 2 0 4 7 42 298 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 156
cert_cover_2 6 2 1 3 6 28 156 3
cert_coverFacet 7 796
cert_cover_5 7 3 1 2 3 7 28 796 3
cert_coverFacet 8 620
cert_cover_5 8 0 1 2 4 8 108 620 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0291

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0292.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0292

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 541, 153, 425, 241, 817, 334, 590, 626, 354, 802, 156, 396, 724, 484, 25, 137, 265, 521, 49, 145, 529, 161, 289, 769, 78, 266, 522, 98, 290, 546, 322, 578, 770, 28, 140, 268, 524, 148, 532, 196, 324, 580, 388, 152, 392, 112, 560, 208, 592, 224, 352, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_541, vertices_153, vertices_425, vertices_241, vertices_817, vertices_334, vertices_590, vertices_626, vertices_354, vertices_802, vertices_156, vertices_396, vertices_724, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_529, vertices_161, vertices_289, vertices_769, vertices_78, vertices_266, vertices_522, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_140, vertices_268, vertices_524, vertices_148, vertices_532, vertices_196, vertices_324, vertices_580, vertices_388, vertices_152, vertices_392, vertices_112, vertices_560, vertices_208, vertices_592, vertices_224, vertices_352, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_541), (false, vertices_153), (false, vertices_425), (false, vertices_241), (false, vertices_817), (true, vertices_78), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_578), (true, vertices_140), (true, vertices_268), (true, vertices_148), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_388), (true, vertices_592), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_153) then 0 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
cert_nodeAtPriority_40 153 98 290 546 322 578 140 268 148 196 324 580 388 592 352 779 78 541 425 241 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 3 4 5 8 626 98 1
cert_row_4 2 1 3 5 6 8 724 148 2
cert_row_4 3 1 4 5 6 7 484 196 1
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 7 78 334 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 626
cert_cover_5 2 1 0 3 4 5 98 626 1
cert_coverFacet 3 354
cert_cover_2 3 4 0 5 7 98 354 3
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 724
cert_cover_5 7 2 1 3 5 6 148 724 2
cert_coverFacet 8 484
cert_cover_5 8 3 1 4 5 6 196 484 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0292

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0293.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0293

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [227, 541, 153, 713, 625, 433, 206, 334, 406, 354, 418, 156, 780, 820, 872, 25, 137, 521, 49, 145, 529, 97, 161, 193, 577, 78, 134, 262, 98, 162, 290, 194, 322, 386, 28, 140, 268, 524, 148, 276, 532, 772, 152, 200, 328, 584, 776, 304, 560, 400, 352, 608, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_541, vertices_153, vertices_713, vertices_625, vertices_433, vertices_206, vertices_334, vertices_406, vertices_354, vertices_418, vertices_156, vertices_780, vertices_820, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_521, vertices_49, vertices_145, vertices_529, vertices_97, vertices_161, vertices_193, vertices_577, vertices_78, vertices_134, vertices_262, vertices_98, vertices_162, vertices_290, vertices_194, vertices_322, vertices_386, vertices_28, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_772, vertices_152, vertices_200, vertices_328, vertices_584, vertices_776, vertices_304, vertices_560, vertices_400, vertices_352, vertices_608, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_541), (false, vertices_153), (false, vertices_713), (false, vertices_625), (false, vertices_433), (true, vertices_78), (true, vertices_134), (true, vertices_262), (true, vertices_290), (true, vertices_322), (true, vertices_386), (true, vertices_140), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_772), (true, vertices_328), (true, vertices_776), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 16 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_153) then 0 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
cert_nodeAtPriority_40 153 134 262 290 322 386 140 268 148 276 772 328 776 352 800 227 78 541 713 625 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 7 406 134 2
cert_row_2 1 0 1 2 5 78
cert_row_4 2 1 3 4 7 8 820 276 2
cert_row_4 3 2 4 5 7 8 872 328 1
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 6 78 206 3
cert_coverFacet 1 334
cert_cover_5 1 1 0 1 2 7 78 334 3
cert_coverFacet 2 406
cert_cover_5 2 0 0 1 3 6 134 406 2
cert_coverFacet 3 354
cert_cover_2 3 4 0 5 7 98 354 3
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 820
cert_cover_5 7 2 1 3 4 7 276 820 2
cert_coverFacet 8 872
cert_cover_5 8 3 2 4 5 7 328 872 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0293

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0294.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0294

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 61, 665, 361, 201, 625, 206, 334, 406, 866, 898, 156, 300, 308, 944, 25, 41, 73, 137, 49, 529, 97, 193, 577, 641, 78, 134, 262, 194, 322, 578, 386, 642, 770, 28, 44, 140, 268, 52, 148, 276, 292, 152, 296, 200, 328, 304, 560, 400, 656, 352, 608, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_61, vertices_665, vertices_361, vertices_201, vertices_625, vertices_206, vertices_334, vertices_406, vertices_866, vertices_898, vertices_156, vertices_300, vertices_308, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_73, vertices_137, vertices_49, vertices_529, vertices_97, vertices_193, vertices_577, vertices_641, vertices_78, vertices_134, vertices_262, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_140, vertices_268, vertices_52, vertices_148, vertices_276, vertices_292, vertices_152, vertices_296, vertices_200, vertices_328, vertices_304, vertices_560, vertices_400, vertices_656, vertices_352, vertices_608, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_61), (false, vertices_665), (false, vertices_361), (false, vertices_201), (false, vertices_625), (true, vertices_78), (true, vertices_134), (true, vertices_262), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_292), (true, vertices_304), (true, vertices_400), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_61) then 19 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_800) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 201 134 262 322 386 770 140 268 148 276 292 304 400 800 896 707 78 61 665 361 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 1 3 6 7 406 134 2
cert_row_4 2 0 4 5 7 8 866 322 1
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 6 78 206 3
cert_coverFacet 1 334
cert_cover_5 1 0 0 1 2 7 78 334 3
cert_coverFacet 2 406
cert_cover_5 2 1 0 1 3 6 134 406 2
cert_coverFacet 3 866
cert_cover_5 3 2 0 4 5 7 322 866 1
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coverFacet 8 944
cert_cover_5 8 3 3 4 6 7 304 944 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0294

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0295.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0295

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 333, 597, 901, 433, 337, 398, 654, 570, 362, 178, 418, 620, 368, 624, 69, 261, 517, 81, 145, 273, 529, 321, 385, 641, 142, 42, 266, 522, 50, 146, 530, 162, 290, 386, 642, 76, 268, 524, 580, 388, 644, 104, 552, 328, 112, 176, 304, 560, 336, 592, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_333, vertices_597, vertices_901, vertices_433, vertices_337, vertices_398, vertices_654, vertices_570, vertices_362, vertices_178, vertices_418, vertices_620, vertices_368, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_81, vertices_145, vertices_273, vertices_529, vertices_321, vertices_385, vertices_641, vertices_142, vertices_42, vertices_266, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_386, vertices_642, vertices_76, vertices_268, vertices_524, vertices_580, vertices_388, vertices_644, vertices_104, vertices_552, vertices_328, vertices_112, vertices_176, vertices_304, vertices_560, vertices_336, vertices_592, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_333), (false, vertices_597), (false, vertices_901), (false, vertices_433), (false, vertices_337), (true, vertices_142), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_524), (true, vertices_104), (true, vertices_552), (true, vertices_112), (true, vertices_560), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_901) then 21 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (true, vertices_142) then 17 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
cert_nodeAtPriority_19 0 337 1 42 266 522 50 162 290 386 524 104 552 112 560 352 608 659 142 333 597 901 433
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
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 76 620 2
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coverFacet 8 624
cert_cover_2 8 4 3 5 8 112 624 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0295

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0296.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0296

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 173, 653, 357, 313, 841, 662, 198, 794, 370, 210, 834, 228, 696, 240, 141, 37, 69, 517, 41, 265, 521, 289, 321, 577, 70, 134, 518, 82, 146, 274, 530, 194, 322, 578, 770, 100, 164, 196, 644, 56, 280, 536, 168, 648, 776, 112, 176, 304, 208, 656, 224, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_173, vertices_653, vertices_357, vertices_313, vertices_841, vertices_662, vertices_198, vertices_794, vertices_370, vertices_210, vertices_834, vertices_228, vertices_696, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_141, vertices_37, vertices_69, vertices_517, vertices_41, vertices_265, vertices_521, vertices_289, vertices_321, vertices_577, vertices_70, vertices_134, vertices_518, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_770, vertices_100, vertices_164, vertices_196, vertices_644, vertices_56, vertices_280, vertices_536, vertices_168, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_656, vertices_224, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_173), (false, vertices_653), (false, vertices_357), (false, vertices_313), (false, vertices_841), (true, vertices_134), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_770), (true, vertices_196), (true, vertices_536), (true, vertices_112), (true, vertices_176), (true, vertices_208), (true, vertices_656), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 16 else
  if p.val = (false, vertices_173) then 18 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_841) then 23 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 134 1 82 2 146 274 530 194 322 770 196 536 112 176 208 656 224 583 173 653 357 313 841
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 134 2
cert_row_4 1 0 3 4 5 7 370 82 2
cert_row_4 2 0 2 3 7 8 794 274 1
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 134 662 2
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 794
cert_cover_5 2 2 0 2 3 7 274 794 1
cert_coverFacet 3 370
cert_cover_5 3 1 0 3 4 5 82 370 2
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 696
cert_cover_5 7 3 2 3 4 6 56 696 3
cert_coverFacet 8 240
cert_cover_2 8 4 3 5 6 112 240 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0296

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0297.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0297

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [211, 61, 93, 805, 709, 689, 838, 410, 338, 930, 706, 364, 184, 344, 424, 29, 37, 69, 517, 49, 81, 145, 545, 193, 641, 82, 146, 274, 194, 322, 578, 386, 642, 770, 44, 76, 292, 324, 580, 772, 56, 88, 152, 280, 168, 296, 328, 392, 176, 336, 416, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_61, vertices_93, vertices_805, vertices_709, vertices_689, vertices_838, vertices_410, vertices_338, vertices_930, vertices_706, vertices_364, vertices_184, vertices_344, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_37, vertices_69, vertices_517, vertices_49, vertices_81, vertices_145, vertices_545, vertices_193, vertices_641, vertices_82, vertices_146, vertices_274, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_292, vertices_324, vertices_580, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_168, vertices_296, vertices_328, vertices_392, vertices_176, vertices_336, vertices_416, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_61), (false, vertices_93), (false, vertices_805), (false, vertices_709), (false, vertices_689), (true, vertices_274), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_324), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_336), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 16 else
  if p.val = (false, vertices_61) then 18 else
  if p.val = (false, vertices_93) then 19 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 274 2 322 1 578 386 642 770 324 152 280 168 296 328 392 336 416 211 61 93 805 709 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 146 1
cert_row_4 1 0 4 6 7 8 930 386 1
cert_row_4 2 0 1 5 7 8 838 322 1
cert_row_4 3 1 2 4 5 7 364 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 2 0 1 5 7 322 838 1
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 6 146 410 1
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 930
cert_cover_5 3 1 0 4 6 7 386 930 1
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 364
cert_cover_5 5 3 1 2 4 5 44 364 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0297

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0298.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0298

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 775, 203, 659, 681, 841, 566, 86, 210, 812, 436, 340, 472, 424, 688, 263, 67, 131, 515, 73, 137, 521, 321, 641, 769, 22, 70, 518, 82, 146, 530, 194, 52, 84, 276, 292, 548, 324, 772, 168, 296, 552, 200, 328, 392, 776, 176, 560, 208, 336, 400, 656, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_775, vertices_203, vertices_659, vertices_681, vertices_841, vertices_566, vertices_86, vertices_210, vertices_812, vertices_436, vertices_340, vertices_472, vertices_424, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_263, vertices_67, vertices_131, vertices_515, vertices_73, vertices_137, vertices_521, vertices_321, vertices_641, vertices_769, vertices_22, vertices_70, vertices_518, vertices_82, vertices_146, vertices_530, vertices_194, vertices_52, vertices_84, vertices_276, vertices_292, vertices_548, vertices_324, vertices_772, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_392, vertices_776, vertices_176, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_775), (false, vertices_203), (false, vertices_659), (false, vertices_681), (false, vertices_841), (true, vertices_22), (true, vertices_82), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_292), (true, vertices_548), (true, vertices_296), (true, vertices_392), (true, vertices_176), (true, vertices_560), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 15 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 16 else
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_203) then 19 else
  if p.val = (false, vertices_659) then 20 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_841) then 23 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 22 3
cert_row_4 1 1 2 4 7 8 812 292 1
cert_row_4 2 1 3 4 6 7 436 52 3
cert_row_4 3 2 3 5 6 7 472 200 1
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 22 566 3
cert_coverFacet 1 86
cert_cover_2 1 1 0 3 5 22 86 3
cert_coverFacet 2 210
cert_cover_2 2 3 0 5 6 82 210 3
cert_coverFacet 3 812
cert_cover_5 3 1 1 2 4 7 292 812 1
cert_coverFacet 4 436
cert_cover_5 4 2 1 3 4 6 52 436 3
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 472
cert_cover_5 6 3 2 3 5 6 200 472 1
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0298

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0299.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0299

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 357, 457, 777, 817, 737, 158, 566, 614, 198, 794, 706, 308, 468, 408, 137, 265, 521, 97, 289, 545, 193, 321, 641, 769, 22, 550, 70, 134, 26, 138, 522, 530, 194, 578, 642, 52, 148, 276, 100, 292, 196, 324, 152, 280, 392, 776, 304, 560, 400, 784, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_357, vertices_457, vertices_777, vertices_817, vertices_737, vertices_158, vertices_566, vertices_614, vertices_198, vertices_794, vertices_706, vertices_308, vertices_468, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_550, vertices_70, vertices_134, vertices_26, vertices_138, vertices_522, vertices_530, vertices_194, vertices_578, vertices_642, vertices_52, vertices_148, vertices_276, vertices_100, vertices_292, vertices_196, vertices_324, vertices_152, vertices_280, vertices_392, vertices_776, vertices_304, vertices_560, vertices_400, vertices_784, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_357), (false, vertices_457), (false, vertices_777), (false, vertices_817), (false, vertices_737), (true, vertices_22), (true, vertices_550), (true, vertices_70), (true, vertices_134), (true, vertices_26), (true, vertices_530), (true, vertices_194), (true, vertices_578), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_196), (true, vertices_152), (true, vertices_280), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_550) then 17 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 777 22 70 134 26 530 194 578 52 148 276 196 152 280 400 651 550 357 457 817 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 8 550
cert_row_4 1 0 2 3 7 8 794 26 3
cert_row_4 2 0 1 2 3 6 158 22 2
cert_row_4 3 1 3 5 6 7 468 148 2
cert_rows
cert_pivot_2 4 8 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 2 0 1 2 3 22 158 2
cert_coverFacet 1 566
cert_cover_5 1 0 0 1 3 4 22 566 3
cert_coverFacet 2 614
cert_cover_5 2 0 0 1 4 5 550 614 3
cert_coverFacet 3 198
cert_cover_2 3 1 0 5 6 70 198 3
cert_coverFacet 4 794
cert_cover_5 4 1 0 2 3 7 26 794 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 468
cert_cover_5 7 3 1 3 5 6 148 468 2
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0299

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0300.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0300

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 803, 707, 117, 613, 313, 654, 394, 778, 450, 60, 156, 812, 724, 472, 67, 259, 515, 101, 49, 81, 273, 289, 545, 577, 138, 266, 522, 194, 322, 386, 642, 770, 28, 44, 140, 524, 52, 84, 148, 548, 580, 644, 56, 152, 280, 296, 392, 776, 208, 336, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_803, vertices_707, vertices_117, vertices_613, vertices_313, vertices_654, vertices_394, vertices_778, vertices_450, vertices_60, vertices_156, vertices_812, vertices_724, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_101, vertices_49, vertices_81, vertices_273, vertices_289, vertices_545, vertices_577, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_140, vertices_524, vertices_52, vertices_84, vertices_148, vertices_548, vertices_580, vertices_644, vertices_56, vertices_152, vertices_280, vertices_296, vertices_392, vertices_776, vertices_208, vertices_336, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_803), (false, vertices_707), (false, vertices_117), (false, vertices_613), (false, vertices_313), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_386), (true, vertices_28), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_148), (true, vertices_644), (true, vertices_152), (true, vertices_392), (true, vertices_776), (true, vertices_208), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 16 else
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_117) then 20 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_313) then 23 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 2 3 5 6 7 472 152 2
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 450
cert_cover_2 3 5 0 6 7 194 450 3
cert_coverFacet 4 60
cert_cover_2 4 2 1 3 4 28 60 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 812
cert_cover_5 6 1 1 2 4 7 44 812 3
cert_coverFacet 7 724
cert_cover_5 7 2 1 3 5 6 84 724 3
cert_coverFacet 8 472
cert_cover_5 8 3 2 3 5 6 152 472 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0300

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0301.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0301

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 333, 789, 613, 465, 705, 302, 806, 154, 794, 170, 738, 236, 408, 456, 69, 261, 517, 145, 273, 529, 193, 321, 577, 641, 294, 26, 42, 138, 266, 146, 530, 162, 546, 642, 770, 44, 76, 268, 100, 548, 772, 152, 280, 168, 200, 328, 392, 400, 784, 224, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_333, vertices_789, vertices_613, vertices_465, vertices_705, vertices_302, vertices_806, vertices_154, vertices_794, vertices_170, vertices_738, vertices_236, vertices_408, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_294, vertices_26, vertices_42, vertices_138, vertices_266, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_770, vertices_44, vertices_76, vertices_268, vertices_100, vertices_548, vertices_772, vertices_152, vertices_280, vertices_168, vertices_200, vertices_328, vertices_392, vertices_400, vertices_784, vertices_224, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_333), (false, vertices_789), (false, vertices_613), (false, vertices_465), (false, vertices_705), (true, vertices_294), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_162), (true, vertices_546), (true, vertices_770), (true, vertices_44), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_200), (true, vertices_392), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_294) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
cert_nodeAtPriority_19 0 705 1 26 42 138 266 162 546 770 44 152 280 168 200 392 224 659 294 333 789 613 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 7 8 794 26 3
cert_row_2 1 0 1 4 7 294
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 1 2 4 5 6 236 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 1 0 1 2 4 294 302 2
cert_coverFacet 1 806
cert_cover_5 1 1 0 1 4 8 294 806 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 794
cert_cover_5 3 0 0 2 3 7 26 794 3
cert_coverFacet 4 170
cert_cover_2 4 2 0 4 6 42 170 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 162 738 2
cert_coverFacet 6 236
cert_cover_5 6 3 1 2 4 5 44 236 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0301

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0302.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0302

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [227, 789, 681, 465, 657, 865, 286, 110, 838, 170, 394, 450, 668, 620, 408, 145, 273, 529, 97, 161, 545, 193, 321, 641, 769, 14, 70, 262, 42, 138, 266, 98, 162, 194, 322, 386, 28, 108, 524, 276, 532, 580, 772, 152, 280, 168, 552, 392, 648, 400, 656, 608, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_789, vertices_681, vertices_465, vertices_657, vertices_865, vertices_286, vertices_110, vertices_838, vertices_170, vertices_394, vertices_450, vertices_668, vertices_620, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_70, vertices_262, vertices_42, vertices_138, vertices_266, vertices_98, vertices_162, vertices_194, vertices_322, vertices_386, vertices_28, vertices_108, vertices_524, vertices_276, vertices_532, vertices_580, vertices_772, vertices_152, vertices_280, vertices_168, vertices_552, vertices_392, vertices_648, vertices_400, vertices_656, vertices_608, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_789), (false, vertices_681), (false, vertices_465), (false, vertices_657), (false, vertices_865), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_322), (true, vertices_386), (true, vertices_28), (true, vertices_108), (true, vertices_524), (true, vertices_580), (true, vertices_152), (true, vertices_280), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 16 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_108) then 19 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
cert_nodeAtPriority_9 0 657 1 14 70 262 42 138 266 322 386 28 524 580 152 280 392 227 789 108 681 465 865
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 1 5 7 8 838 70 3
cert_row_4 2 0 1 2 3 7 286 14 3
cert_row_4 3 1 2 3 6 8 668 28 3
cert_rows
cert_pivot_2 4 5 0 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 2 0 1 2 3 14 286 3
cert_coverFacet 1 110
cert_cover_5 1 0 0 1 2 4 14 110 3
cert_coverFacet 2 838
cert_cover_5 2 1 0 1 5 7 70 838 3
cert_coverFacet 3 170
cert_cover_2 3 2 0 4 6 42 170 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 668
cert_cover_5 6 3 1 2 3 6 28 668 3
cert_coverFacet 7 620
cert_cover_5 7 0 1 2 4 8 108 620 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0302

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2883 : Certifies 2883 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0273.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2884 : Certifies 2884 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0274.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2885 : Certifies 2885 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0275.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2886 : Certifies 2886 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0276.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2887 : Certifies 2887 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0277.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2888 : Certifies 2888 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0278.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2889 : Certifies 2889 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0279.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2890 : Certifies 2890 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0280.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2891 : Certifies 2891 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0281.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2892 : Certifies 2892 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0282.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2893 : Certifies 2893 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0283.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2894 : Certifies 2894 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0284.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2895 : Certifies 2895 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0285.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2896 : Certifies 2896 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0286.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2897 : Certifies 2897 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0287.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2898 : Certifies 2898 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0288.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2899 : Certifies 2899 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0289.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2900 : Certifies 2900 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0290.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2901 : Certifies 2901 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0291.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2902 : Certifies 2902 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0292.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2903 : Certifies 2903 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0293.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2904 : Certifies 2904 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0294.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2905 : Certifies 2905 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0295.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2906 : Certifies 2906 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0296.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2907 : Certifies 2907 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0297.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2908 : Certifies 2908 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0298.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2909 : Certifies 2909 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0299.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2910 : Certifies 2910 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0300.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2911 : Certifies 2911 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0301.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2912 : Certifies 2912 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0302.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B095 (j : Fin 30) :
    Certifies (2883 + j.val) := by
  fin_cases j
  · exact projection_2883
  · exact projection_2884
  · exact projection_2885
  · exact projection_2886
  · exact projection_2887
  · exact projection_2888
  · exact projection_2889
  · exact projection_2890
  · exact projection_2891
  · exact projection_2892
  · exact projection_2893
  · exact projection_2894
  · exact projection_2895
  · exact projection_2896
  · exact projection_2897
  · exact projection_2898
  · exact projection_2899
  · exact projection_2900
  · exact projection_2901
  · exact projection_2902
  · exact projection_2903
  · exact projection_2904
  · exact projection_2905
  · exact projection_2906
  · exact projection_2907
  · exact projection_2908
  · exact projection_2909
  · exact projection_2910
  · exact projection_2911
  · exact projection_2912

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
