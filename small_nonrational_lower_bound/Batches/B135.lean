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
/- Source: ProjectionCertificates/R_m16e10q1_0193.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0193

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 653, 421, 837, 409, 329, 566, 662, 122, 154, 650, 866, 180, 804, 344, 496, 133, 261, 517, 73, 137, 265, 521, 321, 577, 385, 534, 26, 74, 138, 522, 50, 146, 98, 546, 578, 642, 52, 148, 164, 292, 548, 644, 772, 88, 152, 280, 328, 648, 112, 176, 336, 400, 352, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_653, vertices_421, vertices_837, vertices_409, vertices_329, vertices_566, vertices_662, vertices_122, vertices_154, vertices_650, vertices_866, vertices_180, vertices_804, vertices_344, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_521, vertices_321, vertices_577, vertices_385, vertices_534, vertices_26, vertices_74, vertices_138, vertices_522, vertices_50, vertices_146, vertices_98, vertices_546, vertices_578, vertices_642, vertices_52, vertices_148, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_328, vertices_648, vertices_112, vertices_176, vertices_336, vertices_400, vertices_352, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_653), (false, vertices_421), (false, vertices_837), (false, vertices_409), (false, vertices_329), (true, vertices_534), (true, vertices_26), (true, vertices_138), (true, vertices_50), (true, vertices_146), (true, vertices_98), (true, vertices_546), (true, vertices_642), (true, vertices_52), (true, vertices_148), (true, vertices_548), (true, vertices_88), (true, vertices_112), (true, vertices_176), (true, vertices_336), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 18 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_421) then 22 else
  if p.val = (false, vertices_837) then 23 else
  if p.val = (false, vertices_409) then 25 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (true, vertices_534) then 19 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_352) then 15 else
  if p.val = (true, vertices_800) then 16 else
  0
cert_priority
cert_nodeAtPriority_63 329 26 138 50 146 98 546 642 52 148 548 88 112 176 336 352 800 587 534 653 421 837 409
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 8 534
cert_row_4 1 0 2 3 4 5 122 26 3
cert_row_4 2 0 4 5 7 8 866 98 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 534 566 3
cert_coverFacet 1 662
cert_cover_5 1 0 0 1 3 6 534 662 3
cert_coverFacet 2 122
cert_cover_5 2 1 0 2 3 4 26 122 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 866
cert_cover_5 5 2 0 4 5 7 98 866 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coverFacet 9 496
cert_cover_5 9 3 3 4 5 6 112 496 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0193

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0194.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0194

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 157, 45, 309, 233, 785, 929, 838, 218, 346, 786, 738, 284, 620, 332, 804, 13, 21, 37, 41, 137, 145, 273, 529, 161, 289, 641, 769, 90, 146, 274, 530, 194, 322, 578, 642, 770, 28, 44, 76, 268, 276, 292, 548, 324, 580, 772, 152, 280, 104, 200, 328, 784, 224, 608, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_157, vertices_45, vertices_309, vertices_233, vertices_785, vertices_929, vertices_838, vertices_218, vertices_346, vertices_786, vertices_738, vertices_284, vertices_620, vertices_332, vertices_804] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_37, vertices_41, vertices_137, vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_641, vertices_769, vertices_90, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_44, vertices_76, vertices_268, vertices_276, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_104, vertices_200, vertices_328, vertices_784, vertices_224, vertices_608, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_157), (false, vertices_45), (false, vertices_309), (false, vertices_233), (false, vertices_785), (false, vertices_929), (true, vertices_90), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_76), (true, vertices_268), (true, vertices_548), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_280), (true, vertices_328), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_157) then 20 else
  if p.val = (false, vertices_45) then 0 else
  if p.val = (false, vertices_309) then 21 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_785) then 1 else
  if p.val = (false, vertices_929) then 26 else
  if p.val = (true, vertices_90) then 18 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_328) then 14 else
  if p.val = (true, vertices_608) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 1 45 0 785 274 194 322 578 770 76 268 548 324 580 772 280 328 608 659 90 157 309 233 929
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 1 2 4 5 8 620 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 6 90 218 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 7 90 346 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 194 738 1
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 44 620 3
cert_coverFacet 7 332
cert_cover_2 7 2 1 5 7 76 332 3
cert_coverFacet 8 804
cert_cover_2 8 4 1 7 8 292 804 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0194

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0195.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0195

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 395, 227, 547, 217, 329, 865, 182, 406, 550, 572, 284, 844, 600, 408, 752, 35, 131, 259, 515, 73, 137, 265, 97, 545, 193, 321, 769, 150, 38, 262, 518, 162, 546, 386, 28, 268, 524, 52, 276, 548, 772, 88, 152, 280, 536, 328, 584, 392, 176, 560, 208, 592, 400, 224, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_395, vertices_227, vertices_547, vertices_217, vertices_329, vertices_865, vertices_182, vertices_406, vertices_550, vertices_572, vertices_284, vertices_844, vertices_600, vertices_408, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_73, vertices_137, vertices_265, vertices_97, vertices_545, vertices_193, vertices_321, vertices_769, vertices_150, vertices_38, vertices_262, vertices_518, vertices_162, vertices_546, vertices_386, vertices_28, vertices_268, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_88, vertices_152, vertices_280, vertices_536, vertices_328, vertices_584, vertices_392, vertices_176, vertices_560, vertices_208, vertices_592, vertices_400, vertices_224, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_395), (false, vertices_227), (false, vertices_547), (false, vertices_217), (false, vertices_329), (false, vertices_865), (true, vertices_150), (true, vertices_38), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_276), (true, vertices_548), (true, vertices_280), (true, vertices_536), (true, vertices_584), (true, vertices_176), (true, vertices_560), (true, vertices_592), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 16 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_395) then 20 else
  if p.val = (false, vertices_227) then 21 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_217) then 23 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (false, vertices_865) then 26 else
  if p.val = (true, vertices_150) then 18 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 0 547 1 329 38 28 268 524 52 276 548 280 536 584 176 560 592 400 775 150 395 227 217 865
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 6 150
cert_row_4 1 1 2 5 7 8 844 268 2
cert_row_4 2 1 2 3 4 8 572 28 3
cert_row_4 3 3 4 5 6 8 752 176 2
cert_rows
cert_pivot_2 0 7 1 3
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 4 150 182 3
cert_coverFacet 1 406
cert_cover_5 1 0 0 1 3 7 150 406 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 572
cert_cover_5 3 2 1 2 3 4 28 572 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 844
cert_cover_5 5 1 1 2 5 7 268 844 2
cert_coverFacet 6 600
cert_cover_2 6 3 2 5 8 88 600 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 176 752 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0195

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0196.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0196

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 211, 339, 675, 233, 865, 278, 534, 666, 220, 540, 108, 300, 780, 372, 936, 83, 131, 259, 515, 97, 161, 545, 193, 321, 769, 22, 262, 518, 146, 274, 530, 642, 28, 44, 76, 268, 524, 84, 276, 532, 100, 292, 772, 152, 536, 104, 168, 296, 200, 648, 776, 208, 336, 352, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_211, vertices_339, vertices_675, vertices_233, vertices_865, vertices_278, vertices_534, vertices_666, vertices_220, vertices_540, vertices_108, vertices_300, vertices_780, vertices_372, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_83, vertices_131, vertices_259, vertices_515, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_769, vertices_22, vertices_262, vertices_518, vertices_146, vertices_274, vertices_530, vertices_642, vertices_28, vertices_44, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_100, vertices_292, vertices_772, vertices_152, vertices_536, vertices_104, vertices_168, vertices_296, vertices_200, vertices_648, vertices_776, vertices_208, vertices_336, vertices_352, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_211), (false, vertices_339), (false, vertices_675), (false, vertices_233), (false, vertices_865), (true, vertices_22), (true, vertices_530), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_100), (true, vertices_292), (true, vertices_152), (true, vertices_536), (true, vertices_296), (true, vertices_648), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 17 23 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 18 else
  if p.val = (false, vertices_211) then 20 else
  if p.val = (false, vertices_339) then 21 else
  if p.val = (false, vertices_675) then 22 else
  if p.val = (false, vertices_233) then 24 else
  if p.val = (false, vertices_865) then 27 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_296) then 14 else
  if p.val = (true, vertices_648) then 15 else
  if p.val = (true, vertices_776) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 146 1
cert_row_4 1 2 4 6 7 8 936 168 3
cert_row_4 2 1 2 3 5 6 220 28 3
cert_row_4 3 1 3 4 5 7 372 84 2
cert_rows
cert_pivot_2 0 8 2 1
cert_heightProof 4
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 666
cert_cover_5 2 0 0 2 3 6 146 666 1
cert_coverFacet 3 220
cert_cover_5 3 2 1 2 3 5 28 220 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 372
cert_cover_5 8 3 1 3 4 5 84 372 2
cert_coverFacet 9 936
cert_cover_5 9 1 2 4 6 7 168 936 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0196

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0197.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0197

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 651, 557, 121, 465, 737, 302, 526, 406, 710, 282, 804, 452, 836, 312, 880, 139, 25, 41, 521, 81, 145, 97, 545, 193, 641, 14, 134, 262, 518, 26, 266, 522, 146, 274, 642, 44, 524, 292, 548, 196, 324, 580, 388, 772, 56, 280, 296, 112, 304, 336, 400, 608, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_651, vertices_557, vertices_121, vertices_465, vertices_737, vertices_302, vertices_526, vertices_406, vertices_710, vertices_282, vertices_804, vertices_452, vertices_836, vertices_312, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_139, vertices_25, vertices_41, vertices_521, vertices_81, vertices_145, vertices_97, vertices_545, vertices_193, vertices_641, vertices_14, vertices_134, vertices_262, vertices_518, vertices_26, vertices_266, vertices_522, vertices_146, vertices_274, vertices_642, vertices_44, vertices_524, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_56, vertices_280, vertices_296, vertices_112, vertices_304, vertices_336, vertices_400, vertices_608, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_651), (false, vertices_557), (false, vertices_121), (false, vertices_465), (false, vertices_737), (true, vertices_14), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_274), (true, vertices_292), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_388), (true, vertices_772), (true, vertices_280), (true, vertices_296), (true, vertices_304), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 18 else
  if p.val = (false, vertices_651) then 19 else
  if p.val = (false, vertices_557) then 21 else
  if p.val = (false, vertices_121) then 23 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_800) then 15 else
  if p.val = (true, vertices_832) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 7 302 14 3
cert_row_4 1 3 4 5 7 8 880 112 3
cert_row_4 2 0 1 3 6 7 406 134 2
cert_row_4 3 0 1 5 6 8 710 134 2
cert_rows
cert_pivot_2 2 4 3 0
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 4 14 302 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 406
cert_cover_5 2 2 0 1 3 6 134 406 2
cert_coverFacet 3 710
cert_cover_5 3 3 0 1 5 6 134 710 2
cert_coverFacet 4 282
cert_cover_2 4 2 0 3 7 26 282 3
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 836
cert_cover_2 7 5 1 7 8 324 836 3
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coverFacet 9 880
cert_cover_5 9 1 3 4 5 7 112 880 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0197

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0198.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0198

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 781, 405, 645, 185, 281, 737, 342, 218, 282, 234, 778, 354, 802, 724, 868, 133, 261, 517, 25, 41, 265, 521, 145, 273, 161, 545, 641, 26, 42, 202, 266, 522, 82, 274, 98, 290, 546, 322, 770, 84, 148, 276, 324, 580, 644, 772, 152, 280, 168, 776, 208, 224, 352, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_781, vertices_405, vertices_645, vertices_185, vertices_281, vertices_737, vertices_342, vertices_218, vertices_282, vertices_234, vertices_778, vertices_354, vertices_802, vertices_724, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_41, vertices_265, vertices_521, vertices_145, vertices_273, vertices_161, vertices_545, vertices_641, vertices_26, vertices_42, vertices_202, vertices_266, vertices_522, vertices_82, vertices_274, vertices_98, vertices_290, vertices_546, vertices_322, vertices_770, vertices_84, vertices_148, vertices_276, vertices_324, vertices_580, vertices_644, vertices_772, vertices_152, vertices_280, vertices_168, vertices_776, vertices_208, vertices_224, vertices_352, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_781), (false, vertices_405), (false, vertices_645), (false, vertices_185), (false, vertices_281), (false, vertices_737), (true, vertices_26), (true, vertices_202), (true, vertices_266), (true, vertices_82), (true, vertices_274), (true, vertices_98), (true, vertices_290), (true, vertices_322), (true, vertices_770), (true, vertices_84), (true, vertices_324), (true, vertices_580), (true, vertices_208), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 17 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_405) then 21 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_185) then 23 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_580) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 1 645 0 281 26 266 82 274 98 290 322 770 84 324 580 208 352 800 555 202 781 405 185 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_4 1 0 1 3 5 7 342 82 1
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 1 4 5 7 8 868 324 1
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 1 0 1 3 5 82 342 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 5 26 218 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 234
cert_cover_5 3 0 0 2 4 5 42 234 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 802
cert_cover_2 6 4 0 7 8 290 802 3
cert_coverFacet 7 724
cert_cover_5 7 2 1 3 5 6 84 724 3
cert_coverFacet 8 868
cert_cover_5 8 3 1 4 5 7 324 868 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0198

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0199.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0199

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 587, 659, 323, 149, 789, 865, 362, 394, 650, 428, 628, 180, 804, 248, 728, 67, 131, 259, 515, 21, 133, 261, 145, 529, 321, 577, 769, 74, 138, 266, 522, 322, 386, 642, 52, 148, 532, 164, 292, 548, 388, 772, 216, 104, 168, 296, 584, 392, 648, 112, 176, 592, 656, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_587, vertices_659, vertices_323, vertices_149, vertices_789, vertices_865, vertices_362, vertices_394, vertices_650, vertices_428, vertices_628, vertices_180, vertices_804, vertices_248, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_21, vertices_133, vertices_261, vertices_145, vertices_529, vertices_321, vertices_577, vertices_769, vertices_74, vertices_138, vertices_266, vertices_522, vertices_322, vertices_386, vertices_642, vertices_52, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_216, vertices_104, vertices_168, vertices_296, vertices_584, vertices_392, vertices_648, vertices_112, vertices_176, vertices_592, vertices_656, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_587), (false, vertices_659), (false, vertices_323), (false, vertices_149), (false, vertices_789), (false, vertices_865), (true, vertices_138), (true, vertices_266), (true, vertices_52), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_216), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_648), (true, vertices_112), (true, vertices_176), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 17 else
  if p.val = (false, vertices_587) then 18 else
  if p.val = (false, vertices_659) then 19 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_865) then 26 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_216) then 23 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_592) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 7 362 74 2
cert_row_4 1 1 2 4 6 7 428 164 1
cert_row_2 2 2 3 5 6 216
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 0 7 2 1
cert_heightProof 4
cert_coverFacet 0 362
cert_cover_5 0 0 0 2 4 5 74 362 2
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 428
cert_cover_5 3 1 1 2 4 6 164 428 1
cert_coverFacet 4 628
cert_cover_5 4 3 1 3 4 5 52 628 3
cert_coverFacet 5 180
cert_cover_2 5 3 1 4 6 52 180 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 248
cert_cover_5 7 2 2 3 4 5 216 248 2
cert_coverFacet 8 728
cert_cover_5 8 2 2 3 5 8 216 728 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0199

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0200.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0200

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 595, 309, 613, 453, 217, 401, 806, 58, 90, 298, 714, 778, 908, 708, 440, 531, 37, 69, 261, 49, 81, 145, 273, 545, 193, 577, 385, 26, 42, 74, 266, 522, 50, 82, 290, 546, 578, 770, 292, 548, 196, 580, 388, 644, 772, 56, 88, 152, 296, 200, 392, 648, 776, 304, 400, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_595, vertices_309, vertices_613, vertices_453, vertices_217, vertices_401, vertices_806, vertices_58, vertices_90, vertices_298, vertices_714, vertices_778, vertices_908, vertices_708, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_531, vertices_37, vertices_69, vertices_261, vertices_49, vertices_81, vertices_145, vertices_273, vertices_545, vertices_193, vertices_577, vertices_385, vertices_26, vertices_42, vertices_74, vertices_266, vertices_522, vertices_50, vertices_82, vertices_290, vertices_546, vertices_578, vertices_770, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_296, vertices_200, vertices_392, vertices_648, vertices_776, vertices_304, vertices_400, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_595), (false, vertices_309), (false, vertices_613), (false, vertices_453), (false, vertices_217), (false, vertices_401), (true, vertices_26), (true, vertices_42), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_770), (true, vertices_644), (true, vertices_772), (true, vertices_56), (true, vertices_296), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 17 else
  if p.val = (false, vertices_595) then 18 else
  if p.val = (false, vertices_309) then 20 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_217) then 24 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_776) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 74 3
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 1 2 6 7 8 908 388 1
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 90
cert_cover_2 2 2 0 3 5 26 90 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 714
cert_cover_5 4 0 0 2 5 6 74 714 3
cert_coverFacet 5 778
cert_cover_2 5 2 0 7 8 266 778 3
cert_coverFacet 6 908
cert_cover_5 6 2 1 2 6 7 388 908 1
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coverFacet 8 440
cert_cover_5 8 3 2 3 4 6 56 440 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0200

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0201.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0201

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 165, 805, 709, 457, 433, 542, 566, 90, 714, 370, 802, 188, 652, 344, 408, 37, 133, 517, 161, 289, 193, 321, 577, 385, 769, 534, 26, 74, 522, 50, 82, 290, 546, 322, 578, 770, 28, 140, 524, 52, 164, 548, 644, 88, 152, 280, 200, 328, 392, 648, 176, 304, 336, 400, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_165, vertices_805, vertices_709, vertices_457, vertices_433, vertices_542, vertices_566, vertices_90, vertices_714, vertices_370, vertices_802, vertices_188, vertices_652, vertices_344, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_534, vertices_26, vertices_74, vertices_522, vertices_50, vertices_82, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_140, vertices_524, vertices_52, vertices_164, vertices_548, vertices_644, vertices_88, vertices_152, vertices_280, vertices_200, vertices_328, vertices_392, vertices_648, vertices_176, vertices_304, vertices_336, vertices_400, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_165), (false, vertices_805), (false, vertices_709), (false, vertices_457), (false, vertices_433), (true, vertices_534), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_50), (true, vertices_82), (true, vertices_290), (true, vertices_546), (true, vertices_28), (true, vertices_140), (true, vertices_524), (true, vertices_52), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_648), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (false, vertices_433) then 26 else
  if p.val = (true, vertices_534) then 19 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_52) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_280) then 14 else
  if p.val = (true, vertices_648) then 15 else
  if p.val = (true, vertices_336) then 16 else
  0
cert_priority
cert_nodeAtPriority_14 165 26 74 522 50 82 290 546 28 140 524 52 88 152 280 648 336 835 534 805 709 457 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 7 370 50 3
cert_row_4 1 0 2 5 6 8 714 74 3
cert_row_2 2 0 1 3 8 534
cert_row_4 3 1 2 3 4 6 188 28 3
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 2 0 1 2 3 534 542 2
cert_coverFacet 1 566
cert_cover_5 1 2 0 1 3 4 534 566 3
cert_coverFacet 2 90
cert_cover_2 2 2 0 3 5 26 90 3
cert_coverFacet 3 714
cert_cover_5 3 1 0 2 5 6 74 714 3
cert_coverFacet 4 370
cert_cover_5 4 0 0 3 4 5 50 370 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 188
cert_cover_5 6 3 1 2 3 4 28 188 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coverFacet 9 408
cert_cover_2 9 3 2 6 7 152 408 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0201

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0202.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0202

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 779, 659, 227, 789, 425, 401, 710, 586, 844, 116, 692, 340, 228, 376, 432, 11, 99, 131, 515, 41, 265, 145, 273, 529, 161, 385, 769, 74, 522, 194, 578, 642, 52, 84, 276, 532, 100, 164, 196, 324, 580, 644, 772, 104, 296, 328, 584, 776, 112, 176, 304, 336, 400, 656, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_779, vertices_659, vertices_227, vertices_789, vertices_425, vertices_401, vertices_710, vertices_586, vertices_844, vertices_116, vertices_692, vertices_340, vertices_228, vertices_376, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_99, vertices_131, vertices_515, vertices_41, vertices_265, vertices_145, vertices_273, vertices_529, vertices_161, vertices_385, vertices_769, vertices_74, vertices_522, vertices_194, vertices_578, vertices_642, vertices_52, vertices_84, vertices_276, vertices_532, vertices_100, vertices_164, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_104, vertices_296, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_304, vertices_336, vertices_400, vertices_656, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_779), (false, vertices_659), (false, vertices_227), (false, vertices_789), (false, vertices_425), (false, vertices_401), (true, vertices_578), (true, vertices_52), (true, vertices_84), (true, vertices_100), (true, vertices_164), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_644), (true, vertices_328), (true, vertices_584), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 21 16 18 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 22 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_659) then 23 else
  if p.val = (false, vertices_227) then 24 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_336) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 21 => Sum.inl 0
  | 22 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 8 710 194 1
cert_row_4 1 1 3 4 6 8 692 52 3
cert_row_4 2 1 2 5 7 8 844 324 1
cert_row_4 3 2 3 4 5 7 376 104 1
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 0 0 1 5 6 194 710 1
cert_coverFacet 1 586
cert_cover_2 1 2 0 5 8 74 586 3
cert_coverFacet 2 844
cert_cover_5 2 2 1 2 5 7 324 844 1
cert_coverFacet 3 116
cert_cover_2 3 3 1 4 5 52 116 3
cert_coverFacet 4 692
cert_cover_5 4 1 1 3 4 6 52 692 3
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 376
cert_cover_5 7 3 2 3 4 5 104 376 1
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0202

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0203.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0203

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 301, 789, 165, 601, 281, 681, 230, 358, 774, 714, 850, 184, 312, 216, 496, 37, 133, 261, 517, 25, 41, 265, 521, 273, 529, 161, 641, 102, 134, 262, 518, 194, 322, 578, 642, 770, 164, 292, 772, 56, 88, 152, 280, 168, 296, 200, 584, 648, 176, 304, 208, 336, 592, 784, 224, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_301, vertices_789, vertices_165, vertices_601, vertices_281, vertices_681, vertices_230, vertices_358, vertices_774, vertices_714, vertices_850, vertices_184, vertices_312, vertices_216, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_517, vertices_25, vertices_41, vertices_265, vertices_521, vertices_273, vertices_529, vertices_161, vertices_641, vertices_102, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_164, vertices_292, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_168, vertices_296, vertices_200, vertices_584, vertices_648, vertices_176, vertices_304, vertices_208, vertices_336, vertices_592, vertices_784, vertices_224, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_301), (false, vertices_789), (false, vertices_165), (false, vertices_601), (false, vertices_281), (false, vertices_681), (true, vertices_102), (true, vertices_262), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_56), (true, vertices_152), (true, vertices_200), (true, vertices_176), (true, vertices_304), (true, vertices_208), (true, vertices_336), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 17 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_681) then 24 else
  if p.val = (true, vertices_102) then 18 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_352) then 15 else
  0
cert_priority
cert_nodeAtPriority_39 0 165 1 281 262 194 322 578 770 56 152 200 176 304 208 336 224 352 647 102 301 789 601 681
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 5 102
cert_row_4 1 0 2 5 6 8 714 194 1
cert_row_4 2 0 3 5 7 8 850 322 1
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 0 0 1 4 6 102 230 3
cert_coverFacet 1 358
cert_cover_5 1 0 0 1 4 7 102 358 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 714
cert_cover_5 3 1 0 2 5 6 194 714 1
cert_coverFacet 4 850
cert_cover_5 4 2 0 3 5 7 322 850 1
cert_coverFacet 5 184
cert_cover_2 5 3 2 4 6 56 184 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 176 496 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0203

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0204.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0204

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 405, 229, 325, 345, 537, 713, 422, 314, 570, 402, 738, 844, 612, 804, 808, 69, 133, 261, 25, 73, 521, 145, 273, 529, 193, 321, 641, 58, 146, 274, 530, 162, 290, 546, 386, 642, 100, 164, 292, 548, 324, 580, 388, 772, 280, 536, 296, 552, 328, 584, 776, 400, 224, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_405, vertices_229, vertices_325, vertices_345, vertices_537, vertices_713, vertices_422, vertices_314, vertices_570, vertices_402, vertices_738, vertices_844, vertices_612, vertices_804, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_25, vertices_73, vertices_521, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_641, vertices_58, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_100, vertices_164, vertices_292, vertices_548, vertices_324, vertices_580, vertices_388, vertices_772, vertices_280, vertices_536, vertices_296, vertices_552, vertices_328, vertices_584, vertices_776, vertices_400, vertices_224, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_405), (false, vertices_229), (false, vertices_325), (false, vertices_345), (false, vertices_537), (false, vertices_713), (true, vertices_58), (true, vertices_274), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_292), (true, vertices_548), (true, vertices_580), (true, vertices_772), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_229) then 21 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_345) then 23 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_713) then 24 else
  if p.val = (true, vertices_58) then 18 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_608) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
cert_nodeAtPriority_39 0 325 1 537 274 162 290 546 386 292 548 580 772 296 552 776 608 800 659 58 405 229 345 713
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 4 58
cert_row_4 1 1 2 5 7 8 844 324 1
cert_row_4 2 0 1 4 6 7 422 162 1
cert_row_4 3 0 4 5 6 8 738 162 2
cert_rows
cert_pivot_2 3 2 1 0
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 2 0 1 4 6 162 422 1
cert_coverFacet 1 314
cert_cover_5 1 0 0 2 3 7 58 314 3
cert_coverFacet 2 570
cert_cover_5 2 0 0 2 3 8 58 570 3
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 738
cert_cover_5 4 3 0 4 5 6 162 738 2
cert_coverFacet 5 844
cert_cover_5 5 1 1 2 5 7 324 844 1
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0204

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0205.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0205

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 285, 77, 613, 293, 217, 849, 422, 906, 242, 626, 658, 236, 396, 664, 792, 13, 37, 69, 261, 25, 73, 81, 273, 289, 545, 577, 769, 114, 146, 530, 162, 290, 546, 386, 642, 770, 76, 140, 268, 100, 164, 292, 388, 152, 280, 536, 200, 392, 648, 776, 208, 592, 656, 784, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_285, vertices_77, vertices_613, vertices_293, vertices_217, vertices_849, vertices_422, vertices_906, vertices_242, vertices_626, vertices_658, vertices_236, vertices_396, vertices_664, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_261, vertices_25, vertices_73, vertices_81, vertices_273, vertices_289, vertices_545, vertices_577, vertices_769, vertices_114, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_268, vertices_100, vertices_164, vertices_292, vertices_388, vertices_152, vertices_280, vertices_536, vertices_200, vertices_392, vertices_648, vertices_776, vertices_208, vertices_592, vertices_656, vertices_784, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_285), (false, vertices_77), (false, vertices_613), (false, vertices_293), (false, vertices_217), (false, vertices_849), (true, vertices_114), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_140), (true, vertices_164), (true, vertices_388), (true, vertices_536), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_656), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_285) then 20 else
  if p.val = (false, vertices_77) then 0 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_293) then 1 else
  if p.val = (false, vertices_217) then 23 else
  if p.val = (false, vertices_849) then 25 else
  if p.val = (true, vertices_114) then 18 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_224) then 15 else
  0
cert_priority
cert_nodeAtPriority_50 1 77 0 293 146 530 162 386 642 140 164 388 536 392 648 776 656 224 803 114 285 613 217 849
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 5 114
cert_row_4 1 0 2 6 7 8 906 386 1
cert_row_4 2 0 1 4 6 7 422 162 1
cert_row_4 3 1 2 4 5 6 236 76 2
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 2 0 1 4 6 162 422 1
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 386 906 1
cert_coverFacet 2 242
cert_cover_5 2 0 0 3 4 6 114 242 3
cert_coverFacet 3 626
cert_cover_5 3 0 0 3 4 8 114 626 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 236
cert_cover_5 5 3 1 2 4 5 76 236 2
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coverFacet 8 792
cert_cover_2 8 3 2 7 8 280 792 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0205

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0206.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0206

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 45, 781, 117, 453, 233, 649, 542, 58, 682, 434, 850, 60, 596, 836, 496, 13, 37, 69, 261, 41, 137, 521, 97, 193, 385, 641, 769, 26, 42, 522, 50, 274, 530, 162, 386, 642, 770, 28, 44, 524, 52, 84, 532, 324, 580, 772, 56, 168, 648, 112, 432, 336, 592, 224, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_45, vertices_781, vertices_117, vertices_453, vertices_233, vertices_649, vertices_542, vertices_58, vertices_682, vertices_434, vertices_850, vertices_60, vertices_596, vertices_836, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_261, vertices_41, vertices_137, vertices_521, vertices_97, vertices_193, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_522, vertices_50, vertices_274, vertices_530, vertices_162, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_524, vertices_52, vertices_84, vertices_532, vertices_324, vertices_580, vertices_772, vertices_56, vertices_168, vertices_648, vertices_112, vertices_432, vertices_336, vertices_592, vertices_224, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_45), (false, vertices_781), (false, vertices_117), (false, vertices_453), (false, vertices_233), (false, vertices_649), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_28), (true, vertices_532), (true, vertices_580), (true, vertices_56), (true, vertices_432), (true, vertices_336), (true, vertices_592), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_45) then 0 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_117) then 20 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_649) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_162) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_432) then 25 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_832) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 26 1
cert_row_4 1 0 2 4 6 8 682 42 3
cert_row_2 2 3 4 6 7 432
cert_row_4 3 0 3 5 7 8 850 274 2
cert_rows
cert_pivot_2 1 2 4 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 26 542 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 682
cert_cover_5 2 1 0 2 4 6 42 682 3
cert_coverFacet 3 434
cert_cover_5 3 2 0 3 4 6 50 434 3
cert_coverFacet 4 850
cert_cover_5 4 3 0 3 5 7 274 850 2
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 836
cert_cover_2 7 5 1 7 8 324 836 3
cert_coverFacet 8 496
cert_cover_5 8 2 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0206

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0207.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0207

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 651, 803, 589, 141, 341, 833, 370, 562, 402, 658, 236, 244, 404, 696, 872, 131, 259, 515, 13, 69, 133, 261, 137, 521, 321, 577, 769, 50, 146, 274, 530, 290, 546, 386, 642, 76, 140, 84, 148, 276, 228, 388, 104, 168, 552, 584, 648, 112, 176, 560, 336, 400, 656, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_651, vertices_803, vertices_589, vertices_141, vertices_341, vertices_833, vertices_370, vertices_562, vertices_402, vertices_658, vertices_236, vertices_244, vertices_404, vertices_696, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_13, vertices_69, vertices_133, vertices_261, vertices_137, vertices_521, vertices_321, vertices_577, vertices_769, vertices_50, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_76, vertices_140, vertices_84, vertices_148, vertices_276, vertices_228, vertices_388, vertices_104, vertices_168, vertices_552, vertices_584, vertices_648, vertices_112, vertices_176, vertices_560, vertices_336, vertices_400, vertices_656, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_651), (false, vertices_803), (false, vertices_589), (false, vertices_141), (false, vertices_341), (false, vertices_833), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_148), (true, vertices_228), (true, vertices_104), (true, vertices_168), (true, vertices_552), (true, vertices_112), (true, vertices_176), (true, vertices_560), (true, vertices_400), (true, vertices_656), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 22 20 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 17 else
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_803) then 19 else
  if p.val = (false, vertices_589) then 21 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_341) then 23 else
  if p.val = (false, vertices_833) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_228) then 24 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_352) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_228), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 6 228
cert_row_4 1 0 3 4 5 7 370 50 3
cert_row_4 2 2 3 4 6 8 696 168 1
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 1 0 3 2
cert_heightProof 4
cert_coverFacet 0 370
cert_cover_5 0 1 0 3 4 5 50 370 3
cert_coverFacet 1 562
cert_cover_2 1 3 0 4 8 50 562 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 236
cert_cover_5 4 0 1 2 4 5 76 236 2
cert_coverFacet 5 244
cert_cover_5 5 0 1 3 4 5 84 244 2
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 696
cert_cover_5 7 2 2 3 4 6 168 696 1
cert_coverFacet 8 872
cert_cover_5 8 3 2 4 5 7 104 872 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0207

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0208.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0208

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [115, 291, 579, 899, 309, 713, 465, 302, 618, 778, 668, 236, 780, 244, 788, 912, 35, 67, 259, 515, 49, 81, 273, 289, 193, 577, 385, 641, 42, 266, 522, 98, 290, 578, 770, 44, 140, 268, 524, 52, 148, 276, 532, 228, 292, 772, 104, 200, 584, 648, 776, 112, 208, 400, 656, 784, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_115, vertices_291, vertices_579, vertices_899, vertices_309, vertices_713, vertices_465, vertices_302, vertices_618, vertices_778, vertices_668, vertices_236, vertices_780, vertices_244, vertices_788, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_259, vertices_515, vertices_49, vertices_81, vertices_273, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_42, vertices_266, vertices_522, vertices_98, vertices_290, vertices_578, vertices_770, vertices_44, vertices_140, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_532, vertices_228, vertices_292, vertices_772, vertices_104, vertices_200, vertices_584, vertices_648, vertices_776, vertices_112, vertices_208, vertices_400, vertices_656, vertices_784, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_115), (false, vertices_291), (false, vertices_579), (false, vertices_899), (false, vertices_309), (false, vertices_713), (false, vertices_465), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_532), (true, vertices_228), (true, vertices_772), (true, vertices_104), (true, vertices_776), (true, vertices_656), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_115) then 17 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_579) then 1 else
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_309) then 20 else
  if p.val = (false, vertices_713) then 23 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_228) then 21 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
cert_nodeAtPriority_61 0 291 1 579 42 266 522 44 140 268 524 148 532 772 104 776 656 784 115 899 309 228 713 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 7 302 42 1
cert_row_4 1 0 2 4 5 8 618 42 3
cert_row_2 2 1 4 5 6 228
cert_row_4 3 1 2 3 6 8 668 140 2
cert_rows
cert_pivot_2 7 0 4 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 4 42 302 1
cert_coverFacet 1 618
cert_cover_5 1 1 0 2 4 5 42 618 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 668
cert_cover_5 3 3 1 2 3 6 140 668 2
cert_coverFacet 4 236
cert_cover_5 4 2 1 2 4 5 44 236 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 244
cert_cover_5 6 2 1 3 4 5 52 244 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 912
cert_cover_2 8 6 3 7 8 400 912 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0208

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0209.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0209

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 149, 789, 421, 681, 865, 206, 214, 362, 554, 650, 626, 348, 396, 424, 848, 21, 133, 261, 145, 529, 161, 289, 545, 641, 769, 198, 42, 74, 138, 522, 82, 146, 530, 98, 546, 642, 76, 140, 268, 84, 148, 276, 388, 168, 296, 552, 328, 392, 648, 336, 592, 784, 352, 608, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_149, vertices_789, vertices_421, vertices_681, vertices_865, vertices_206, vertices_214, vertices_362, vertices_554, vertices_650, vertices_626, vertices_348, vertices_396, vertices_424, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_145, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_198, vertices_42, vertices_74, vertices_138, vertices_522, vertices_82, vertices_146, vertices_530, vertices_98, vertices_546, vertices_642, vertices_76, vertices_140, vertices_268, vertices_84, vertices_148, vertices_276, vertices_388, vertices_168, vertices_296, vertices_552, vertices_328, vertices_392, vertices_648, vertices_336, vertices_592, vertices_784, vertices_352, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_149), (false, vertices_789), (false, vertices_421), (false, vertices_681), (false, vertices_865), (true, vertices_198), (true, vertices_42), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_82), (true, vertices_98), (true, vertices_546), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_84), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_336), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 18 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_421) then 22 else
  if p.val = (false, vertices_681) then 24 else
  if p.val = (false, vertices_865) then 27 else
  if p.val = (true, vertices_198) then 19 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_84) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_336) then 15 else
  if p.val = (true, vertices_592) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_198), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_4 1 0 3 4 5 8 626 82 2
cert_row_4 2 0 2 4 5 7 362 42 3
cert_row_4 3 1 2 3 5 7 348 76 2
cert_rows
cert_pivot_2 6 8 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 198 206 2
cert_coverFacet 1 214
cert_cover_5 1 0 0 1 3 5 198 214 2
cert_coverFacet 2 362
cert_cover_5 2 2 0 2 4 5 42 362 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 626
cert_cover_5 5 1 0 3 4 5 82 626 2
cert_coverFacet 6 348
cert_cover_5 6 3 1 2 3 5 76 348 2
cert_coverFacet 7 396
cert_cover_2 7 2 1 6 7 140 396 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coverFacet 9 848
cert_cover_2 9 5 3 7 8 336 848 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0209

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0210.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0210

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 531, 899, 709, 601, 241, 417, 302, 58, 538, 842, 188, 220, 332, 932, 836, 19, 259, 515, 49, 81, 529, 161, 289, 193, 577, 385, 641, 26, 42, 266, 522, 50, 530, 290, 770, 156, 44, 76, 268, 164, 292, 196, 324, 580, 644, 772, 56, 88, 536, 328, 584, 176, 208, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_531, vertices_899, vertices_709, vertices_601, vertices_241, vertices_417, vertices_302, vertices_58, vertices_538, vertices_842, vertices_188, vertices_220, vertices_332, vertices_932, vertices_836] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_259, vertices_515, vertices_49, vertices_81, vertices_529, vertices_161, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_530, vertices_290, vertices_770, vertices_156, vertices_44, vertices_76, vertices_268, vertices_164, vertices_292, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_56, vertices_88, vertices_536, vertices_328, vertices_584, vertices_176, vertices_208, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_531), (false, vertices_899), (false, vertices_709), (false, vertices_601), (false, vertices_241), (false, vertices_417), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_156), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_164), (true, vertices_292), (true, vertices_324), (true, vertices_772), (true, vertices_56), (true, vertices_328), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 17 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (false, vertices_417) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_156) then 21 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_56) then 13 else
  if p.val = (true, vertices_328) then 14 else
  if p.val = (true, vertices_832) then 15 else
  0
cert_priority
cert_nodeAtPriority_61 0 531 1 417 26 42 266 522 44 76 268 164 292 324 772 56 328 832 307 899 709 156 601 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 6 156
cert_row_4 1 0 2 5 7 8 842 266 2
cert_row_4 2 0 1 2 4 7 302 42 1
cert_row_4 3 1 4 6 7 8 932 164 3
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 2 0 1 2 4 42 302 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 842
cert_cover_5 3 1 0 2 5 7 266 842 2
cert_coverFacet 4 188
cert_cover_5 4 0 1 2 3 4 156 188 3
cert_coverFacet 5 220
cert_cover_5 5 0 1 2 3 5 156 220 3
cert_coverFacet 6 332
cert_cover_2 6 2 1 5 7 76 332 3
cert_coverFacet 7 932
cert_cover_5 7 3 1 4 6 7 164 932 3
cert_coverFacet 8 836
cert_cover_2 8 5 1 7 8 324 836 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0210

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0211.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0211

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 405, 677, 837, 665, 614, 58, 538, 682, 370, 834, 460, 228, 376, 408, 232, 133, 261, 517, 145, 273, 529, 641, 769, 26, 42, 522, 50, 274, 530, 98, 546, 322, 578, 770, 100, 164, 548, 196, 324, 580, 388, 56, 152, 280, 536, 104, 168, 200, 328, 392, 648, 368, 400, 224, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_405, vertices_677, vertices_837, vertices_665, vertices_614, vertices_58, vertices_538, vertices_682, vertices_370, vertices_834, vertices_460, vertices_228, vertices_376, vertices_408, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_145, vertices_273, vertices_529, vertices_641, vertices_769, vertices_26, vertices_42, vertices_522, vertices_50, vertices_274, vertices_530, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_100, vertices_164, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_56, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_200, vertices_328, vertices_392, vertices_648, vertices_368, vertices_400, vertices_224, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_405), (false, vertices_677), (false, vertices_837), (false, vertices_665), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_50), (true, vertices_98), (true, vertices_546), (true, vertices_322), (true, vertices_578), (true, vertices_100), (true, vertices_196), (true, vertices_56), (true, vertices_280), (true, vertices_104), (true, vertices_168), (true, vertices_200), (true, vertices_328), (true, vertices_392), (true, vertices_368), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 20 24 26 28 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 19 else
  if p.val = (false, vertices_405) then 21 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_837) then 23 else
  if p.val = (false, vertices_665) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_200) then 14 else
  if p.val = (true, vertices_328) then 15 else
  if p.val = (true, vertices_392) then 16 else
  if p.val = (true, vertices_368) then 27 else
  if p.val = (true, vertices_224) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 24 => Sum.inl 2
  | 25 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inr ⟨(true, vertices_368), by decide +kernel⟩
  | 28 => Sum.inl 4
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 7 368
cert_row_4 1 1 2 5 6 7 460 196 1
cert_row_4 2 0 1 4 5 8 614 98 1
cert_row_4 3 0 2 4 6 8 682 42 3
cert_rows
cert_pivot_2 3 7 1 0
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 2 0 1 4 5 98 614 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 682
cert_cover_5 3 3 0 2 4 6 42 682 3
cert_coverFacet 4 370
cert_cover_5 4 0 0 3 4 5 50 370 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 460
cert_cover_5 6 1 1 2 5 6 196 460 1
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coverFacet 8 376
cert_cover_5 8 0 2 3 4 5 56 376 3
cert_coverFacet 9 408
cert_cover_2 9 3 2 6 7 152 408 3
cert_coverFacet 10 232
cert_cover_2 10 4 2 5 6 104 232 3
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0211

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0212.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0212

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 109, 653, 789, 325, 409, 361, 614, 682, 210, 850, 226, 556, 836, 424, 496, 13, 69, 261, 517, 105, 137, 265, 145, 273, 529, 321, 641, 82, 146, 530, 98, 162, 546, 194, 578, 642, 44, 524, 100, 548, 324, 580, 772, 168, 296, 552, 392, 648, 208, 336, 400, 784, 224, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_109, vertices_653, vertices_789, vertices_325, vertices_409, vertices_361, vertices_614, vertices_682, vertices_210, vertices_850, vertices_226, vertices_556, vertices_836, vertices_424, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_517, vertices_105, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_321, vertices_641, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_44, vertices_524, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_208, vertices_336, vertices_400, vertices_784, vertices_224, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_109), (false, vertices_653), (false, vertices_789), (false, vertices_325), (false, vertices_409), (false, vertices_361), (true, vertices_82), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_578), (true, vertices_548), (true, vertices_580), (true, vertices_168), (true, vertices_552), (true, vertices_208), (true, vertices_336), (true, vertices_224), (true, vertices_416), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_109) then 22 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_409) then 23 else
  if p.val = (false, vertices_361) then 24 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_416) then 14 else
  if p.val = (true, vertices_832) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 8 614 98 1
cert_row_4 1 0 2 4 6 8 682 162 1
cert_row_4 2 0 3 5 7 8 850 82 3
cert_row_4 3 3 4 5 6 7 496 208 1
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 0 0 1 4 5 98 614 1
cert_coverFacet 1 682
cert_cover_5 1 1 0 2 4 6 162 682 1
cert_coverFacet 2 210
cert_cover_2 2 3 0 5 6 82 210 3
cert_coverFacet 3 850
cert_cover_5 3 2 0 3 5 7 82 850 3
cert_coverFacet 4 226
cert_cover_2 4 4 0 5 6 98 226 3
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 836
cert_cover_2 6 5 1 7 8 324 836 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 208 496 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0212

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0213.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0213

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 307, 611, 589, 233, 393, 417, 790, 690, 348, 780, 212, 660, 740, 472, 432, 35, 259, 515, 73, 137, 265, 521, 97, 161, 289, 577, 385, 50, 274, 530, 546, 770, 76, 268, 524, 84, 148, 276, 532, 196, 580, 644, 772, 344, 200, 392, 776, 176, 304, 208, 400, 656, 224, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_307, vertices_611, vertices_589, vertices_233, vertices_393, vertices_417, vertices_790, vertices_690, vertices_348, vertices_780, vertices_212, vertices_660, vertices_740, vertices_472, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_73, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_50, vertices_274, vertices_530, vertices_546, vertices_770, vertices_76, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_580, vertices_644, vertices_772, vertices_344, vertices_200, vertices_392, vertices_776, vertices_176, vertices_304, vertices_208, vertices_400, vertices_656, vertices_224, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_307), (false, vertices_611), (false, vertices_589), (false, vertices_233), (false, vertices_393), (false, vertices_417), (true, vertices_530), (true, vertices_268), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_196), (true, vertices_644), (true, vertices_772), (true, vertices_344), (true, vertices_176), (true, vertices_208), (true, vertices_400), (true, vertices_656), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_307) then 18 else
  if p.val = (false, vertices_611) then 19 else
  if p.val = (false, vertices_589) then 21 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (false, vertices_417) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_344) then 24 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_344), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 5 7 344
cert_row_4 1 0 1 3 7 8 790 274 1
cert_row_4 2 0 3 4 6 8 690 50 3
cert_row_4 3 1 4 5 6 8 740 196 1
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 274 790 1
cert_coverFacet 1 690
cert_cover_5 1 2 0 3 4 6 50 690 3
cert_coverFacet 2 348
cert_cover_5 2 0 1 2 3 5 76 348 2
cert_coverFacet 3 780
cert_cover_2 3 2 1 7 8 268 780 3
cert_coverFacet 4 212
cert_cover_2 4 3 1 5 6 84 212 3
cert_coverFacet 5 660
cert_cover_2 5 3 1 6 8 148 660 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 196 740 1
cert_coverFacet 7 472
cert_cover_5 7 0 2 3 5 6 344 472 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0213

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0214.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0214

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 541, 205, 309, 229, 841, 785, 422, 666, 850, 402, 610, 674, 156, 404, 744, 13, 21, 37, 197, 73, 521, 273, 529, 97, 289, 321, 769, 146, 274, 530, 98, 162, 290, 546, 322, 578, 386, 642, 28, 140, 148, 276, 164, 292, 388, 152, 536, 200, 584, 648, 400, 784, 224, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_541, vertices_205, vertices_309, vertices_229, vertices_841, vertices_785, vertices_422, vertices_666, vertices_850, vertices_402, vertices_610, vertices_674, vertices_156, vertices_404, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_37, vertices_197, vertices_73, vertices_521, vertices_273, vertices_529, vertices_97, vertices_289, vertices_321, vertices_769, vertices_146, vertices_274, vertices_530, vertices_98, vertices_162, vertices_290, vertices_546, vertices_322, vertices_578, vertices_386, vertices_642, vertices_28, vertices_140, vertices_148, vertices_276, vertices_164, vertices_292, vertices_388, vertices_152, vertices_536, vertices_200, vertices_584, vertices_648, vertices_400, vertices_784, vertices_224, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_541), (false, vertices_205), (false, vertices_309), (false, vertices_229), (false, vertices_841), (false, vertices_785), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_388), (true, vertices_152), (true, vertices_648), (true, vertices_400), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 21 18 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 17 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_205) then 22 else
  if p.val = (false, vertices_309) then 23 else
  if p.val = (false, vertices_229) then 24 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_608) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 7 422 162 1
cert_row_4 1 0 3 5 7 8 850 274 2
cert_row_4 2 0 2 3 6 8 666 146 1
cert_row_4 3 2 4 5 6 8 744 200 1
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 162 422 1
cert_coverFacet 1 666
cert_cover_5 1 2 0 2 3 6 146 666 1
cert_coverFacet 2 850
cert_cover_5 2 1 0 3 5 7 274 850 2
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 610
cert_cover_2 4 4 0 5 8 98 610 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 156
cert_cover_2 6 2 1 3 6 28 156 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 744
cert_cover_5 8 3 2 4 5 6 200 744 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0214

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0215.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0215

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 51, 803, 117, 709, 361, 833, 666, 434, 962, 60, 540, 108, 460, 652, 440, 19, 35, 515, 21, 69, 517, 49, 97, 289, 321, 577, 769, 50, 146, 530, 290, 386, 642, 770, 28, 44, 76, 140, 524, 52, 532, 100, 196, 644, 56, 152, 536, 104, 296, 328, 392, 648, 432, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_51, vertices_803, vertices_117, vertices_709, vertices_361, vertices_833, vertices_666, vertices_434, vertices_962, vertices_60, vertices_540, vertices_108, vertices_460, vertices_652, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_515, vertices_21, vertices_69, vertices_517, vertices_49, vertices_97, vertices_289, vertices_321, vertices_577, vertices_769, vertices_50, vertices_146, vertices_530, vertices_290, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_76, vertices_140, vertices_524, vertices_52, vertices_532, vertices_100, vertices_196, vertices_644, vertices_56, vertices_152, vertices_536, vertices_104, vertices_296, vertices_328, vertices_392, vertices_648, vertices_432, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_51), (false, vertices_803), (false, vertices_117), (false, vertices_709), (false, vertices_361), (false, vertices_833), (true, vertices_146), (true, vertices_386), (true, vertices_642), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_392), (true, vertices_648), (true, vertices_432), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 17 else
  if p.val = (false, vertices_51) then 0 else
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_117) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (false, vertices_833) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_432) then 25 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 6 7 432
cert_row_4 1 0 2 3 6 8 666 146 1
cert_row_4 2 0 5 6 7 8 962 386 1
cert_row_4 3 1 2 5 6 7 460 76 3
cert_rows
cert_pivot_2 4 3 0 1
cert_heightProof 4
cert_coverFacet 0 666
cert_cover_5 0 1 0 2 3 6 146 666 1
cert_coverFacet 1 434
cert_cover_5 1 0 0 3 4 6 50 434 3
cert_coverFacet 2 962
cert_cover_5 2 2 0 5 6 7 386 962 1
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 460
cert_cover_5 6 3 1 2 5 6 76 460 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 440
cert_cover_5 8 0 2 3 4 6 56 440 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0215

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0216.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0216

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 597, 617, 689, 465, 353, 158, 526, 678, 410, 362, 554, 284, 844, 340, 660, 81, 145, 529, 97, 161, 289, 545, 321, 577, 385, 14, 134, 518, 154, 42, 266, 522, 162, 290, 546, 386, 28, 268, 524, 84, 148, 276, 532, 324, 580, 644, 280, 104, 552, 328, 584, 336, 400, 656, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_597, vertices_617, vertices_689, vertices_465, vertices_353, vertices_158, vertices_526, vertices_678, vertices_410, vertices_362, vertices_554, vertices_284, vertices_844, vertices_340, vertices_660] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_529, vertices_97, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_14, vertices_134, vertices_518, vertices_154, vertices_42, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_28, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_324, vertices_580, vertices_644, vertices_280, vertices_104, vertices_552, vertices_328, vertices_584, vertices_336, vertices_400, vertices_656, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_597), (false, vertices_617), (false, vertices_689), (false, vertices_465), (false, vertices_353), (true, vertices_14), (true, vertices_134), (true, vertices_518), (true, vertices_154), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_546), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_324), (true, vertices_644), (true, vertices_280), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 18 else
  if p.val = (false, vertices_597) then 21 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_689) then 25 else
  if p.val = (false, vertices_465) then 26 else
  if p.val = (false, vertices_353) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_154) then 19 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_148) then 11 else
  if p.val = (true, vertices_276) then 12 else
  if p.val = (true, vertices_324) then 13 else
  if p.val = (true, vertices_644) then 14 else
  if p.val = (true, vertices_280) then 15 else
  if p.val = (true, vertices_328) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 0 1 4 6 8 678 134 2
cert_row_4 2 0 2 4 5 7 362 42 3
cert_row_4 3 1 2 5 7 8 844 268 2
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 14 158 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 678
cert_cover_5 2 1 0 1 4 6 134 678 2
cert_coverFacet 3 410
cert_cover_5 3 0 0 2 3 7 154 410 3
cert_coverFacet 4 362
cert_cover_5 4 2 0 2 4 5 42 362 3
cert_coverFacet 5 554
cert_cover_2 5 2 0 4 8 42 554 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 844
cert_cover_5 7 3 1 2 5 7 268 844 2
cert_coverFacet 8 340
cert_cover_2 8 3 1 5 7 84 340 3
cert_coverFacet 9 660
cert_cover_2 9 3 1 6 8 148 660 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0216

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0217.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0217

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 331, 787, 675, 565, 433, 449, 654, 778, 236, 588, 372, 596, 676, 856, 480, 75, 131, 259, 515, 49, 273, 529, 161, 545, 193, 321, 385, 138, 266, 522, 642, 770, 76, 140, 524, 52, 84, 532, 100, 164, 548, 580, 644, 200, 328, 584, 776, 304, 336, 592, 784, 224, 352, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_331, vertices_787, vertices_675, vertices_565, vertices_433, vertices_449, vertices_654, vertices_778, vertices_236, vertices_588, vertices_372, vertices_596, vertices_676, vertices_856, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_75, vertices_131, vertices_259, vertices_515, vertices_49, vertices_273, vertices_529, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_138, vertices_266, vertices_522, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_52, vertices_84, vertices_532, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_200, vertices_328, vertices_584, vertices_776, vertices_304, vertices_336, vertices_592, vertices_784, vertices_224, vertices_352, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_331), (false, vertices_787), (false, vertices_675), (false, vertices_565), (false, vertices_433), (false, vertices_449), (true, vertices_522), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_84), (true, vertices_100), (true, vertices_164), (true, vertices_580), (true, vertices_644), (true, vertices_584), (true, vertices_776), (true, vertices_336), (true, vertices_592), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 21 16 18 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 19 else
  if p.val = (false, vertices_331) then 20 else
  if p.val = (false, vertices_787) then 22 else
  if p.val = (false, vertices_675) then 23 else
  if p.val = (false, vertices_565) then 17 else
  if p.val = (false, vertices_433) then 25 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_352) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 21 => Sum.inl 0
  | 22 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_4 1 1 2 4 5 6 236 76 2
cert_row_4 2 1 3 4 5 7 372 52 3
cert_row_4 3 2 3 5 7 8 856 328 1
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 236
cert_cover_5 2 1 1 2 4 5 76 236 2
cert_coverFacet 3 588
cert_cover_2 3 2 1 5 8 76 588 3
cert_coverFacet 4 372
cert_cover_5 4 2 1 3 4 5 52 372 3
cert_coverFacet 5 596
cert_cover_2 5 3 1 5 8 84 596 3
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 856
cert_cover_5 7 3 2 3 5 7 328 856 1
cert_coverFacet 8 480
cert_cover_2 8 5 4 6 7 224 480 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0217

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0218.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0218

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 285, 181, 613, 773, 401, 481, 782, 218, 346, 650, 738, 572, 184, 680, 464, 21, 37, 261, 517, 145, 273, 97, 161, 321, 577, 385, 769, 90, 138, 266, 522, 194, 322, 578, 642, 770, 28, 268, 524, 52, 548, 772, 56, 152, 280, 168, 552, 648, 176, 208, 336, 400, 224, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_285, vertices_181, vertices_613, vertices_773, vertices_401, vertices_481, vertices_782, vertices_218, vertices_346, vertices_650, vertices_738, vertices_572, vertices_184, vertices_680, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_261, vertices_517, vertices_145, vertices_273, vertices_97, vertices_161, vertices_321, vertices_577, vertices_385, vertices_769, vertices_90, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_52, vertices_548, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_552, vertices_648, vertices_176, vertices_208, vertices_336, vertices_400, vertices_224, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_285), (false, vertices_181), (false, vertices_613), (false, vertices_773), (false, vertices_401), (false, vertices_481), (true, vertices_90), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_194), (true, vertices_642), (true, vertices_524), (true, vertices_56), (true, vertices_152), (true, vertices_168), (true, vertices_552), (true, vertices_648), (true, vertices_208), (true, vertices_336), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_285) then 20 else
  if p.val = (false, vertices_181) then 21 else
  if p.val = (false, vertices_613) then 22 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_90) then 18 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 0 4 5 6 8 738 194 1
cert_row_2 2 0 2 3 5 90
cert_row_4 3 1 2 3 4 8 572 28 3
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 218
cert_cover_5 1 2 0 2 3 6 90 218 3
cert_coverFacet 2 346
cert_cover_5 2 2 0 2 3 7 90 346 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 738
cert_cover_5 4 1 0 4 5 6 194 738 1
cert_coverFacet 5 572
cert_cover_5 5 3 1 2 3 4 28 572 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0218

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0219.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0219

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 405, 229, 837, 425, 609, 790, 122, 410, 298, 626, 716, 660, 600, 664, 232, 69, 133, 261, 97, 161, 289, 545, 577, 385, 769, 26, 42, 266, 114, 274, 530, 290, 546, 770, 148, 276, 532, 196, 580, 644, 772, 88, 152, 536, 104, 168, 296, 200, 584, 392, 648, 592, 400, 656, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_405, vertices_229, vertices_837, vertices_425, vertices_609, vertices_790, vertices_122, vertices_410, vertices_298, vertices_626, vertices_716, vertices_660, vertices_600, vertices_664, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_97, vertices_161, vertices_289, vertices_545, vertices_577, vertices_385, vertices_769, vertices_26, vertices_42, vertices_266, vertices_114, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_148, vertices_276, vertices_532, vertices_196, vertices_580, vertices_644, vertices_772, vertices_88, vertices_152, vertices_536, vertices_104, vertices_168, vertices_296, vertices_200, vertices_584, vertices_392, vertices_648, vertices_592, vertices_400, vertices_656, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_405), (false, vertices_229), (false, vertices_837), (false, vertices_425), (false, vertices_609), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_114), (true, vertices_274), (true, vertices_530), (true, vertices_532), (true, vertices_644), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_104), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_405) then 21 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_837) then 23 else
  if p.val = (false, vertices_425) then 25 else
  if p.val = (false, vertices_609) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_114) then 19 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_592) then 15 else
  if p.val = (true, vertices_656) then 16 else
  0
cert_priority
cert_nodeAtPriority_63 609 26 42 266 274 530 532 644 88 152 536 104 200 584 648 592 656 803 114 405 229 837 425
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 5 114
cert_row_4 1 1 2 5 6 8 716 196 1
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 0 2 3 6 7 410 26 3
cert_rows
cert_pivot_2 4 5 1 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 4 26 122 3
cert_coverFacet 2 410
cert_cover_5 2 3 0 2 3 6 26 410 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 626
cert_cover_5 4 0 0 3 4 8 114 626 3
cert_coverFacet 5 716
cert_cover_5 5 1 1 2 5 6 196 716 1
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coverFacet 9 232
cert_cover_2 9 4 2 5 6 104 232 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0219

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0220.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0220

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [103, 167, 659, 835, 197, 793, 465, 618, 674, 108, 300, 844, 436, 452, 696, 312, 39, 67, 131, 515, 69, 133, 145, 273, 529, 193, 321, 769, 98, 162, 546, 578, 642, 44, 76, 268, 100, 164, 292, 196, 324, 388, 56, 280, 536, 104, 296, 552, 584, 776, 176, 304, 400, 656, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_103, vertices_167, vertices_659, vertices_835, vertices_197, vertices_793, vertices_465, vertices_618, vertices_674, vertices_108, vertices_300, vertices_844, vertices_436, vertices_452, vertices_696, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_39, vertices_67, vertices_131, vertices_515, vertices_69, vertices_133, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_769, vertices_98, vertices_162, vertices_546, vertices_578, vertices_642, vertices_44, vertices_76, vertices_268, vertices_100, vertices_164, vertices_292, vertices_196, vertices_324, vertices_388, vertices_56, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_584, vertices_776, vertices_176, vertices_304, vertices_400, vertices_656, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_103), (false, vertices_167), (false, vertices_659), (false, vertices_835), (false, vertices_197), (false, vertices_793), (false, vertices_465), (true, vertices_546), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_292), (true, vertices_324), (true, vertices_388), (true, vertices_56), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_584), (true, vertices_176), (true, vertices_304), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 16 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_103) then 17 else
  if p.val = (false, vertices_167) then 18 else
  if p.val = (false, vertices_659) then 20 else
  if p.val = (false, vertices_835) then 21 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_793) then 23 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_103), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_167), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 8 618 98 1
cert_row_4 1 1 2 5 7 8 844 76 3
cert_row_4 2 1 3 4 6 7 436 164 1
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 618
cert_cover_5 0 0 0 2 4 5 98 618 1
cert_coverFacet 1 674
cert_cover_2 1 4 0 6 8 162 674 3
cert_coverFacet 2 108
cert_cover_2 2 2 1 4 5 44 108 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 844
cert_cover_5 4 1 1 2 5 7 76 844 3
cert_coverFacet 5 436
cert_cover_5 5 2 1 3 4 6 164 436 1
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 696
cert_cover_5 7 3 2 3 4 6 56 696 3
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0220

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0221.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0221

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 61, 781, 613, 169, 393, 481, 790, 218, 346, 658, 738, 284, 692, 184, 456, 13, 37, 517, 41, 137, 265, 97, 161, 321, 577, 385, 769, 90, 146, 274, 530, 194, 322, 578, 642, 770, 28, 268, 52, 276, 532, 548, 772, 56, 152, 280, 168, 200, 328, 392, 176, 656, 224, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_61, vertices_781, vertices_613, vertices_169, vertices_393, vertices_481, vertices_790, vertices_218, vertices_346, vertices_658, vertices_738, vertices_284, vertices_692, vertices_184, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_517, vertices_41, vertices_137, vertices_265, vertices_97, vertices_161, vertices_321, vertices_577, vertices_385, vertices_769, vertices_90, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_268, vertices_52, vertices_276, vertices_532, vertices_548, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_200, vertices_328, vertices_392, vertices_176, vertices_656, vertices_224, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_61), (false, vertices_781), (false, vertices_613), (false, vertices_169), (false, vertices_393), (false, vertices_481), (true, vertices_90), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_642), (true, vertices_276), (true, vertices_532), (true, vertices_152), (true, vertices_280), (true, vertices_200), (true, vertices_328), (true, vertices_176), (true, vertices_656), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_61) then 20 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_613) then 22 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (false, vertices_393) then 1 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_90) then 18 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 3 7 8 790 274 1
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 274 790 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 6 90 218 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 7 90 346 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 194 738 1
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 52 692 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0221

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0222.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0222

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 613, 809, 713, 465, 353, 206, 590, 182, 534, 794, 402, 820, 228, 240, 368, 137, 265, 521, 97, 289, 545, 193, 321, 577, 385, 78, 22, 134, 518, 138, 266, 522, 146, 274, 530, 386, 52, 532, 100, 164, 548, 196, 580, 200, 584, 776, 112, 176, 304, 208, 336, 400, 784, 224, 352, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_613, vertices_809, vertices_713, vertices_465, vertices_353, vertices_206, vertices_590, vertices_182, vertices_534, vertices_794, vertices_402, vertices_820, vertices_228, vertices_240, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_78, vertices_22, vertices_134, vertices_518, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_52, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_200, vertices_584, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_336, vertices_400, vertices_784, vertices_224, vertices_352, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_613), (false, vertices_809), (false, vertices_713), (false, vertices_465), (false, vertices_353), (true, vertices_78), (true, vertices_22), (true, vertices_134), (true, vertices_518), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_52), (true, vertices_532), (true, vertices_164), (true, vertices_196), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_784), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_809) then 23 else
  if p.val = (false, vertices_713) then 24 else
  if p.val = (false, vertices_465) then 26 else
  if p.val = (false, vertices_353) then 0 else
  if p.val = (true, vertices_78) then 19 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_784) then 15 else
  if p.val = (true, vertices_224) then 16 else
  0
cert_priority
cert_nodeAtPriority_33 353 22 134 518 522 146 274 530 52 532 164 196 112 176 304 784 224 395 78 613 809 713 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 1 3 4 6 182 22 3
cert_row_4 2 0 2 3 7 8 794 266 2
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 5 6 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 6 78 206 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 182
cert_cover_5 2 1 0 1 3 4 22 182 3
cert_coverFacet 3 534
cert_cover_2 3 1 0 3 8 22 534 3
cert_coverFacet 4 794
cert_cover_5 4 2 0 2 3 7 266 794 2
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 820
cert_cover_5 6 3 1 3 4 7 52 820 3
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coverFacet 8 240
cert_cover_2 8 4 3 5 6 112 240 3
cert_coverFacet 9 368
cert_cover_2 9 4 3 5 7 112 368 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0222

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_4083 : Certifies 4083 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0193.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4084 : Certifies 4084 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0194.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4085 : Certifies 4085 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0195.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4086 : Certifies 4086 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0196.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4087 : Certifies 4087 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0197.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4088 : Certifies 4088 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0198.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4089 : Certifies 4089 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0199.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4090 : Certifies 4090 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0200.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4091 : Certifies 4091 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0201.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4092 : Certifies 4092 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0202.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4093 : Certifies 4093 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0203.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4094 : Certifies 4094 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0204.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4095 : Certifies 4095 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0205.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4096 : Certifies 4096 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0206.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4097 : Certifies 4097 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0207.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4098 : Certifies 4098 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0208.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4099 : Certifies 4099 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0209.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4100 : Certifies 4100 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0210.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4101 : Certifies 4101 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0211.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4102 : Certifies 4102 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0212.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4103 : Certifies 4103 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0213.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4104 : Certifies 4104 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0214.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4105 : Certifies 4105 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0215.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4106 : Certifies 4106 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0216.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4107 : Certifies 4107 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0217.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4108 : Certifies 4108 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0218.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4109 : Certifies 4109 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0219.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4110 : Certifies 4110 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0220.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4111 : Certifies 4111 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0221.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4112 : Certifies 4112 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0222.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B135 (j : Fin 30) :
    Certifies (4083 + j.val) := by
  fin_cases j
  · exact projection_4083
  · exact projection_4084
  · exact projection_4085
  · exact projection_4086
  · exact projection_4087
  · exact projection_4088
  · exact projection_4089
  · exact projection_4090
  · exact projection_4091
  · exact projection_4092
  · exact projection_4093
  · exact projection_4094
  · exact projection_4095
  · exact projection_4096
  · exact projection_4097
  · exact projection_4098
  · exact projection_4099
  · exact projection_4100
  · exact projection_4101
  · exact projection_4102
  · exact projection_4103
  · exact projection_4104
  · exact projection_4105
  · exact projection_4106
  · exact projection_4107
  · exact projection_4108
  · exact projection_4109
  · exact projection_4110
  · exact projection_4111
  · exact projection_4112

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
