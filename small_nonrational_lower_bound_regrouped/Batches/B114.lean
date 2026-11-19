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
/- Source: ProjectionCertificates/R_m15e10q1_0875.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0875

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 285, 653, 341, 229, 841, 609, 662, 794, 402, 866, 418, 540, 212, 496, 13, 277, 69, 133, 265, 521, 97, 161, 545, 321, 577, 641, 146, 274, 530, 162, 290, 546, 386, 642, 770, 28, 524, 84, 148, 532, 196, 644, 280, 536, 776, 208, 336, 400, 224, 352, 608, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_285, vertices_653, vertices_341, vertices_229, vertices_841, vertices_609, vertices_662, vertices_794, vertices_402, vertices_866, vertices_418, vertices_540, vertices_212, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_277, vertices_69, vertices_133, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_641, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_524, vertices_84, vertices_148, vertices_532, vertices_196, vertices_644, vertices_280, vertices_536, vertices_776, vertices_208, vertices_336, vertices_400, vertices_224, vertices_352, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_285), (false, vertices_653), (false, vertices_341), (false, vertices_229), (false, vertices_841), (false, vertices_609), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_386), (true, vertices_770), (true, vertices_148), (true, vertices_532), (true, vertices_536), (true, vertices_208), (true, vertices_400), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 19 16 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_285) then 20 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_341) then 21 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_841) then 18 else
  if p.val = (false, vertices_609) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
cert_nodeAtPriority_48 0 609 1 146 2 274 530 290 386 770 148 532 536 208 400 352 416 675 653 841 285 341 229
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_4 1 0 2 3 7 8 794 274 1
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 3 4 5 6 7 496 208 1
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 274 794 1
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 866
cert_cover_5 3 2 0 4 5 7 290 866 2
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 208 496 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0875

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0876.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0876

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 837, 713, 689, 481, 566, 342, 774, 58, 346, 426, 604, 184, 664, 456, 161, 289, 545, 193, 321, 577, 641, 769, 22, 262, 518, 26, 42, 266, 50, 338, 290, 546, 770, 84, 532, 324, 580, 772, 56, 88, 152, 536, 168, 200, 328, 584, 392, 648, 176, 560, 656, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_837, vertices_713, vertices_689, vertices_481, vertices_566, vertices_342, vertices_774, vertices_58, vertices_346, vertices_426, vertices_604, vertices_184, vertices_664, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_22, vertices_262, vertices_518, vertices_26, vertices_42, vertices_266, vertices_50, vertices_338, vertices_290, vertices_546, vertices_770, vertices_84, vertices_532, vertices_324, vertices_580, vertices_772, vertices_56, vertices_88, vertices_152, vertices_536, vertices_168, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_176, vertices_560, vertices_656, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_837), (false, vertices_713), (false, vertices_689), (false, vertices_481), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_50), (true, vertices_338), (true, vertices_84), (true, vertices_532), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_168), (true, vertices_328), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_50) then 6 else
  if p.val = (true, vertices_338) then 18 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_328) then 14 else
  if p.val = (true, vertices_392) then 15 else
  0
cert_priority
cert_nodeAtPriority_64 22 262 518 26 42 266 50 84 532 56 88 152 536 168 328 392 803 338 837 713 689 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 42 3
cert_row_2 1 0 3 5 7 338
cert_row_4 2 0 1 3 4 8 566 22 3
cert_row_4 3 1 2 3 5 8 604 84 1
cert_rows
cert_pivot_2 6 7 0 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 2 0 1 3 4 22 566 3
cert_coverFacet 1 342
cert_cover_5 1 1 0 1 3 5 22 342 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 58
cert_cover_2 3 2 0 3 4 26 58 3
cert_coverFacet 4 346
cert_cover_5 4 1 0 2 3 5 26 346 3
cert_coverFacet 5 426
cert_cover_5 5 0 0 2 4 6 42 426 3
cert_coverFacet 6 604
cert_cover_5 6 3 1 2 3 5 84 604 1
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coverFacet 9 456
cert_cover_2 9 5 2 6 7 200 456 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0876

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0877.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0877

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 677, 665, 425, 841, 614, 346, 242, 402, 418, 834, 604, 244, 660, 408, 137, 265, 521, 161, 289, 545, 641, 769, 82, 146, 274, 98, 162, 290, 546, 322, 578, 386, 770, 84, 148, 532, 100, 164, 548, 580, 644, 88, 152, 280, 536, 328, 584, 392, 240, 400, 656, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_677, vertices_665, vertices_425, vertices_841, vertices_614, vertices_346, vertices_242, vertices_402, vertices_418, vertices_834, vertices_604, vertices_244, vertices_660, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_82, vertices_146, vertices_274, vertices_98, vertices_162, vertices_290, vertices_546, vertices_322, vertices_578, vertices_386, vertices_770, vertices_84, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_88, vertices_152, vertices_280, vertices_536, vertices_328, vertices_584, vertices_392, vertices_240, vertices_400, vertices_656, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_677), (false, vertices_665), (false, vertices_425), (false, vertices_841), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_98), (true, vertices_162), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_100), (true, vertices_580), (true, vertices_88), (true, vertices_280), (true, vertices_240), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 20 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_841) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_580) then 12 else
  if p.val = (true, vertices_88) then 13 else
  if p.val = (true, vertices_280) then 14 else
  if p.val = (true, vertices_240) then 25 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
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
cert_row_2 0 3 4 5 6 240
cert_row_4 1 0 1 4 5 8 614 98 1
cert_row_4 2 0 2 3 5 7 346 82 1
cert_row_4 3 1 2 3 5 8 604 84 1
cert_rows
cert_pivot_2 6 4 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 1 0 1 4 5 98 614 1
cert_coverFacet 1 346
cert_cover_5 1 2 0 2 3 5 82 346 1
cert_coverFacet 2 242
cert_cover_5 2 0 0 3 4 5 82 242 2
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 604
cert_cover_5 6 3 1 2 3 5 84 604 1
cert_coverFacet 7 244
cert_cover_5 7 0 1 3 4 5 84 244 2
cert_coverFacet 8 660
cert_cover_2 8 3 1 6 8 148 660 3
cert_coverFacet 9 408
cert_cover_2 9 3 2 6 7 152 408 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0877

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0878.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0878

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 837, 681, 625, 481, 782, 58, 282, 170, 650, 242, 466, 572, 348, 596, 97, 161, 545, 321, 577, 385, 641, 769, 26, 42, 138, 266, 522, 50, 210, 274, 162, 386, 642, 770, 28, 268, 524, 84, 532, 324, 580, 772, 56, 280, 168, 552, 648, 112, 560, 336, 592, 224, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_837, vertices_681, vertices_625, vertices_481, vertices_782, vertices_58, vertices_282, vertices_170, vertices_650, vertices_242, vertices_466, vertices_572, vertices_348, vertices_596] (by decide +kernel)
  polygons := literalFinset [vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_138, vertices_266, vertices_522, vertices_50, vertices_210, vertices_274, vertices_162, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_84, vertices_532, vertices_324, vertices_580, vertices_772, vertices_56, vertices_280, vertices_168, vertices_552, vertices_648, vertices_112, vertices_560, vertices_336, vertices_592, vertices_224, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_837), (false, vertices_681), (false, vertices_625), (false, vertices_481), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_210), (true, vertices_274), (true, vertices_162), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_532), (true, vertices_56), (true, vertices_280), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_210) then 18 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_162) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_84) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_56) then 13 else
  if p.val = (true, vertices_280) then 14 else
  if p.val = (true, vertices_336) then 15 else
  0
cert_priority
cert_nodeAtPriority_64 26 42 138 266 522 50 274 162 28 268 524 84 532 56 280 336 899 210 837 681 625 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 6 210
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 1 2 3 4 8 572 28 3
cert_row_4 3 1 2 3 5 7 348 28 3
cert_rows
cert_pivot_2 6 0 4 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 170
cert_cover_2 3 2 0 4 6 42 170 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 242
cert_cover_5 5 0 0 3 4 5 50 242 3
cert_coverFacet 6 466
cert_cover_5 6 0 0 3 5 7 210 466 3
cert_coverFacet 7 572
cert_cover_5 7 2 1 2 3 4 28 572 3
cert_coverFacet 8 348
cert_cover_5 8 3 1 2 3 5 28 348 3
cert_coverFacet 9 596
cert_cover_2 9 3 1 5 8 84 596 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0878

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0879.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0879

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 613, 601, 361, 905, 678, 410, 242, 370, 898, 668, 212, 596, 228, 344, 73, 265, 521, 97, 289, 545, 577, 769, 114, 146, 274, 162, 290, 546, 386, 642, 770, 84, 148, 532, 100, 164, 548, 196, 580, 644, 88, 152, 280, 536, 328, 392, 648, 208, 336, 592, 224, 352, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_613, vertices_601, vertices_361, vertices_905, vertices_678, vertices_410, vertices_242, vertices_370, vertices_898, vertices_668, vertices_212, vertices_596, vertices_228, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_97, vertices_289, vertices_545, vertices_577, vertices_769, vertices_114, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_84, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_88, vertices_152, vertices_280, vertices_536, vertices_328, vertices_392, vertices_648, vertices_208, vertices_336, vertices_592, vertices_224, vertices_352, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_613), (false, vertices_601), (false, vertices_361), (false, vertices_905), (true, vertices_114), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_164), (true, vertices_196), (true, vertices_644), (true, vertices_152), (true, vertices_280), (true, vertices_208), (true, vertices_336), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_601) then 22 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (false, vertices_905) then 24 else
  if p.val = (true, vertices_114) then 18 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_224) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_114), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 5 114
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 0 2 3 6 7 410 146 1
cert_row_4 3 1 2 3 6 8 668 148 1
cert_rows
cert_pivot_2 5 4 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 410
cert_cover_5 1 2 0 2 3 6 146 410 1
cert_coverFacet 2 242
cert_cover_5 2 0 0 3 4 6 114 242 3
cert_coverFacet 3 370
cert_cover_5 3 0 0 3 4 7 114 370 3
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 668
cert_cover_5 5 3 1 2 3 6 148 668 1
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 228
cert_cover_2 8 4 1 5 6 100 228 3
cert_coverFacet 9 344
cert_cover_2 9 3 2 5 7 88 344 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0879

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0880.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0880

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 91, 539, 451, 421, 709, 585, 370, 786, 684, 820, 120, 568, 488, 712, 27, 67, 259, 515, 133, 261, 517, 73, 521, 193, 577, 385, 82, 274, 530, 322, 770, 164, 292, 548, 644, 772, 56, 88, 536, 104, 168, 552, 200, 584, 648, 112, 304, 560, 784, 352, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_91, vertices_539, vertices_451, vertices_421, vertices_709, vertices_585, vertices_370, vertices_786, vertices_684, vertices_820, vertices_120, vertices_568, vertices_488, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_67, vertices_259, vertices_515, vertices_133, vertices_261, vertices_517, vertices_73, vertices_521, vertices_193, vertices_577, vertices_385, vertices_82, vertices_274, vertices_530, vertices_322, vertices_770, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_56, vertices_88, vertices_536, vertices_104, vertices_168, vertices_552, vertices_200, vertices_584, vertices_648, vertices_112, vertices_304, vertices_560, vertices_784, vertices_352, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_91), (false, vertices_539), (false, vertices_451), (false, vertices_421), (false, vertices_709), (false, vertices_585), (true, vertices_274), (true, vertices_548), (true, vertices_56), (true, vertices_104), (true, vertices_168), (true, vertices_552), (true, vertices_200), (true, vertices_648), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_784), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 14 22 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_91) then 19 else
  if p.val = (false, vertices_539) then 20 else
  if p.val = (false, vertices_451) then 21 else
  if p.val = (false, vertices_421) then 16 else
  if p.val = (false, vertices_709) then 17 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_56) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
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
cert_row_4 0 0 3 4 5 7 370 82 2
cert_row_4 1 1 3 4 7 8 820 292 1
cert_row_4 2 1 2 4 6 8 684 164 1
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 370
cert_cover_5 0 0 0 3 4 5 82 370 2
cert_coverFacet 1 786
cert_cover_2 1 3 0 7 8 274 786 3
cert_coverFacet 2 684
cert_cover_5 2 2 1 2 4 6 164 684 1
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 292 820 1
cert_coverFacet 4 120
cert_cover_2 4 3 2 4 5 56 120 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 104 488 3
cert_coverFacet 7 712
cert_cover_2 7 5 2 6 8 200 712 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0880

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0881.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0881

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 205, 837, 345, 809, 649, 406, 806, 682, 242, 306, 468, 120, 312, 232, 69, 133, 517, 73, 137, 265, 521, 321, 641, 769, 134, 262, 518, 50, 146, 274, 162, 290, 546, 642, 404, 196, 324, 772, 56, 88, 280, 104, 168, 296, 552, 200, 648, 112, 304, 208, 336, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_205, vertices_837, vertices_345, vertices_809, vertices_649, vertices_406, vertices_806, vertices_682, vertices_242, vertices_306, vertices_468, vertices_120, vertices_312, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_73, vertices_137, vertices_265, vertices_521, vertices_321, vertices_641, vertices_769, vertices_134, vertices_262, vertices_518, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_642, vertices_404, vertices_196, vertices_324, vertices_772, vertices_56, vertices_88, vertices_280, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_648, vertices_112, vertices_304, vertices_208, vertices_336, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_205), (false, vertices_837), (false, vertices_345), (false, vertices_809), (false, vertices_649), (true, vertices_262), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_404), (true, vertices_56), (true, vertices_104), (true, vertices_168), (true, vertices_112), (true, vertices_304), (true, vertices_208), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_205) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (false, vertices_809) then 23 else
  if p.val = (false, vertices_649) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_404) then 20 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
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
cert_row_4 0 0 2 4 6 8 682 162 1
cert_row_4 1 0 1 4 7 8 806 262 2
cert_row_2 2 1 3 6 7 404
cert_row_4 3 0 3 4 5 6 242 50 3
cert_rows
cert_pivot_2 2 8 1 0
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 2 0 1 3 6 134 406 2
cert_coverFacet 1 806
cert_cover_5 1 1 0 1 4 7 262 806 2
cert_coverFacet 2 682
cert_cover_5 2 0 0 2 4 6 162 682 1
cert_coverFacet 3 242
cert_cover_5 3 3 0 3 4 5 50 242 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 468
cert_cover_5 5 2 1 3 5 6 404 468 2
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 232
cert_cover_2 8 4 2 5 6 104 232 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0881

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0882.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0882

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 803, 341, 709, 313, 625, 422, 646, 570, 170, 714, 460, 344, 600, 424, 771, 69, 261, 517, 49, 81, 273, 289, 545, 577, 134, 262, 518, 42, 138, 522, 162, 290, 546, 642, 196, 324, 388, 644, 56, 88, 280, 536, 168, 296, 200, 328, 584, 392, 560, 336, 592, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_803, vertices_341, vertices_709, vertices_313, vertices_625, vertices_422, vertices_646, vertices_570, vertices_170, vertices_714, vertices_460, vertices_344, vertices_600, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_771, vertices_69, vertices_261, vertices_517, vertices_49, vertices_81, vertices_273, vertices_289, vertices_545, vertices_577, vertices_134, vertices_262, vertices_518, vertices_42, vertices_138, vertices_522, vertices_162, vertices_290, vertices_546, vertices_642, vertices_196, vertices_324, vertices_388, vertices_644, vertices_56, vertices_88, vertices_280, vertices_536, vertices_168, vertices_296, vertices_200, vertices_328, vertices_584, vertices_392, vertices_560, vertices_336, vertices_592, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_803), (false, vertices_341), (false, vertices_709), (false, vertices_313), (false, vertices_625), (true, vertices_134), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_162), (true, vertices_642), (true, vertices_388), (true, vertices_88), (true, vertices_536), (true, vertices_168), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_392), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_62 134 42 138 522 162 642 388 88 536 168 200 328 584 392 416 775 803 341 709 313 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 42 2
cert_row_4 1 0 1 4 6 7 422 134 2
cert_row_4 2 0 2 5 6 8 714 138 2
cert_row_4 3 1 2 5 6 7 460 196 1
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 1 0 1 4 6 134 422 2
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 570
cert_cover_5 2 0 0 2 3 4 42 570 2
cert_coverFacet 3 170
cert_cover_2 3 2 0 4 6 42 170 3
cert_coverFacet 4 714
cert_cover_5 4 2 0 2 5 6 138 714 2
cert_coverFacet 5 460
cert_cover_5 5 3 1 2 5 6 196 460 1
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0882

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0883.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0883

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 285, 597, 901, 313, 689, 838, 234, 722, 354, 898, 92, 364, 184, 216, 21, 261, 517, 281, 49, 529, 161, 289, 385, 641, 98, 162, 290, 194, 322, 578, 386, 642, 770, 28, 76, 268, 84, 324, 580, 772, 56, 88, 152, 104, 168, 296, 200, 176, 208, 592, 656, 352, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_285, vertices_597, vertices_901, vertices_313, vertices_689, vertices_838, vertices_234, vertices_722, vertices_354, vertices_898, vertices_92, vertices_364, vertices_184, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_261, vertices_517, vertices_281, vertices_49, vertices_529, vertices_161, vertices_289, vertices_385, vertices_641, vertices_98, vertices_162, vertices_290, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_268, vertices_84, vertices_324, vertices_580, vertices_772, vertices_56, vertices_88, vertices_152, vertices_104, vertices_168, vertices_296, vertices_200, vertices_176, vertices_208, vertices_592, vertices_656, vertices_352, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_285), (false, vertices_597), (false, vertices_901), (false, vertices_313), (false, vertices_689), (true, vertices_98), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_76), (true, vertices_324), (true, vertices_88), (true, vertices_152), (true, vertices_104), (true, vertices_168), (true, vertices_200), (true, vertices_208), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_285) then 21 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 98 1 194 2 322 578 642 770 76 324 88 152 104 168 200 208 352 419 597 901 285 313 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 8 722 194 1
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 2 4 5 6 234 98 1
cert_row_4 3 1 2 4 5 7 364 76 2
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 234
cert_cover_5 1 2 0 2 4 5 98 234 1
cert_coverFacet 2 722
cert_cover_5 2 0 0 3 5 6 194 722 1
cert_coverFacet 3 354
cert_cover_2 3 4 0 5 7 98 354 3
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 92
cert_cover_2 5 2 1 3 5 28 92 3
cert_coverFacet 6 364
cert_cover_5 6 3 1 2 4 5 76 364 2
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0883

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0884.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0884

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 267, 835, 613, 57, 345, 241, 902, 410, 666, 692, 484, 836, 568, 464, 11, 259, 515, 25, 41, 265, 49, 81, 97, 545, 321, 577, 154, 266, 522, 386, 642, 770, 100, 164, 548, 324, 580, 388, 644, 772, 56, 280, 536, 552, 176, 560, 208, 336, 400, 656, 224, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_267, vertices_835, vertices_613, vertices_57, vertices_345, vertices_241, vertices_902, vertices_410, vertices_666, vertices_692, vertices_484, vertices_836, vertices_568, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_259, vertices_515, vertices_25, vertices_41, vertices_265, vertices_49, vertices_81, vertices_97, vertices_545, vertices_321, vertices_577, vertices_154, vertices_266, vertices_522, vertices_386, vertices_642, vertices_770, vertices_100, vertices_164, vertices_548, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_280, vertices_536, vertices_552, vertices_176, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_224, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_267), (false, vertices_835), (false, vertices_613), (false, vertices_57), (false, vertices_345), (false, vertices_241), (true, vertices_154), (true, vertices_386), (true, vertices_642), (true, vertices_164), (true, vertices_324), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_536), (true, vertices_560), (true, vertices_400), (true, vertices_656), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 15 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_57) then 1 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_154) then 17 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
cert_nodeAtPriority_23 267 57 386 642 164 324 388 644 772 536 560 400 656 448 555 835 154 613 345 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 0 1 6 7 8 902 386 1
cert_row_4 2 1 3 4 6 8 692 164 1
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 7 154 410 3
cert_coverFacet 2 666
cert_cover_5 2 0 0 2 3 8 154 666 3
cert_coverFacet 3 692
cert_cover_5 3 2 1 3 4 6 164 692 1
cert_coverFacet 4 484
cert_cover_5 4 3 1 4 5 6 100 484 3
cert_coverFacet 5 836
cert_cover_2 5 5 1 7 8 324 836 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0884

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0885.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0885

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 781, 601, 361, 737, 902, 410, 242, 370, 674, 156, 540, 396, 724, 344, 73, 265, 521, 97, 289, 545, 577, 769, 114, 146, 274, 162, 290, 546, 386, 642, 770, 28, 140, 268, 524, 148, 532, 388, 644, 772, 88, 152, 280, 536, 328, 392, 208, 336, 592, 224, 352, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_781, vertices_601, vertices_361, vertices_737, vertices_902, vertices_410, vertices_242, vertices_370, vertices_674, vertices_156, vertices_540, vertices_396, vertices_724, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_97, vertices_289, vertices_545, vertices_577, vertices_769, vertices_114, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_140, vertices_268, vertices_524, vertices_148, vertices_532, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_536, vertices_328, vertices_392, vertices_208, vertices_336, vertices_592, vertices_224, vertices_352, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_781), (false, vertices_601), (false, vertices_361), (false, vertices_737), (true, vertices_114), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_28), (true, vertices_140), (true, vertices_148), (true, vertices_532), (true, vertices_388), (true, vertices_644), (true, vertices_152), (true, vertices_280), (true, vertices_392), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_601) then 22 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_114) then 18 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_336) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_114), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 5 114
cert_row_4 1 0 2 3 6 7 410 146 1
cert_row_4 2 0 1 6 7 8 902 386 1
cert_row_4 3 1 3 5 6 8 724 148 2
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 2 0 1 6 7 386 902 1
cert_coverFacet 1 410
cert_cover_5 1 1 0 2 3 6 146 410 1
cert_coverFacet 2 242
cert_cover_5 2 0 0 3 4 6 114 242 3
cert_coverFacet 3 370
cert_cover_5 3 0 0 3 4 7 114 370 3
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 396
cert_cover_2 7 2 1 6 7 140 396 3
cert_coverFacet 8 724
cert_cover_5 8 3 1 3 5 6 148 724 2
cert_coverFacet 9 344
cert_cover_2 9 3 2 5 7 88 344 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0885

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0886.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0886

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 675, 451, 709, 601, 337, 422, 810, 220, 412, 620, 300, 676, 792, 464, 131, 259, 515, 81, 273, 529, 193, 321, 577, 641, 162, 290, 546, 386, 770, 156, 44, 76, 268, 164, 292, 548, 196, 580, 388, 644, 88, 280, 536, 296, 552, 584, 776, 208, 336, 400, 784, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_675, vertices_451, vertices_709, vertices_601, vertices_337, vertices_422, vertices_810, vertices_220, vertices_412, vertices_620, vertices_300, vertices_676, vertices_792, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_81, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_156, vertices_44, vertices_76, vertices_268, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_644, vertices_88, vertices_280, vertices_536, vertices_296, vertices_552, vertices_584, vertices_776, vertices_208, vertices_336, vertices_400, vertices_784, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_675), (false, vertices_451), (false, vertices_709), (false, vertices_601), (false, vertices_337), (true, vertices_290), (true, vertices_156), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_388), (true, vertices_280), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_675) then 17 else
  if p.val = (false, vertices_451) then 18 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_156) then 21 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 22 => Sum.inl 2
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
cert_row_2 0 1 2 3 6 156
cert_row_4 1 0 1 4 6 7 422 162 1
cert_row_4 2 0 2 4 7 8 810 290 1
cert_row_4 3 1 2 4 5 8 620 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 1 0 1 4 6 162 422 1
cert_coverFacet 1 810
cert_cover_5 1 2 0 2 4 7 290 810 1
cert_coverFacet 2 220
cert_cover_5 2 0 1 2 3 5 156 220 3
cert_coverFacet 3 412
cert_cover_5 3 0 1 2 3 7 156 412 3
cert_coverFacet 4 620
cert_cover_5 4 3 1 2 4 5 44 620 3
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0886

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0887.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0887

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 589, 229, 645, 425, 329, 369, 902, 346, 602, 394, 818, 628, 420, 804, 69, 133, 517, 73, 137, 265, 521, 97, 161, 289, 321, 641, 90, 138, 266, 522, 274, 530, 386, 642, 770, 100, 164, 292, 548, 580, 388, 644, 772, 328, 584, 392, 112, 304, 560, 336, 592, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_589, vertices_229, vertices_645, vertices_425, vertices_329, vertices_369, vertices_902, vertices_346, vertices_602, vertices_394, vertices_818, vertices_628, vertices_420, vertices_804] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_73, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_321, vertices_641, vertices_90, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_100, vertices_164, vertices_292, vertices_548, vertices_580, vertices_388, vertices_644, vertices_772, vertices_328, vertices_584, vertices_392, vertices_112, vertices_304, vertices_560, vertices_336, vertices_592, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_589), (false, vertices_229), (false, vertices_645), (false, vertices_425), (false, vertices_329), (false, vertices_369), (true, vertices_90), (true, vertices_266), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_770), (true, vertices_292), (true, vertices_548), (true, vertices_388), (true, vertices_772), (true, vertices_560), (true, vertices_592), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (true, vertices_90) then 16 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 645 1 329 266 274 530 386 770 292 548 388 772 560 592 800 651 90 589 229 425 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 6 7 8 902 386 1
cert_row_4 2 0 3 4 7 8 818 274 2
cert_row_4 3 1 3 4 5 8 628 100 1
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 7 90 346 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 8 90 602 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 818
cert_cover_5 4 2 0 3 4 7 274 818 2
cert_coverFacet 5 628
cert_cover_5 5 3 1 3 4 5 100 628 1
cert_coverFacet 6 420
cert_cover_2 6 4 1 6 7 164 420 3
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0887

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0888.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0888

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 405, 121, 281, 809, 689, 118, 182, 326, 390, 842, 226, 706, 348, 744, 25, 41, 265, 49, 145, 273, 545, 385, 641, 769, 54, 70, 134, 262, 98, 162, 194, 322, 578, 386, 642, 770, 84, 148, 276, 324, 388, 88, 280, 104, 552, 328, 584, 776, 112, 176, 224, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_405, vertices_121, vertices_281, vertices_809, vertices_689, vertices_118, vertices_182, vertices_326, vertices_390, vertices_842, vertices_226, vertices_706, vertices_348, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_49, vertices_145, vertices_273, vertices_545, vertices_385, vertices_641, vertices_769, vertices_54, vertices_70, vertices_134, vertices_262, vertices_98, vertices_162, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_84, vertices_148, vertices_276, vertices_324, vertices_388, vertices_88, vertices_280, vertices_104, vertices_552, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_224, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_405), (false, vertices_121), (false, vertices_281), (false, vertices_809), (false, vertices_689), (true, vertices_54), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_98), (true, vertices_162), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_84), (true, vertices_324), (true, vertices_328), (true, vertices_584), (true, vertices_224), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_121) then 21 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (true, vertices_54) then 17 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 281 70 134 262 98 162 194 322 578 84 324 328 584 224 704 899 54 405 121 809 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 4 5 6 8 744 104 3
cert_row_2 1 0 1 3 4 54
cert_row_4 2 0 2 5 7 8 842 322 1
cert_row_4 3 1 2 3 5 7 348 84 1
cert_rows
cert_pivot_2 6 4 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 1 0 1 3 5 54 118 3
cert_coverFacet 1 182
cert_cover_5 1 1 0 1 3 6 54 182 3
cert_coverFacet 2 326
cert_cover_2 2 1 0 5 7 70 326 3
cert_coverFacet 3 390
cert_cover_2 3 1 0 6 7 134 390 3
cert_coverFacet 4 842
cert_cover_5 4 2 0 2 5 7 322 842 1
cert_coverFacet 5 226
cert_cover_2 5 4 0 5 6 98 226 3
cert_coverFacet 6 706
cert_cover_2 6 5 0 6 8 194 706 3
cert_coverFacet 7 348
cert_cover_5 7 3 1 2 3 5 84 348 1
cert_coverFacet 8 744
cert_cover_5 8 0 2 4 5 6 104 744 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0888

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0889.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0889

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 403, 611, 643, 565, 277, 665, 714, 226, 418, 412, 540, 844, 868, 488, 35, 131, 259, 515, 21, 37, 261, 145, 273, 529, 545, 641, 98, 162, 290, 194, 578, 386, 642, 28, 268, 524, 276, 532, 292, 548, 836, 152, 536, 200, 328, 584, 392, 648, 400, 224, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_403, vertices_611, vertices_643, vertices_565, vertices_277, vertices_665, vertices_714, vertices_226, vertices_418, vertices_412, vertices_540, vertices_844, vertices_868, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_21, vertices_37, vertices_261, vertices_145, vertices_273, vertices_529, vertices_545, vertices_641, vertices_98, vertices_162, vertices_290, vertices_194, vertices_578, vertices_386, vertices_642, vertices_28, vertices_268, vertices_524, vertices_276, vertices_532, vertices_292, vertices_548, vertices_836, vertices_152, vertices_536, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_400, vertices_224, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_403), (false, vertices_611), (false, vertices_643), (false, vertices_565), (false, vertices_277), (false, vertices_665), (true, vertices_162), (true, vertices_194), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_836), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_392), (true, vertices_224), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 15 else
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_277) then 1 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_836) then 20 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_836), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 194 1
cert_row_2 1 1 5 7 8 836
cert_row_4 2 1 2 3 6 7 412 28 3
cert_row_4 3 2 4 5 6 7 488 200 1
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 714
cert_cover_5 0 0 0 2 5 6 194 714 1
cert_coverFacet 1 226
cert_cover_2 1 4 0 5 6 98 226 3
cert_coverFacet 2 418
cert_cover_2 2 4 0 6 7 162 418 3
cert_coverFacet 3 412
cert_cover_5 3 2 1 2 3 6 28 412 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 844
cert_cover_5 5 1 1 2 5 7 268 844 2
cert_coverFacet 6 868
cert_cover_5 6 1 1 4 5 7 292 868 2
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 200 488 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0889

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0890.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0890

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 781, 233, 585, 433, 961, 110, 270, 118, 534, 774, 306, 914, 604, 752, 41, 73, 265, 521, 161, 289, 193, 577, 385, 769, 14, 22, 102, 262, 518, 42, 266, 50, 274, 530, 290, 770, 76, 268, 524, 84, 532, 772, 104, 584, 112, 176, 304, 592, 400, 656, 224, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_781, vertices_233, vertices_585, vertices_433, vertices_961, vertices_110, vertices_270, vertices_118, vertices_534, vertices_774, vertices_306, vertices_914, vertices_604, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_22, vertices_102, vertices_262, vertices_518, vertices_42, vertices_266, vertices_50, vertices_274, vertices_530, vertices_290, vertices_770, vertices_76, vertices_268, vertices_524, vertices_84, vertices_532, vertices_772, vertices_104, vertices_584, vertices_112, vertices_176, vertices_304, vertices_592, vertices_400, vertices_656, vertices_224, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_781), (false, vertices_233), (false, vertices_585), (false, vertices_433), (false, vertices_961), (true, vertices_14), (true, vertices_22), (true, vertices_102), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_770), (true, vertices_76), (true, vertices_84), (true, vertices_532), (true, vertices_112), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 25 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_961) then 26 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_102) then 17 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 6 7 8 914 274 2
cert_row_2 1 0 1 4 5 102
cert_row_4 2 1 2 3 5 8 604 76 2
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 7 0 1 3
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 118
cert_cover_5 2 1 0 1 3 4 22 118 3
cert_coverFacet 3 534
cert_cover_2 3 1 0 3 8 22 534 3
cert_coverFacet 4 774
cert_cover_2 4 1 0 7 8 262 774 3
cert_coverFacet 5 306
cert_cover_2 5 3 0 4 7 50 306 3
cert_coverFacet 6 914
cert_cover_5 6 0 0 3 6 7 274 914 2
cert_coverFacet 7 604
cert_cover_5 7 2 1 2 3 5 76 604 2
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 112 752 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0890

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0891.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0891

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 779, 339, 147, 617, 329, 721, 406, 806, 436, 740, 248, 312, 344, 808, 19, 131, 259, 515, 73, 265, 521, 81, 145, 321, 577, 641, 134, 262, 518, 146, 274, 770, 404, 164, 292, 548, 644, 56, 88, 280, 104, 296, 552, 328, 776, 176, 304, 208, 336, 224, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_779, vertices_339, vertices_147, vertices_617, vertices_329, vertices_721, vertices_406, vertices_806, vertices_436, vertices_740, vertices_248, vertices_312, vertices_344, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_73, vertices_265, vertices_521, vertices_81, vertices_145, vertices_321, vertices_577, vertices_641, vertices_134, vertices_262, vertices_518, vertices_146, vertices_274, vertices_770, vertices_404, vertices_164, vertices_292, vertices_548, vertices_644, vertices_56, vertices_88, vertices_280, vertices_104, vertices_296, vertices_552, vertices_328, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_224, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_779), (false, vertices_339), (false, vertices_147), (false, vertices_617), (false, vertices_329), (false, vertices_721), (true, vertices_262), (true, vertices_404), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_56), (true, vertices_88), (true, vertices_280), (true, vertices_296), (true, vertices_176), (true, vertices_304), (true, vertices_224), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_339) then 17 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_404) then 19 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
cert_nodeAtPriority_47 147 329 262 164 292 548 56 88 280 296 176 304 224 800 647 779 339 404 617 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 262 2
cert_row_2 1 1 3 6 7 404
cert_row_4 2 1 4 5 6 8 740 164 2
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 1 0 1 3 6 134 406 2
cert_coverFacet 1 806
cert_cover_5 1 0 0 1 4 7 262 806 2
cert_coverFacet 2 436
cert_cover_5 2 1 1 3 4 6 404 436 2
cert_coverFacet 3 740
cert_cover_5 3 2 1 4 5 6 164 740 2
cert_coverFacet 4 248
cert_cover_5 4 3 2 3 4 5 56 248 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0891

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0892.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0892

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 611, 291, 597, 421, 197, 233, 906, 418, 674, 796, 468, 632, 472, 680, 35, 259, 515, 69, 133, 261, 517, 97, 161, 289, 193, 577, 162, 290, 546, 386, 642, 770, 84, 276, 532, 196, 388, 772, 88, 280, 536, 104, 168, 552, 200, 392, 648, 776, 464, 592, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_611, vertices_291, vertices_597, vertices_421, vertices_197, vertices_233, vertices_906, vertices_418, vertices_674, vertices_796, vertices_468, vertices_632, vertices_472, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_69, vertices_133, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_193, vertices_577, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_84, vertices_276, vertices_532, vertices_196, vertices_388, vertices_772, vertices_88, vertices_280, vertices_536, vertices_104, vertices_168, vertices_552, vertices_200, vertices_392, vertices_648, vertices_776, vertices_464, vertices_592, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_611), (false, vertices_291), (false, vertices_597), (false, vertices_421), (false, vertices_197), (false, vertices_233), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_276), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_552), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_464), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_197) then 1 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_464) then 23 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(true, vertices_464), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 386 1
cert_row_2 1 3 5 6 7 464
cert_row_4 2 1 2 3 7 8 796 276 1
cert_row_4 3 2 3 4 5 8 632 88 2
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 906
cert_cover_5 0 0 0 2 6 7 386 906 1
cert_coverFacet 1 418
cert_cover_2 1 4 0 6 7 162 418 3
cert_coverFacet 2 674
cert_cover_2 2 4 0 6 8 162 674 3
cert_coverFacet 3 796
cert_cover_5 3 2 1 2 3 7 276 796 1
cert_coverFacet 4 468
cert_cover_5 4 1 1 3 5 6 84 468 3
cert_coverFacet 5 632
cert_cover_5 5 3 2 3 4 5 88 632 2
cert_coverFacet 6 472
cert_cover_5 6 1 2 3 5 6 88 472 3
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0892

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0893.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0893

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 779, 339, 147, 713, 329, 241, 406, 806, 436, 740, 632, 312, 344, 808, 19, 131, 259, 515, 73, 265, 521, 81, 145, 193, 321, 641, 134, 262, 518, 146, 274, 770, 404, 164, 292, 548, 644, 56, 88, 280, 296, 552, 328, 584, 776, 112, 176, 304, 336, 224, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_779, vertices_339, vertices_147, vertices_713, vertices_329, vertices_241, vertices_406, vertices_806, vertices_436, vertices_740, vertices_632, vertices_312, vertices_344, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_73, vertices_265, vertices_521, vertices_81, vertices_145, vertices_193, vertices_321, vertices_641, vertices_134, vertices_262, vertices_518, vertices_146, vertices_274, vertices_770, vertices_404, vertices_164, vertices_292, vertices_548, vertices_644, vertices_56, vertices_88, vertices_280, vertices_296, vertices_552, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_304, vertices_336, vertices_224, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_779), (false, vertices_339), (false, vertices_147), (false, vertices_713), (false, vertices_329), (false, vertices_241), (true, vertices_262), (true, vertices_404), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_56), (true, vertices_88), (true, vertices_280), (true, vertices_296), (true, vertices_552), (true, vertices_304), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_339) then 17 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_404) then 19 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
cert_nodeAtPriority_47 147 329 262 164 292 548 56 88 280 296 552 304 608 800 647 779 339 404 713 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 262 2
cert_row_2 1 1 3 6 7 404
cert_row_4 2 1 4 5 6 8 740 164 2
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 1 0 1 3 6 134 406 2
cert_coverFacet 1 806
cert_cover_5 1 0 0 1 4 7 262 806 2
cert_coverFacet 2 436
cert_cover_5 2 1 1 3 4 6 404 436 2
cert_coverFacet 3 740
cert_cover_5 3 2 1 4 5 6 164 740 2
cert_coverFacet 4 632
cert_cover_5 4 3 2 3 4 5 56 632 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0893

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0894.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0894

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 659, 387, 541, 89, 457, 241, 678, 482, 802, 348, 812, 372, 180, 660, 131, 259, 515, 25, 73, 265, 521, 81, 145, 529, 193, 385, 162, 290, 546, 386, 642, 770, 28, 268, 524, 52, 340, 148, 532, 164, 292, 548, 644, 88, 328, 776, 112, 176, 656, 224, 352, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_659, vertices_387, vertices_541, vertices_89, vertices_457, vertices_241, vertices_678, vertices_482, vertices_802, vertices_348, vertices_812, vertices_372, vertices_180, vertices_660] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_25, vertices_73, vertices_265, vertices_521, vertices_81, vertices_145, vertices_529, vertices_193, vertices_385, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_52, vertices_340, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_88, vertices_328, vertices_776, vertices_112, vertices_176, vertices_656, vertices_224, vertices_352, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_659), (false, vertices_387), (false, vertices_541), (false, vertices_89), (false, vertices_457), (false, vertices_241), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_268), (true, vertices_52), (true, vertices_340), (true, vertices_148), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_644), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_541) then 18 else
  if p.val = (false, vertices_89) then 1 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_340) then 19 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
cert_nodeAtPriority_44 387 89 162 290 546 268 52 148 164 292 548 644 352 800 779 659 541 340 457 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 5 7 340
cert_row_4 1 0 4 5 6 7 482 162 2
cert_row_4 2 0 1 4 6 8 678 162 1
cert_row_4 3 1 2 4 7 8 812 268 2
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 162 678 1
cert_coverFacet 1 482
cert_cover_5 1 1 0 4 5 6 162 482 2
cert_coverFacet 2 802
cert_cover_2 2 4 0 7 8 290 802 3
cert_coverFacet 3 348
cert_cover_5 3 0 1 2 3 5 28 348 3
cert_coverFacet 4 812
cert_cover_5 4 3 1 2 4 7 268 812 2
cert_coverFacet 5 372
cert_cover_5 5 0 1 3 4 5 52 372 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0894

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0895.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0895

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 613, 601, 425, 553, 369, 662, 422, 838, 154, 394, 850, 684, 356, 664, 25, 41, 265, 521, 81, 273, 97, 289, 545, 577, 134, 262, 518, 26, 138, 266, 146, 274, 530, 834, 386, 100, 164, 292, 548, 324, 580, 644, 152, 536, 168, 552, 392, 648, 336, 592, 656, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_613, vertices_601, vertices_425, vertices_553, vertices_369, vertices_662, vertices_422, vertices_838, vertices_154, vertices_394, vertices_850, vertices_684, vertices_356, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_521, vertices_81, vertices_273, vertices_97, vertices_289, vertices_545, vertices_577, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_834, vertices_386, vertices_100, vertices_164, vertices_292, vertices_548, vertices_324, vertices_580, vertices_644, vertices_152, vertices_536, vertices_168, vertices_552, vertices_392, vertices_648, vertices_336, vertices_592, vertices_656, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_613), (false, vertices_601), (false, vertices_425), (false, vertices_553), (false, vertices_369), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_146), (true, vertices_530), (true, vertices_834), (true, vertices_386), (true, vertices_164), (true, vertices_292), (true, vertices_324), (true, vertices_644), (true, vertices_152), (true, vertices_648), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 16 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_834) then 17 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 553 134 262 518 138 146 530 386 164 292 324 644 152 648 656 283 834 613 601 425 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 7 8 834
cert_row_4 1 0 1 3 6 8 662 134 2
cert_row_4 2 0 1 4 6 7 422 134 2
cert_row_4 3 1 2 4 6 8 684 164 1
cert_rows
cert_pivot_2 5 3 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 134 662 2
cert_coverFacet 1 422
cert_cover_5 1 2 0 1 4 6 134 422 2
cert_coverFacet 2 838
cert_cover_5 2 0 0 1 5 7 262 838 2
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 850
cert_cover_5 5 0 0 3 5 7 274 850 2
cert_coverFacet 6 684
cert_cover_5 6 3 1 2 4 6 164 684 1
cert_coverFacet 7 356
cert_cover_2 7 4 1 5 7 100 356 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0895

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0897.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0897

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 285, 153, 457, 721, 865, 158, 174, 278, 358, 690, 802, 108, 332, 744, 25, 137, 265, 145, 273, 529, 193, 321, 577, 769, 142, 22, 38, 262, 146, 274, 530, 162, 290, 546, 770, 28, 44, 76, 268, 276, 100, 324, 152, 104, 168, 200, 328, 656, 352, 608, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_285, vertices_153, vertices_457, vertices_721, vertices_865, vertices_158, vertices_174, vertices_278, vertices_358, vertices_690, vertices_802, vertices_108, vertices_332, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_769, vertices_142, vertices_22, vertices_38, vertices_262, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_770, vertices_28, vertices_44, vertices_76, vertices_268, vertices_276, vertices_100, vertices_324, vertices_152, vertices_104, vertices_168, vertices_200, vertices_328, vertices_656, vertices_352, vertices_608, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_285), (false, vertices_153), (false, vertices_457), (false, vertices_721), (false, vertices_865), (true, vertices_142), (true, vertices_22), (true, vertices_38), (true, vertices_262), (true, vertices_146), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_44), (true, vertices_76), (true, vertices_100), (true, vertices_324), (true, vertices_104), (true, vertices_168), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_285) then 19 else
  if p.val = (false, vertices_153) then 0 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_865) then 25 else
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
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 153 22 38 262 146 162 290 546 44 76 100 324 104 168 672 787 142 285 457 721 865
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 7 358 38 3
cert_row_2 1 0 1 2 6 142
cert_row_4 2 0 3 4 6 8 690 146 2
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 7 1 0 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 142 158 3
cert_coverFacet 1 174
cert_cover_5 1 1 0 1 2 4 142 174 3
cert_coverFacet 2 278
cert_cover_2 2 1 0 3 7 22 278 3
cert_coverFacet 3 358
cert_cover_5 3 0 0 1 4 5 38 358 3
cert_coverFacet 4 690
cert_cover_5 4 2 0 3 4 6 146 690 2
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 108
cert_cover_2 6 2 1 4 5 44 108 3
cert_coverFacet 7 332
cert_cover_2 7 2 1 5 7 76 332 3
cert_coverFacet 8 744
cert_cover_5 8 3 2 4 5 6 104 744 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0897

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0898.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0898

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 213, 533, 837, 793, 481, 662, 678, 570, 282, 362, 418, 620, 228, 840, 21, 69, 517, 145, 273, 529, 193, 321, 385, 769, 646, 26, 42, 266, 146, 274, 530, 162, 290, 546, 386, 148, 532, 100, 164, 548, 196, 580, 280, 536, 104, 552, 328, 584, 776, 224, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_213, vertices_533, vertices_837, vertices_793, vertices_481, vertices_662, vertices_678, vertices_570, vertices_282, vertices_362, vertices_418, vertices_620, vertices_228, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_517, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_385, vertices_769, vertices_646, vertices_26, vertices_42, vertices_266, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_280, vertices_536, vertices_104, vertices_552, vertices_328, vertices_584, vertices_776, vertices_224, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_213), (false, vertices_533), (false, vertices_837), (false, vertices_793), (false, vertices_481), (true, vertices_646), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_100), (true, vertices_164), (true, vertices_548), (true, vertices_104), (true, vertices_552), (true, vertices_328), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_793) then 22 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_646) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_584) then 14 else
  0
cert_priority
cert_nodeAtPriority_34 533 26 42 266 530 162 290 546 100 164 548 104 552 328 584 403 646 213 837 793 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 8 646
cert_row_4 1 0 2 3 4 8 570 26 3
cert_row_4 2 0 2 4 5 7 362 42 3
cert_row_4 3 1 2 4 5 8 620 100 1
cert_rows
cert_pivot_2 6 3 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 646 662 2
cert_coverFacet 1 678
cert_cover_5 1 0 0 1 4 6 646 678 2
cert_coverFacet 2 570
cert_cover_5 2 1 0 2 3 4 26 570 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 362
cert_cover_5 4 2 0 2 4 5 42 362 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 100 620 1
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coverFacet 8 840
cert_cover_2 8 5 2 7 8 328 840 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0898

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0899.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0899

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 781, 233, 393, 625, 929, 206, 526, 566, 214, 594, 412, 308, 804, 496, 73, 137, 265, 521, 97, 161, 545, 577, 385, 769, 14, 22, 198, 518, 74, 522, 82, 530, 578, 140, 268, 524, 52, 148, 276, 292, 548, 772, 200, 392, 112, 304, 560, 208, 592, 400, 224, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_781, vertices_233, vertices_393, vertices_625, vertices_929, vertices_206, vertices_526, vertices_566, vertices_214, vertices_594, vertices_412, vertices_308, vertices_804, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_577, vertices_385, vertices_769, vertices_14, vertices_22, vertices_198, vertices_518, vertices_74, vertices_522, vertices_82, vertices_530, vertices_578, vertices_140, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_292, vertices_548, vertices_772, vertices_200, vertices_392, vertices_112, vertices_304, vertices_560, vertices_208, vertices_592, vertices_400, vertices_224, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_781), (false, vertices_233), (false, vertices_393), (false, vertices_625), (false, vertices_929), (true, vertices_14), (true, vertices_22), (true, vertices_198), (true, vertices_518), (true, vertices_82), (true, vertices_530), (true, vertices_140), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_292), (true, vertices_548), (true, vertices_304), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_198) then 17 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 393 14 22 518 82 530 140 52 148 276 292 548 304 208 400 587 198 781 233 625 929
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 22 3
cert_row_2 1 0 1 5 6 198
cert_row_4 2 1 2 3 6 7 412 140 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 8 0 1 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 566
cert_cover_5 2 0 0 1 3 4 22 566 3
cert_coverFacet 3 214
cert_cover_5 3 1 0 1 3 5 22 214 3
cert_coverFacet 4 594
cert_cover_2 4 3 0 5 8 82 594 3
cert_coverFacet 5 412
cert_cover_5 5 2 1 2 3 6 140 412 2
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0899

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0900.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0900

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 613, 233, 809, 721, 286, 598, 806, 154, 778, 658, 244, 436, 408, 424, 41, 137, 521, 97, 545, 193, 577, 641, 22, 262, 518, 26, 138, 266, 522, 146, 530, 642, 770, 180, 84, 276, 100, 292, 548, 580, 152, 280, 168, 296, 392, 776, 208, 592, 400, 656, 224, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_613, vertices_233, vertices_809, vertices_721, vertices_286, vertices_598, vertices_806, vertices_154, vertices_778, vertices_658, vertices_244, vertices_436, vertices_408, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_521, vertices_97, vertices_545, vertices_193, vertices_577, vertices_641, vertices_22, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_642, vertices_770, vertices_180, vertices_84, vertices_276, vertices_100, vertices_292, vertices_548, vertices_580, vertices_152, vertices_280, vertices_168, vertices_296, vertices_392, vertices_776, vertices_208, vertices_592, vertices_400, vertices_656, vertices_224, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_613), (false, vertices_233), (false, vertices_809), (false, vertices_721), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_266), (true, vertices_146), (true, vertices_530), (true, vertices_770), (true, vertices_180), (true, vertices_84), (true, vertices_276), (true, vertices_292), (true, vertices_152), (true, vertices_280), (true, vertices_392), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 17 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_809) then 23 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_180) then 20 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_180), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 4 6 180
cert_row_4 1 0 1 2 3 7 286 22 2
cert_row_4 2 0 1 3 5 8 598 22 3
cert_row_4 3 0 1 4 7 8 806 262 2
cert_rows
cert_pivot_2 6 2 3 0
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 1 0 1 2 3 22 286 2
cert_coverFacet 1 598
cert_cover_5 1 2 0 1 3 5 22 598 3
cert_coverFacet 2 806
cert_cover_5 2 3 0 1 4 7 262 806 2
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 244
cert_cover_5 6 0 1 3 4 5 180 244 3
cert_coverFacet 7 436
cert_cover_5 7 0 1 3 4 7 180 436 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 424
cert_cover_2 9 4 2 6 7 168 424 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0900

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0901.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0901

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 781, 345, 713, 817, 654, 182, 806, 562, 210, 706, 236, 364, 240, 368, 73, 265, 521, 81, 273, 529, 577, 769, 38, 134, 518, 50, 82, 146, 530, 546, 194, 578, 642, 108, 140, 268, 524, 164, 292, 772, 200, 328, 648, 112, 176, 304, 560, 208, 336, 224, 352, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_781, vertices_345, vertices_713, vertices_817, vertices_654, vertices_182, vertices_806, vertices_562, vertices_210, vertices_706, vertices_236, vertices_364, vertices_240, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_81, vertices_273, vertices_529, vertices_577, vertices_769, vertices_38, vertices_134, vertices_518, vertices_50, vertices_82, vertices_146, vertices_530, vertices_546, vertices_194, vertices_578, vertices_642, vertices_108, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_772, vertices_200, vertices_328, vertices_648, vertices_112, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_224, vertices_352, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_781), (false, vertices_345), (false, vertices_713), (false, vertices_817), (true, vertices_38), (true, vertices_134), (true, vertices_518), (true, vertices_50), (true, vertices_146), (true, vertices_546), (true, vertices_194), (true, vertices_642), (true, vertices_108), (true, vertices_140), (true, vertices_164), (true, vertices_292), (true, vertices_112), (true, vertices_176), (true, vertices_208), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 17 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (false, vertices_713) then 23 else
  if p.val = (false, vertices_817) then 25 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_108) then 20 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_352) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 1 2 6 8 654 134 2
cert_row_4 2 0 1 3 4 6 182 38 2
cert_row_4 3 0 1 4 7 8 806 38 3
cert_rows
cert_pivot_2 5 2 3 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 134 654 2
cert_coverFacet 1 182
cert_cover_5 1 2 0 1 3 4 38 182 2
cert_coverFacet 2 806
cert_cover_5 2 3 0 1 4 7 38 806 3
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 236
cert_cover_5 6 0 1 2 4 6 108 236 3
cert_coverFacet 7 364
cert_cover_5 7 0 1 2 4 7 108 364 3
cert_coverFacet 8 240
cert_cover_2 8 4 3 5 6 112 240 3
cert_coverFacet 9 368
cert_cover_2 9 4 3 5 7 112 368 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0901

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0902.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0902

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 781, 409, 681, 721, 558, 118, 278, 774, 594, 738, 300, 468, 484, 424, 137, 265, 521, 145, 273, 529, 641, 769, 22, 38, 262, 518, 82, 274, 530, 98, 546, 578, 770, 44, 268, 524, 84, 276, 100, 292, 452, 772, 168, 296, 552, 392, 208, 592, 400, 224, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_781, vertices_409, vertices_681, vertices_721, vertices_558, vertices_118, vertices_278, vertices_774, vertices_594, vertices_738, vertices_300, vertices_468, vertices_484, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_641, vertices_769, vertices_22, vertices_38, vertices_262, vertices_518, vertices_82, vertices_274, vertices_530, vertices_98, vertices_546, vertices_578, vertices_770, vertices_44, vertices_268, vertices_524, vertices_84, vertices_276, vertices_100, vertices_292, vertices_452, vertices_772, vertices_168, vertices_296, vertices_552, vertices_392, vertices_208, vertices_592, vertices_400, vertices_224, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_781), (false, vertices_409), (false, vertices_681), (false, vertices_721), (true, vertices_22), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_82), (true, vertices_98), (true, vertices_546), (true, vertices_578), (true, vertices_44), (true, vertices_84), (true, vertices_276), (true, vertices_100), (true, vertices_292), (true, vertices_452), (true, vertices_296), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 17 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_292) then 12 else
  if p.val = (true, vertices_452) then 20 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_452), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 5 6 7 452
cert_row_4 1 0 1 2 4 8 558 38 2
cert_row_4 2 0 1 3 4 5 118 22 3
cert_row_4 3 0 4 5 6 8 738 98 3
cert_rows
cert_pivot_2 7 2 1 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 38 558 2
cert_coverFacet 1 118
cert_cover_5 1 2 0 1 3 4 22 118 3
cert_coverFacet 2 278
cert_cover_2 2 1 0 3 7 22 278 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 594
cert_cover_2 4 3 0 5 8 82 594 3
cert_coverFacet 5 738
cert_cover_5 5 3 0 4 5 6 98 738 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 468
cert_cover_5 7 0 1 3 5 6 84 468 3
cert_coverFacet 8 484
cert_cover_5 8 0 1 4 5 6 100 484 3
cert_coverFacet 9 424
cert_cover_2 9 4 2 6 7 168 424 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0902

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0904.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0904

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 677, 841, 721, 481, 62, 662, 550, 602, 298, 778, 92, 428, 460, 212, 161, 289, 545, 193, 321, 577, 641, 769, 22, 38, 518, 26, 42, 266, 522, 530, 290, 546, 770, 28, 44, 76, 396, 84, 148, 164, 548, 196, 644, 88, 296, 328, 584, 776, 208, 592, 656, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_677, vertices_841, vertices_721, vertices_481, vertices_62, vertices_662, vertices_550, vertices_602, vertices_298, vertices_778, vertices_92, vertices_428, vertices_460, vertices_212] (by decide +kernel)
  polygons := literalFinset [vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_22, vertices_38, vertices_518, vertices_26, vertices_42, vertices_266, vertices_522, vertices_530, vertices_290, vertices_546, vertices_770, vertices_28, vertices_44, vertices_76, vertices_396, vertices_84, vertices_148, vertices_164, vertices_548, vertices_196, vertices_644, vertices_88, vertices_296, vertices_328, vertices_584, vertices_776, vertices_208, vertices_592, vertices_656, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_677), (false, vertices_841), (false, vertices_721), (false, vertices_481), (true, vertices_22), (true, vertices_38), (true, vertices_518), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_530), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_396), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_88), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_76) then 10 else
  if p.val = (true, vertices_396) then 20 else
  if p.val = (true, vertices_84) then 11 else
  if p.val = (true, vertices_148) then 12 else
  if p.val = (true, vertices_196) then 13 else
  if p.val = (true, vertices_88) then 14 else
  if p.val = (true, vertices_296) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
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
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 1 2 3 4 62 22 2
cert_row_4 2 0 1 3 6 8 662 22 3
cert_row_4 3 0 2 3 5 8 602 26 3
cert_rows
cert_pivot_2 7 4 1 0
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 1 0 1 2 3 22 62 2
cert_coverFacet 1 662
cert_cover_5 1 2 0 1 3 6 22 662 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 602
cert_cover_5 3 3 0 2 3 5 26 602 3
cert_coverFacet 4 298
cert_cover_2 4 2 0 4 7 42 298 3
cert_coverFacet 5 778
cert_cover_2 5 2 0 7 8 266 778 3
cert_coverFacet 6 92
cert_cover_2 6 2 1 3 5 28 92 3
cert_coverFacet 7 428
cert_cover_5 7 0 1 2 4 6 44 428 3
cert_coverFacet 8 460
cert_cover_5 8 0 1 2 5 6 76 460 3
cert_coverFacet 9 212
cert_cover_2 9 3 1 5 6 84 212 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0904

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0905.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0905

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 787, 707, 661, 241, 369, 782, 618, 188, 284, 556, 788, 740, 312, 360, 67, 259, 515, 113, 145, 273, 529, 193, 321, 641, 74, 266, 522, 578, 770, 28, 44, 268, 524, 148, 276, 532, 164, 548, 644, 772, 56, 280, 104, 296, 552, 328, 176, 304, 784, 224, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_787, vertices_707, vertices_661, vertices_241, vertices_369, vertices_782, vertices_618, vertices_188, vertices_284, vertices_556, vertices_788, vertices_740, vertices_312, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_113, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_641, vertices_74, vertices_266, vertices_522, vertices_578, vertices_770, vertices_28, vertices_44, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_164, vertices_548, vertices_644, vertices_772, vertices_56, vertices_280, vertices_104, vertices_296, vertices_552, vertices_328, vertices_176, vertices_304, vertices_784, vertices_224, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_787), (false, vertices_707), (false, vertices_661), (false, vertices_241), (false, vertices_369), (true, vertices_522), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_164), (true, vertices_548), (true, vertices_772), (true, vertices_56), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 21 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_787) then 17 else
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_661) then 20 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_28) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 0 2 4 5 8 618 74 2
cert_row_4 2 1 2 3 4 6 188 28 3
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 7 0 2 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 618
cert_cover_5 1 1 0 2 4 5 74 618 2
cert_coverFacet 2 188
cert_cover_5 2 2 1 2 3 4 28 188 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 556
cert_cover_2 4 2 1 4 8 44 556 3
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 164 740 2
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0905

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0906.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0906

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 651, 611, 677, 185, 313, 353, 838, 794, 668, 404, 788, 484, 612, 432, 11, 67, 515, 57, 137, 265, 97, 161, 289, 545, 321, 641, 266, 522, 322, 578, 770, 148, 276, 532, 100, 164, 548, 324, 580, 388, 644, 772, 152, 280, 536, 648, 176, 304, 400, 784, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_651, vertices_611, vertices_677, vertices_185, vertices_313, vertices_353, vertices_838, vertices_794, vertices_668, vertices_404, vertices_788, vertices_484, vertices_612, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_515, vertices_57, vertices_137, vertices_265, vertices_97, vertices_161, vertices_289, vertices_545, vertices_321, vertices_641, vertices_266, vertices_522, vertices_322, vertices_578, vertices_770, vertices_148, vertices_276, vertices_532, vertices_100, vertices_164, vertices_548, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_152, vertices_280, vertices_536, vertices_648, vertices_176, vertices_304, vertices_400, vertices_784, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_651), (false, vertices_611), (false, vertices_677), (false, vertices_185), (false, vertices_313), (false, vertices_353), (true, vertices_770), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_100), (true, vertices_324), (true, vertices_580), (true, vertices_388), (true, vertices_772), (true, vertices_536), (true, vertices_400), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_353) then 0 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 4 5 6 7 484 100 3
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 2 3 7 8 794 266 2
cert_row_4 3 1 2 3 6 8 668 148 1
cert_rows
cert_pivot_2 4 5 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 794
cert_cover_5 1 2 0 2 3 7 266 794 2
cert_coverFacet 2 668
cert_cover_5 2 3 1 2 3 6 148 668 1
cert_coverFacet 3 404
cert_cover_2 3 3 1 6 7 148 404 3
cert_coverFacet 4 788
cert_cover_2 4 3 1 7 8 276 788 3
cert_coverFacet 5 484
cert_cover_5 5 0 1 4 5 6 100 484 3
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0906

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3453 : Certifies 3453 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0875.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3454 : Certifies 3454 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0876.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3455 : Certifies 3455 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0877.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3456 : Certifies 3456 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0878.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3457 : Certifies 3457 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0879.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3458 : Certifies 3458 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0880.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3459 : Certifies 3459 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0881.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3460 : Certifies 3460 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0882.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3461 : Certifies 3461 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0883.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3462 : Certifies 3462 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0884.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3463 : Certifies 3463 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0885.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3464 : Certifies 3464 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0886.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3465 : Certifies 3465 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0887.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3466 : Certifies 3466 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0888.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3467 : Certifies 3467 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0889.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3468 : Certifies 3468 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0890.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3469 : Certifies 3469 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0891.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3470 : Certifies 3470 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0892.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3471 : Certifies 3471 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0893.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3472 : Certifies 3472 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0894.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3473 : Certifies 3473 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0895.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3474 : Certifies 3474 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0897.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3475 : Certifies 3475 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0898.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3476 : Certifies 3476 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0899.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3477 : Certifies 3477 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0900.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3478 : Certifies 3478 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0901.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3479 : Certifies 3479 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0902.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3480 : Certifies 3480 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0904.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3481 : Certifies 3481 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0905.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3482 : Certifies 3482 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0906.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B114 (j : Fin 30) :
    Certifies (3453 + j.val) := by
  fin_cases j
  · exact projection_3453
  · exact projection_3454
  · exact projection_3455
  · exact projection_3456
  · exact projection_3457
  · exact projection_3458
  · exact projection_3459
  · exact projection_3460
  · exact projection_3461
  · exact projection_3462
  · exact projection_3463
  · exact projection_3464
  · exact projection_3465
  · exact projection_3466
  · exact projection_3467
  · exact projection_3468
  · exact projection_3469
  · exact projection_3470
  · exact projection_3471
  · exact projection_3472
  · exact projection_3473
  · exact projection_3474
  · exact projection_3475
  · exact projection_3476
  · exact projection_3477
  · exact projection_3478
  · exact projection_3479
  · exact projection_3480
  · exact projection_3481
  · exact projection_3482

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
