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
/- Source: ProjectionCertificates/R_m15e10q1_0119.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0119

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 837, 793, 681, 457, 118, 570, 594, 226, 674, 188, 412, 596, 788, 484, 137, 265, 521, 193, 321, 577, 641, 769, 50, 82, 530, 98, 162, 546, 194, 578, 642, 156, 52, 84, 276, 532, 100, 164, 324, 580, 388, 772, 56, 280, 536, 168, 552, 392, 592, 784, 224, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_837, vertices_793, vertices_681, vertices_457, vertices_118, vertices_570, vertices_594, vertices_226, vertices_674, vertices_188, vertices_412, vertices_596, vertices_788, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_50, vertices_82, vertices_530, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_156, vertices_52, vertices_84, vertices_276, vertices_532, vertices_100, vertices_164, vertices_324, vertices_580, vertices_388, vertices_772, vertices_56, vertices_280, vertices_536, vertices_168, vertices_552, vertices_392, vertices_592, vertices_784, vertices_224, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_837), (false, vertices_793), (false, vertices_681), (false, vertices_457), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_156), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_100), (true, vertices_164), (true, vertices_388), (true, vertices_56), (true, vertices_592), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_793) then 22 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_156) then 20 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_164) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_56) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_224) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
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
cert_row_4 0 0 2 3 4 8 570 50 1
cert_row_2 1 1 2 3 6 156
cert_row_4 2 0 1 3 4 5 118 50 1
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 8 2 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 2 0 1 3 4 50 118 1
cert_coverFacet 1 570
cert_cover_5 1 0 0 2 3 4 50 570 1
cert_coverFacet 2 594
cert_cover_2 2 3 0 5 8 82 594 3
cert_coverFacet 3 226
cert_cover_2 3 4 0 5 6 98 226 3
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 188
cert_cover_5 5 1 1 2 3 4 156 188 3
cert_coverFacet 6 412
cert_cover_5 6 1 1 2 3 7 156 412 3
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 788
cert_cover_2 8 3 1 7 8 276 788 3
cert_coverFacet 9 484
cert_cover_5 9 3 1 4 5 6 100 484 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0119

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0120.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0120

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 661, 453, 713, 865, 542, 182, 422, 58, 618, 802, 120, 216, 664, 496, 133, 261, 517, 193, 321, 577, 641, 769, 22, 166, 262, 518, 26, 42, 522, 50, 290, 546, 770, 148, 532, 388, 56, 88, 152, 536, 104, 200, 584, 648, 112, 176, 208, 656, 352, 608, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_661, vertices_453, vertices_713, vertices_865, vertices_542, vertices_182, vertices_422, vertices_58, vertices_618, vertices_802, vertices_120, vertices_216, vertices_664, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_22, vertices_166, vertices_262, vertices_518, vertices_26, vertices_42, vertices_522, vertices_50, vertices_290, vertices_546, vertices_770, vertices_148, vertices_532, vertices_388, vertices_56, vertices_88, vertices_152, vertices_536, vertices_104, vertices_200, vertices_584, vertices_648, vertices_112, vertices_176, vertices_208, vertices_656, vertices_352, vertices_608, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_661), (false, vertices_453), (false, vertices_713), (false, vertices_865), (true, vertices_22), (true, vertices_166), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_50), (true, vertices_290), (true, vertices_546), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_104), (true, vertices_112), (true, vertices_176), (true, vertices_208), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_661) then 20 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_713) then 23 else
  if p.val = (false, vertices_865) then 26 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_166) then 18 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_166), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
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
cert_row_4 0 3 4 5 6 7 496 112 3
cert_row_2 1 0 1 4 6 166
cert_row_4 2 0 1 2 3 8 542 22 2
cert_row_4 3 0 2 4 5 8 618 42 3
cert_rows
cert_pivot_2 7 6 1 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 2 0 1 2 3 22 542 2
cert_coverFacet 1 182
cert_cover_5 1 1 0 1 3 4 22 182 3
cert_coverFacet 2 422
cert_cover_5 2 1 0 1 4 7 166 422 3
cert_coverFacet 3 58
cert_cover_2 3 2 0 3 4 26 58 3
cert_coverFacet 4 618
cert_cover_5 4 3 0 2 4 5 42 618 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coverFacet 9 496
cert_cover_5 9 0 3 4 5 6 112 496 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0120

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0121.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0121

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 709, 313, 689, 465, 609, 206, 526, 614, 570, 298, 458, 908, 792, 912, 49, 145, 273, 97, 289, 545, 193, 321, 577, 641, 14, 70, 518, 42, 202, 266, 522, 98, 290, 546, 322, 140, 524, 196, 580, 644, 56, 280, 536, 296, 392, 776, 560, 400, 656, 784, 608, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_709, vertices_313, vertices_689, vertices_465, vertices_609, vertices_206, vertices_526, vertices_614, vertices_570, vertices_298, vertices_458, vertices_908, vertices_792, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_273, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_14, vertices_70, vertices_518, vertices_42, vertices_202, vertices_266, vertices_522, vertices_98, vertices_290, vertices_546, vertices_322, vertices_140, vertices_524, vertices_196, vertices_580, vertices_644, vertices_56, vertices_280, vertices_536, vertices_296, vertices_392, vertices_776, vertices_560, vertices_400, vertices_656, vertices_784, vertices_608, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_709), (false, vertices_313), (false, vertices_689), (false, vertices_465), (false, vertices_609), (true, vertices_14), (true, vertices_70), (true, vertices_518), (true, vertices_42), (true, vertices_202), (true, vertices_266), (true, vertices_522), (true, vertices_546), (true, vertices_140), (true, vertices_524), (true, vertices_536), (true, vertices_392), (true, vertices_776), (true, vertices_784), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 16 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (false, vertices_609) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_202) then 17 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
cert_nodeAtPriority_40 609 14 70 518 42 266 522 546 140 524 536 392 776 784 896 355 202 709 313 689 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 42 2
cert_row_4 1 0 1 4 5 8 614 70 2
cert_row_2 2 0 2 5 6 202
cert_row_4 3 1 2 6 7 8 908 140 3
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 2 0 1 2 5 14 206 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 614
cert_cover_5 2 1 0 1 4 5 70 614 2
cert_coverFacet 3 570
cert_cover_5 3 0 0 2 3 4 42 570 2
cert_coverFacet 4 298
cert_cover_2 4 2 0 4 7 42 298 3
cert_coverFacet 5 458
cert_cover_5 5 2 0 2 5 7 202 458 3
cert_coverFacet 6 908
cert_cover_5 6 3 1 2 6 7 140 908 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coverFacet 8 912
cert_cover_2 8 6 3 7 8 400 912 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0121

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0122.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0122

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 565, 357, 709, 681, 417, 790, 838, 154, 282, 426, 722, 316, 568, 664, 37, 69, 517, 161, 289, 545, 193, 321, 385, 641, 774, 26, 138, 266, 146, 274, 530, 194, 322, 578, 386, 52, 276, 532, 292, 324, 580, 56, 152, 280, 536, 168, 296, 552, 648, 560, 656, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_565, vertices_357, vertices_709, vertices_681, vertices_417, vertices_790, vertices_838, vertices_154, vertices_282, vertices_426, vertices_722, vertices_316, vertices_568, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_774, vertices_26, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_52, vertices_276, vertices_532, vertices_292, vertices_324, vertices_580, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_648, vertices_560, vertices_656, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_565), (false, vertices_357), (false, vertices_709), (false, vertices_681), (false, vertices_417), (true, vertices_774), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_578), (true, vertices_276), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_296), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_774) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
cert_nodeAtPriority_51 417 26 138 266 146 274 530 578 276 56 152 280 536 296 656 451 774 565 357 709 681
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 8 722 146 2
cert_row_2 1 0 1 7 8 774
cert_row_4 2 0 2 4 6 7 426 138 2
cert_row_4 3 1 2 3 4 7 316 52 1
cert_rows
cert_pivot_2 5 8 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 774 790 2
cert_coverFacet 1 838
cert_cover_5 1 1 0 1 5 7 774 838 2
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 426
cert_cover_5 4 2 0 2 4 6 138 426 2
cert_coverFacet 5 722
cert_cover_5 5 0 0 3 5 6 146 722 2
cert_coverFacet 6 316
cert_cover_5 6 3 1 2 3 4 52 316 1
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0122

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0123.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0123

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 403, 547, 707, 229, 389, 617, 810, 658, 786, 124, 316, 724, 404, 856, 35, 131, 259, 515, 37, 133, 261, 97, 545, 193, 577, 385, 146, 274, 530, 290, 546, 642, 770, 60, 84, 148, 276, 100, 292, 196, 388, 88, 280, 104, 296, 552, 584, 776, 592, 400, 656, 784, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_403, vertices_547, vertices_707, vertices_229, vertices_389, vertices_617, vertices_810, vertices_658, vertices_786, vertices_124, vertices_316, vertices_724, vertices_404, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_37, vertices_133, vertices_261, vertices_97, vertices_545, vertices_193, vertices_577, vertices_385, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_642, vertices_770, vertices_60, vertices_84, vertices_148, vertices_276, vertices_100, vertices_292, vertices_196, vertices_388, vertices_88, vertices_280, vertices_104, vertices_296, vertices_552, vertices_584, vertices_776, vertices_592, vertices_400, vertices_656, vertices_784, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_403), (false, vertices_547), (false, vertices_707), (false, vertices_229), (false, vertices_389), (false, vertices_617), (true, vertices_530), (true, vertices_770), (true, vertices_60), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_88), (true, vertices_280), (true, vertices_296), (true, vertices_776), (true, vertices_592), (true, vertices_656), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 15 else
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_60) then 20 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_784) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_4 0 0 2 4 7 8 810 290 1
cert_row_2 1 1 2 3 4 60
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 810
cert_cover_5 0 0 0 2 4 7 290 810 1
cert_coverFacet 1 658
cert_cover_2 1 3 0 6 8 146 658 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 124
cert_cover_5 3 1 1 2 3 5 60 124 3
cert_coverFacet 4 316
cert_cover_5 4 1 1 2 3 7 60 316 3
cert_coverFacet 5 724
cert_cover_5 5 2 1 3 5 6 84 724 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 856
cert_cover_5 7 3 2 3 5 7 88 856 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0123

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0124.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0124

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 181, 229, 665, 617, 457, 310, 842, 394, 650, 402, 658, 802, 468, 868, 165, 73, 137, 521, 49, 145, 529, 97, 545, 193, 138, 266, 522, 50, 146, 274, 530, 290, 546, 386, 642, 770, 52, 148, 276, 100, 292, 196, 324, 328, 584, 392, 648, 400, 656, 608, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_181, vertices_229, vertices_665, vertices_617, vertices_457, vertices_310, vertices_842, vertices_394, vertices_650, vertices_402, vertices_658, vertices_802, vertices_468, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_165, vertices_73, vertices_137, vertices_521, vertices_49, vertices_145, vertices_529, vertices_97, vertices_545, vertices_193, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_52, vertices_148, vertices_276, vertices_100, vertices_292, vertices_196, vertices_324, vertices_328, vertices_584, vertices_392, vertices_648, vertices_400, vertices_656, vertices_608, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_181), (false, vertices_229), (false, vertices_665), (false, vertices_617), (false, vertices_457), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_290), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_276), (true, vertices_292), (true, vertices_324), (true, vertices_400), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_800) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
cert_nodeAtPriority_42 138 2 266 1 522 146 274 290 386 642 770 276 292 324 400 800 832 563 181 229 665 617 457
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 266 2
cert_row_4 1 0 1 3 4 7 310 50 1
cert_row_4 2 1 3 5 6 7 468 148 2
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 1 0 1 3 4 50 310 1
cert_coverFacet 1 842
cert_cover_5 1 0 0 2 5 7 266 842 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 802
cert_cover_2 6 4 0 7 8 290 802 3
cert_coverFacet 7 468
cert_cover_5 7 2 1 3 5 6 148 468 2
cert_coverFacet 8 868
cert_cover_5 8 3 1 4 5 7 100 868 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0124

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0125.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0125

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 837, 793, 617, 393, 481, 398, 214, 790, 58, 282, 242, 628, 452, 568, 41, 137, 265, 521, 97, 161, 321, 577, 385, 769, 22, 134, 262, 26, 42, 138, 266, 50, 210, 274, 162, 84, 532, 196, 324, 580, 388, 772, 56, 280, 536, 552, 392, 112, 560, 784, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_837, vertices_793, vertices_617, vertices_393, vertices_481, vertices_398, vertices_214, vertices_790, vertices_58, vertices_282, vertices_242, vertices_628, vertices_452, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_321, vertices_577, vertices_385, vertices_769, vertices_22, vertices_134, vertices_262, vertices_26, vertices_42, vertices_138, vertices_266, vertices_50, vertices_210, vertices_274, vertices_162, vertices_84, vertices_532, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_56, vertices_280, vertices_536, vertices_552, vertices_392, vertices_112, vertices_560, vertices_784, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_837), (false, vertices_793), (false, vertices_617), (false, vertices_393), (false, vertices_481), (true, vertices_22), (true, vertices_134), (true, vertices_262), (true, vertices_26), (true, vertices_266), (true, vertices_50), (true, vertices_210), (true, vertices_274), (true, vertices_84), (true, vertices_532), (true, vertices_196), (true, vertices_388), (true, vertices_56), (true, vertices_112), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 16 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_50) then 6 else
  if p.val = (true, vertices_210) then 17 else
  if p.val = (true, vertices_274) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_560) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 393 22 134 262 26 266 50 274 84 532 196 388 56 112 560 171 210 837 793 617 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_2 1 0 3 5 6 210
cert_row_4 2 0 1 3 7 8 790 22 3
cert_row_4 3 1 3 4 5 8 628 84 2
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 214
cert_cover_5 1 1 0 1 3 5 22 214 3
cert_coverFacet 2 790
cert_cover_5 2 2 0 1 3 7 22 790 3
cert_coverFacet 3 58
cert_cover_2 3 2 0 3 4 26 58 3
cert_coverFacet 4 282
cert_cover_2 4 2 0 3 7 26 282 3
cert_coverFacet 5 242
cert_cover_5 5 1 0 3 4 5 50 242 3
cert_coverFacet 6 628
cert_cover_5 6 3 1 3 4 5 84 628 2
cert_coverFacet 7 452
cert_cover_2 7 5 1 6 7 196 452 3
cert_coverFacet 8 568
cert_cover_2 8 3 2 4 8 56 568 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0125

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0126.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0126

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 341, 709, 217, 281, 681, 777, 558, 358, 186, 282, 778, 370, 612, 752, 69, 261, 517, 25, 137, 265, 521, 81, 273, 193, 641, 769, 38, 262, 518, 26, 42, 266, 522, 50, 274, 354, 770, 100, 548, 324, 580, 152, 280, 168, 552, 776, 112, 176, 208, 336, 608, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_341, vertices_709, vertices_217, vertices_281, vertices_681, vertices_777, vertices_558, vertices_358, vertices_186, vertices_282, vertices_778, vertices_370, vertices_612, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_25, vertices_137, vertices_265, vertices_521, vertices_81, vertices_273, vertices_193, vertices_641, vertices_769, vertices_38, vertices_262, vertices_518, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_354, vertices_770, vertices_100, vertices_548, vertices_324, vertices_580, vertices_152, vertices_280, vertices_168, vertices_552, vertices_776, vertices_112, vertices_176, vertices_208, vertices_336, vertices_608, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_341), (false, vertices_709), (false, vertices_217), (false, vertices_281), (false, vertices_681), (false, vertices_777), (true, vertices_38), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_354), (true, vertices_100), (true, vertices_548), (true, vertices_112), (true, vertices_176), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_777) then 1 else
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
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
cert_nodeAtPriority_25 0 281 1 777 38 26 42 266 522 50 274 100 548 112 176 608 775 354 341 709 217 681
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 5 7 354
cert_row_4 1 0 1 2 4 8 558 38 2
cert_row_4 2 0 2 3 4 6 186 26 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 7 1 0 3
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
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0126

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0127.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0127

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 523, 195, 835, 557, 465, 929, 206, 526, 598, 60, 220, 564, 440, 880, 11, 67, 131, 515, 41, 521, 161, 545, 193, 321, 385, 769, 14, 70, 518, 138, 522, 194, 578, 28, 44, 204, 524, 52, 84, 532, 548, 56, 152, 168, 304, 560, 208, 336, 592, 400, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_523, vertices_195, vertices_835, vertices_557, vertices_465, vertices_929, vertices_206, vertices_526, vertices_598, vertices_60, vertices_220, vertices_564, vertices_440, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_131, vertices_515, vertices_41, vertices_521, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_14, vertices_70, vertices_518, vertices_138, vertices_522, vertices_194, vertices_578, vertices_28, vertices_44, vertices_204, vertices_524, vertices_52, vertices_84, vertices_532, vertices_548, vertices_56, vertices_152, vertices_168, vertices_304, vertices_560, vertices_208, vertices_336, vertices_592, vertices_400, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_523), (false, vertices_195), (false, vertices_835), (false, vertices_557), (false, vertices_465), (false, vertices_929), (true, vertices_14), (true, vertices_70), (true, vertices_518), (true, vertices_28), (true, vertices_204), (true, vertices_52), (true, vertices_84), (true, vertices_532), (true, vertices_56), (true, vertices_152), (true, vertices_304), (true, vertices_560), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 15 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (false, vertices_929) then 24 else
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
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_592) then 13 else
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
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
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
cert_row_4 3 3 4 5 7 8 880 304 2
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
cert_coverFacet 7 880
cert_cover_5 7 3 3 4 5 7 304 880 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0127

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0128.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0128

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 173, 333, 613, 425, 849, 678, 218, 794, 394, 658, 418, 204, 724, 344, 13, 37, 69, 169, 265, 289, 545, 321, 577, 769, 26, 138, 266, 146, 530, 162, 290, 546, 386, 642, 770, 76, 140, 164, 548, 196, 580, 644, 88, 280, 200, 328, 392, 208, 336, 592, 656, 784, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_173, vertices_333, vertices_613, vertices_425, vertices_849, vertices_678, vertices_218, vertices_794, vertices_394, vertices_658, vertices_418, vertices_204, vertices_724, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_169, vertices_265, vertices_289, vertices_545, vertices_321, vertices_577, vertices_769, vertices_26, vertices_138, vertices_266, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_88, vertices_280, vertices_200, vertices_328, vertices_392, vertices_208, vertices_336, vertices_592, vertices_656, vertices_784, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_173), (false, vertices_333), (false, vertices_613), (false, vertices_425), (false, vertices_849), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_196), (true, vertices_644), (true, vertices_88), (true, vertices_280), (true, vertices_200), (true, vertices_208), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_173) then 21 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 26 1 138 2 266 146 530 162 386 642 196 644 88 280 200 208 656 803 333 613 173 425 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 162 1
cert_row_4 1 0 2 3 7 8 794 26 3
cert_row_4 2 0 2 3 5 6 218 26 3
cert_row_4 3 1 3 5 6 8 724 196 1
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 162 678 1
cert_coverFacet 1 218
cert_cover_5 1 2 0 2 3 5 26 218 3
cert_coverFacet 2 794
cert_cover_5 2 1 0 2 3 7 26 794 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 204
cert_cover_2 6 2 1 5 6 76 204 3
cert_coverFacet 7 724
cert_cover_5 7 3 1 3 5 6 196 724 1
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0128

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0129.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0129

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 837, 217, 793, 329, 737, 174, 398, 790, 614, 402, 674, 364, 408, 232, 25, 73, 265, 145, 529, 193, 321, 577, 641, 769, 142, 38, 262, 518, 146, 274, 530, 162, 546, 386, 642, 44, 268, 100, 324, 580, 772, 152, 280, 104, 168, 200, 328, 392, 400, 784, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_837, vertices_217, vertices_793, vertices_329, vertices_737, vertices_174, vertices_398, vertices_790, vertices_614, vertices_402, vertices_674, vertices_364, vertices_408, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_142, vertices_38, vertices_262, vertices_518, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_386, vertices_642, vertices_44, vertices_268, vertices_100, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_104, vertices_168, vertices_200, vertices_328, vertices_392, vertices_400, vertices_784, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_837), (false, vertices_217), (false, vertices_793), (false, vertices_329), (false, vertices_737), (true, vertices_142), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_274), (true, vertices_162), (true, vertices_546), (true, vertices_386), (true, vertices_44), (true, vertices_268), (true, vertices_100), (true, vertices_104), (true, vertices_168), (true, vertices_392), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_793) then 22 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_142) then 17 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 329 38 262 518 274 162 546 386 44 268 100 104 168 392 400 659 142 837 217 793 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 6 142
cert_row_4 1 0 1 3 7 8 790 262 2
cert_row_4 2 0 1 4 5 8 614 38 3
cert_row_4 3 1 2 4 5 7 364 44 3
cert_rows
cert_pivot_2 6 3 0 1
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 0 0 1 2 4 142 174 3
cert_coverFacet 1 398
cert_cover_5 1 0 0 1 2 7 142 398 3
cert_coverFacet 2 790
cert_cover_5 2 1 0 1 3 7 262 790 2
cert_coverFacet 3 614
cert_cover_5 3 2 0 1 4 5 38 614 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 364
cert_cover_5 6 3 1 2 4 5 44 364 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 232
cert_cover_2 8 4 2 5 6 104 232 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0129

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0130.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0130

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 781, 601, 281, 465, 929, 590, 118, 678, 242, 60, 92, 300, 804, 440, 25, 265, 521, 81, 273, 193, 577, 385, 641, 769, 38, 70, 518, 114, 162, 194, 578, 642, 28, 44, 76, 268, 524, 52, 84, 292, 548, 772, 56, 88, 280, 296, 584, 176, 208, 400, 416, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_781, vertices_601, vertices_281, vertices_465, vertices_929, vertices_590, vertices_118, vertices_678, vertices_242, vertices_60, vertices_92, vertices_300, vertices_804, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_265, vertices_521, vertices_81, vertices_273, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_38, vertices_70, vertices_518, vertices_114, vertices_162, vertices_194, vertices_578, vertices_642, vertices_28, vertices_44, vertices_76, vertices_268, vertices_524, vertices_52, vertices_84, vertices_292, vertices_548, vertices_772, vertices_56, vertices_88, vertices_280, vertices_296, vertices_584, vertices_176, vertices_208, vertices_400, vertices_416, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_781), (false, vertices_601), (false, vertices_281), (false, vertices_465), (false, vertices_929), (true, vertices_38), (true, vertices_70), (true, vertices_518), (true, vertices_114), (true, vertices_162), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_52), (true, vertices_84), (true, vertices_292), (true, vertices_548), (true, vertices_56), (true, vertices_296), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_114) then 17 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_176) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 281 38 70 518 162 28 44 76 52 84 292 548 56 296 176 707 114 781 601 465 929
cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 6 7 440 56 3
cert_row_2 1 0 3 4 5 114
cert_row_4 2 0 1 2 5 8 590 70 2
cert_row_4 3 0 1 4 6 8 678 38 3
cert_rows
cert_pivot_2 7 3 2 0
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 2 0 1 2 5 70 590 2
cert_coverFacet 1 118
cert_cover_5 1 1 0 1 3 4 38 118 2
cert_coverFacet 2 678
cert_cover_5 2 3 0 1 4 6 38 678 3
cert_coverFacet 3 242
cert_cover_5 3 1 0 3 4 6 114 242 3
cert_coverFacet 4 60
cert_cover_2 4 2 1 3 4 28 60 3
cert_coverFacet 5 92
cert_cover_2 5 2 1 3 5 28 92 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coverFacet 8 440
cert_cover_5 8 0 2 3 4 6 56 440 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0130

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0132.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0132

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [115, 787, 355, 85, 661, 453, 905, 566, 810, 60, 92, 556, 716, 120, 488, 19, 99, 259, 21, 69, 133, 81, 529, 321, 385, 641, 769, 50, 530, 290, 546, 770, 28, 44, 76, 524, 52, 84, 532, 548, 196, 644, 56, 88, 104, 296, 552, 200, 392, 648, 776, 112, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_115, vertices_787, vertices_355, vertices_85, vertices_661, vertices_453, vertices_905, vertices_566, vertices_810, vertices_60, vertices_92, vertices_556, vertices_716, vertices_120, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_99, vertices_259, vertices_21, vertices_69, vertices_133, vertices_81, vertices_529, vertices_321, vertices_385, vertices_641, vertices_769, vertices_50, vertices_530, vertices_290, vertices_546, vertices_770, vertices_28, vertices_44, vertices_76, vertices_524, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_104, vertices_296, vertices_552, vertices_200, vertices_392, vertices_648, vertices_776, vertices_112, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_115), (false, vertices_787), (false, vertices_355), (false, vertices_85), (false, vertices_661), (false, vertices_453), (false, vertices_905), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_524), (true, vertices_52), (true, vertices_548), (true, vertices_56), (true, vertices_88), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_200)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_115) then 15 else
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_355) then 17 else
  if p.val = (false, vertices_85) then 0 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_905) then 22 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_200) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_4 0 0 1 3 4 8 566 50 1
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_4 2 1 2 5 6 8 716 76 3
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 50 566 1
cert_coverFacet 1 810
cert_cover_5 1 1 0 2 4 7 290 810 1
cert_coverFacet 2 60
cert_cover_2 2 2 1 3 4 28 60 3
cert_coverFacet 3 92
cert_cover_2 3 2 1 3 5 28 92 3
cert_coverFacet 4 556
cert_cover_2 4 2 1 4 8 44 556 3
cert_coverFacet 5 716
cert_cover_5 5 2 1 2 5 6 76 716 3
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0132

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0133.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0133

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 653, 217, 777, 849, 737, 62, 270, 678, 774, 306, 866, 188, 780, 496, 25, 137, 265, 521, 81, 273, 193, 577, 641, 769, 14, 38, 262, 518, 26, 266, 50, 274, 290, 546, 770, 60, 140, 268, 524, 164, 644, 772, 152, 776, 176, 304, 208, 336, 224, 352, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_653, vertices_217, vertices_777, vertices_849, vertices_737, vertices_62, vertices_270, vertices_678, vertices_774, vertices_306, vertices_866, vertices_188, vertices_780, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_521, vertices_81, vertices_273, vertices_193, vertices_577, vertices_641, vertices_769, vertices_14, vertices_38, vertices_262, vertices_518, vertices_26, vertices_266, vertices_50, vertices_274, vertices_290, vertices_546, vertices_770, vertices_60, vertices_140, vertices_268, vertices_524, vertices_164, vertices_644, vertices_772, vertices_152, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_224, vertices_352, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_653), (false, vertices_217), (false, vertices_777), (false, vertices_849), (false, vertices_737), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_60), (true, vertices_268), (true, vertices_164), (true, vertices_772), (true, vertices_176), (true, vertices_304), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 16 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_849) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_60) then 19 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
cert_nodeAtPriority_9 0 777 1 14 38 262 518 50 290 546 770 268 164 772 176 304 352 283 653 60 217 849 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 1 4 6 8 678 38 3
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 14 62 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 678
cert_cover_5 2 1 0 1 4 6 38 678 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 866
cert_cover_5 5 2 0 4 5 7 290 866 2
cert_coverFacet 6 188
cert_cover_5 6 0 1 2 3 6 60 188 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 176 496 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0133

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0134.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0134

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 109, 553, 841, 913, 481, 558, 118, 662, 242, 92, 284, 780, 788, 472, 41, 73, 521, 97, 161, 545, 321, 385, 641, 769, 22, 38, 518, 114, 146, 162, 546, 642, 28, 44, 76, 268, 524, 84, 276, 532, 100, 772, 88, 280, 552, 328, 776, 208, 400, 656, 784, 224, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_109, vertices_553, vertices_841, vertices_913, vertices_481, vertices_558, vertices_118, vertices_662, vertices_242, vertices_92, vertices_284, vertices_780, vertices_788, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_521, vertices_97, vertices_161, vertices_545, vertices_321, vertices_385, vertices_641, vertices_769, vertices_22, vertices_38, vertices_518, vertices_114, vertices_146, vertices_162, vertices_546, vertices_642, vertices_28, vertices_44, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_100, vertices_772, vertices_88, vertices_280, vertices_552, vertices_328, vertices_776, vertices_208, vertices_400, vertices_656, vertices_784, vertices_224, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_109), (false, vertices_553), (false, vertices_841), (false, vertices_913), (false, vertices_481), (true, vertices_22), (true, vertices_38), (true, vertices_518), (true, vertices_114), (true, vertices_146), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_772), (true, vertices_88), (true, vertices_280), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_109) then 19 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_913) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_114) then 17 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_208) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 553 22 38 518 146 28 268 524 84 276 532 772 88 280 208 675 114 109 841 913 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 5 6 7 472 88 3
cert_row_2 1 0 3 4 5 114
cert_row_4 2 0 1 2 4 8 558 38 2
cert_row_4 3 0 1 3 6 8 662 22 3
cert_rows
cert_pivot_2 7 5 2 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 2 0 1 2 4 38 558 2
cert_coverFacet 1 118
cert_cover_5 1 1 0 1 3 4 22 118 3
cert_coverFacet 2 662
cert_cover_5 2 3 0 1 3 6 22 662 3
cert_coverFacet 3 242
cert_cover_5 3 1 0 3 4 6 114 242 3
cert_coverFacet 4 92
cert_cover_2 4 2 1 3 5 28 92 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 472
cert_cover_5 8 0 2 3 5 6 88 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0134

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0135.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0135

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 787, 643, 653, 85, 837, 369, 682, 402, 866, 418, 220, 620, 248, 432, 19, 131, 515, 21, 69, 133, 517, 81, 273, 321, 641, 769, 146, 274, 162, 290, 546, 386, 642, 770, 76, 140, 524, 84, 148, 580, 216, 104, 168, 552, 648, 112, 176, 304, 400, 352, 608, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_787, vertices_643, vertices_653, vertices_85, vertices_837, vertices_369, vertices_682, vertices_402, vertices_866, vertices_418, vertices_220, vertices_620, vertices_248, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_515, vertices_21, vertices_69, vertices_133, vertices_517, vertices_81, vertices_273, vertices_321, vertices_641, vertices_769, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_84, vertices_148, vertices_580, vertices_216, vertices_104, vertices_168, vertices_552, vertices_648, vertices_112, vertices_176, vertices_304, vertices_400, vertices_352, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_787), (false, vertices_643), (false, vertices_653), (false, vertices_85), (false, vertices_837), (false, vertices_369), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_76), (true, vertices_216), (true, vertices_104), (true, vertices_168), (true, vertices_552), (true, vertices_176), (true, vertices_400), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 15 else
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_85) then 1 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_216) then 21 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 5 6 216
cert_row_4 1 0 2 4 6 8 682 162 1
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 1 2 4 5 8 620 76 2
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 682
cert_cover_5 0 1 0 2 4 6 162 682 1
cert_coverFacet 1 402
cert_cover_2 1 3 0 6 7 146 402 3
cert_coverFacet 2 866
cert_cover_5 2 2 0 4 5 7 290 866 2
cert_coverFacet 3 418
cert_cover_2 3 4 0 6 7 162 418 3
cert_coverFacet 4 220
cert_cover_5 4 0 1 2 3 5 76 220 2
cert_coverFacet 5 620
cert_cover_5 5 3 1 2 4 5 76 620 2
cert_coverFacet 6 248
cert_cover_5 6 0 2 3 4 5 216 248 2
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0135

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0136.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0136

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [87, 539, 195, 899, 533, 837, 481, 218, 682, 60, 540, 556, 372, 932, 248, 19, 67, 131, 515, 21, 69, 517, 529, 193, 321, 385, 769, 26, 138, 522, 82, 194, 642, 28, 44, 524, 52, 84, 532, 292, 548, 324, 772, 56, 216, 536, 168, 552, 112, 224, 352, 416, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_87, vertices_539, vertices_195, vertices_899, vertices_533, vertices_837, vertices_481, vertices_218, vertices_682, vertices_60, vertices_540, vertices_556, vertices_372, vertices_932, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_131, vertices_515, vertices_21, vertices_69, vertices_517, vertices_529, vertices_193, vertices_321, vertices_385, vertices_769, vertices_26, vertices_138, vertices_522, vertices_82, vertices_194, vertices_642, vertices_28, vertices_44, vertices_524, vertices_52, vertices_84, vertices_532, vertices_292, vertices_548, vertices_324, vertices_772, vertices_56, vertices_216, vertices_536, vertices_168, vertices_552, vertices_112, vertices_224, vertices_352, vertices_416, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_87), (false, vertices_539), (false, vertices_195), (false, vertices_899), (false, vertices_533), (false, vertices_837), (false, vertices_481), (true, vertices_138), (true, vertices_28), (true, vertices_44), (true, vertices_524), (true, vertices_52), (true, vertices_292), (true, vertices_548), (true, vertices_56), (true, vertices_216), (true, vertices_168), (true, vertices_552), (true, vertices_112), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_87) then 15 else
  if p.val = (false, vertices_539) then 16 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_216) then 21 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_87), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
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
cert_row_4 0 0 2 4 6 8 682 138 2
cert_row_2 1 2 3 5 6 216
cert_row_4 2 1 3 4 5 7 372 52 3
cert_row_4 3 1 4 6 7 8 932 292 2
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 218
cert_cover_5 0 1 0 2 3 5 26 218 3
cert_coverFacet 1 682
cert_cover_5 1 0 0 2 4 6 138 682 2
cert_coverFacet 2 60
cert_cover_2 2 2 1 3 4 28 60 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 556
cert_cover_2 4 2 1 4 8 44 556 3
cert_coverFacet 5 372
cert_cover_5 5 2 1 3 4 5 52 372 3
cert_coverFacet 6 932
cert_cover_5 6 3 1 4 6 7 292 932 2
cert_coverFacet 7 248
cert_cover_5 7 1 2 3 4 5 56 248 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0136

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0137.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0137

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 173, 269, 789, 217, 281, 689, 358, 774, 346, 722, 786, 610, 364, 744, 13, 37, 261, 517, 25, 137, 265, 145, 273, 529, 161, 545, 38, 262, 518, 82, 274, 530, 98, 546, 322, 578, 770, 44, 268, 356, 772, 88, 280, 104, 168, 200, 328, 208, 656, 784, 608, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_173, vertices_269, vertices_789, vertices_217, vertices_281, vertices_689, vertices_358, vertices_774, vertices_346, vertices_722, vertices_786, vertices_610, vertices_364, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_261, vertices_517, vertices_25, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_161, vertices_545, vertices_38, vertices_262, vertices_518, vertices_82, vertices_274, vertices_530, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_44, vertices_268, vertices_356, vertices_772, vertices_88, vertices_280, vertices_104, vertices_168, vertices_200, vertices_328, vertices_208, vertices_656, vertices_784, vertices_608, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_173), (false, vertices_269), (false, vertices_789), (false, vertices_217), (false, vertices_281), (false, vertices_689), (true, vertices_262), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_356), (true, vertices_104), (true, vertices_328), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 15 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_356) then 19 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_54 269 281 262 82 274 530 98 322 578 770 104 328 608 704 551 173 789 356 217 689
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 7 356
cert_row_4 1 0 2 3 5 7 346 82 1
cert_row_4 2 0 3 5 6 8 722 82 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 0 0 1 4 5 38 358 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 346
cert_cover_5 2 1 0 2 3 5 82 346 1
cert_coverFacet 3 722
cert_cover_5 3 2 0 3 5 6 82 722 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 610
cert_cover_2 5 4 0 5 8 98 610 3
cert_coverFacet 6 364
cert_cover_5 6 0 1 2 4 5 44 364 3
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 104 744 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0137

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0138.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0138

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 837, 361, 681, 817, 705, 94, 790, 710, 154, 690, 348, 408, 424, 432, 41, 73, 137, 289, 545, 193, 321, 577, 641, 769, 22, 70, 518, 26, 74, 138, 146, 530, 194, 642, 92, 276, 324, 580, 772, 152, 280, 168, 296, 328, 392, 176, 304, 560, 400, 784, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_837, vertices_361, vertices_681, vertices_817, vertices_705, vertices_94, vertices_790, vertices_710, vertices_154, vertices_690, vertices_348, vertices_408, vertices_424, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_137, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_22, vertices_70, vertices_518, vertices_26, vertices_74, vertices_138, vertices_146, vertices_530, vertices_194, vertices_642, vertices_92, vertices_276, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_168, vertices_296, vertices_328, vertices_392, vertices_176, vertices_304, vertices_560, vertices_400, vertices_784, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_837), (false, vertices_361), (false, vertices_681), (false, vertices_817), (false, vertices_705), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_26), (true, vertices_146), (true, vertices_530), (true, vertices_642), (true, vertices_92), (true, vertices_276), (true, vertices_152), (true, vertices_280), (true, vertices_392), (true, vertices_176), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_92) then 19 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 705 2 22 1 70 3 518 26 146 530 642 276 152 280 392 176 400 416 203 837 92 361 681 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 5 92
cert_row_4 1 0 1 3 7 8 790 22 3
cert_row_4 2 0 1 5 6 8 710 70 3
cert_row_4 3 0 3 4 6 8 690 146 2
cert_rows
cert_pivot_2 2 7 1 0
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 22 94 2
cert_coverFacet 1 790
cert_cover_5 1 1 0 1 3 7 22 790 3
cert_coverFacet 2 710
cert_cover_5 2 2 0 1 5 6 70 710 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 690
cert_cover_5 4 3 0 3 4 6 146 690 2
cert_coverFacet 5 348
cert_cover_5 5 0 1 2 3 7 92 348 3
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0138

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0139.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0139

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 203, 787, 387, 665, 585, 433, 806, 454, 620, 484, 248, 312, 792, 808, 67, 131, 259, 515, 73, 137, 521, 145, 273, 529, 577, 385, 70, 262, 518, 194, 386, 770, 100, 292, 548, 452, 580, 56, 152, 280, 536, 104, 296, 552, 200, 584, 776, 176, 304, 784, 224, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_203, vertices_787, vertices_387, vertices_665, vertices_585, vertices_433, vertices_806, vertices_454, vertices_620, vertices_484, vertices_248, vertices_312, vertices_792, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_73, vertices_137, vertices_521, vertices_145, vertices_273, vertices_529, vertices_577, vertices_385, vertices_70, vertices_262, vertices_518, vertices_194, vertices_386, vertices_770, vertices_100, vertices_292, vertices_548, vertices_452, vertices_580, vertices_56, vertices_152, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_200, vertices_584, vertices_776, vertices_176, vertices_304, vertices_784, vertices_224, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_203), (false, vertices_787), (false, vertices_387), (false, vertices_665), (false, vertices_585), (false, vertices_433), (true, vertices_262), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_452), (true, vertices_56), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_224), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 15 else
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_787) then 17 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_585) then 1 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_452) then 19 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
cert_nodeAtPriority_47 387 585 262 100 292 548 56 280 104 296 552 776 224 800 583 203 787 452 665 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 262 2
cert_row_2 1 1 5 6 7 452
cert_row_4 2 1 2 4 5 8 620 100 1
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 262 806 2
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 6 70 454 3
cert_coverFacet 2 620
cert_cover_5 2 2 1 2 4 5 100 620 1
cert_coverFacet 3 484
cert_cover_5 3 1 1 4 5 6 100 484 3
cert_coverFacet 4 248
cert_cover_5 4 3 2 3 4 5 56 248 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 792
cert_cover_2 6 3 2 7 8 280 792 3
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0139

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0140.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0140

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 117, 905, 561, 721, 481, 110, 270, 566, 774, 362, 92, 668, 780, 472, 49, 81, 529, 97, 289, 545, 193, 385, 641, 769, 14, 38, 262, 518, 106, 266, 290, 546, 770, 28, 76, 268, 524, 52, 84, 532, 100, 772, 88, 152, 328, 392, 648, 776, 560, 208, 656, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_117, vertices_905, vertices_561, vertices_721, vertices_481, vertices_110, vertices_270, vertices_566, vertices_774, vertices_362, vertices_92, vertices_668, vertices_780, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_38, vertices_262, vertices_518, vertices_106, vertices_266, vertices_290, vertices_546, vertices_770, vertices_28, vertices_76, vertices_268, vertices_524, vertices_52, vertices_84, vertices_532, vertices_100, vertices_772, vertices_88, vertices_152, vertices_328, vertices_392, vertices_648, vertices_776, vertices_560, vertices_208, vertices_656, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_117), (false, vertices_905), (false, vertices_561), (false, vertices_721), (false, vertices_481), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_106), (true, vertices_266), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_532), (true, vertices_772), (true, vertices_88), (true, vertices_152), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_117) then 19 else
  if p.val = (false, vertices_905) then 21 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_106) then 17 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_328) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 561 14 38 262 518 266 28 76 268 524 532 772 88 152 328 803 106 117 905 721 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 5 6 7 472 88 3
cert_row_2 1 0 2 4 5 106
cert_row_4 2 0 1 3 4 8 566 38 2
cert_row_4 3 1 2 3 6 8 668 28 3
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 566
cert_cover_5 2 2 0 1 3 4 38 566 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 362
cert_cover_5 4 1 0 2 4 7 106 362 3
cert_coverFacet 5 92
cert_cover_2 5 2 1 3 5 28 92 3
cert_coverFacet 6 668
cert_cover_5 6 3 1 2 3 6 28 668 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 472
cert_cover_5 8 0 2 3 5 6 88 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0140

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0141.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0141

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 805, 453, 361, 625, 705, 542, 398, 154, 722, 796, 248, 312, 456, 816, 133, 261, 517, 97, 289, 545, 193, 321, 577, 641, 14, 134, 518, 26, 138, 146, 530, 642, 540, 268, 388, 772, 56, 152, 280, 104, 296, 200, 328, 392, 112, 304, 560, 208, 592, 784, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_805, vertices_453, vertices_361, vertices_625, vertices_705, vertices_542, vertices_398, vertices_154, vertices_722, vertices_796, vertices_248, vertices_312, vertices_456, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_14, vertices_134, vertices_518, vertices_26, vertices_138, vertices_146, vertices_530, vertices_642, vertices_540, vertices_268, vertices_388, vertices_772, vertices_56, vertices_152, vertices_280, vertices_104, vertices_296, vertices_200, vertices_328, vertices_392, vertices_112, vertices_304, vertices_560, vertices_208, vertices_592, vertices_784, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_805), (false, vertices_453), (false, vertices_361), (false, vertices_625), (false, vertices_705), (true, vertices_14), (true, vertices_26), (true, vertices_138), (true, vertices_146), (true, vertices_530), (true, vertices_540), (true, vertices_268), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_200), (true, vertices_392), (true, vertices_304), (true, vertices_208), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_540) then 20 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_784) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_540), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_2 1 1 2 3 8 540
cert_row_4 2 0 3 5 6 8 722 146 2
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 7 1 0 2
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 1 0 1 2 3 14 542 3
cert_coverFacet 1 398
cert_cover_5 1 0 0 1 2 6 14 398 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 722
cert_cover_5 3 2 0 3 5 6 146 722 2
cert_coverFacet 4 796
cert_cover_5 4 1 1 2 3 7 540 796 3
cert_coverFacet 5 248
cert_cover_5 5 3 2 3 4 5 56 248 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 456
cert_cover_2 7 5 2 6 7 200 456 3
cert_coverFacet 8 816
cert_cover_2 8 4 3 7 8 304 816 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0141

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0142.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0142

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 653, 773, 233, 841, 433, 353, 598, 150, 838, 370, 402, 692, 632, 680, 133, 261, 517, 73, 137, 521, 97, 161, 289, 321, 385, 769, 22, 582, 134, 262, 82, 146, 274, 322, 386, 148, 532, 644, 772, 104, 168, 552, 584, 648, 112, 176, 304, 560, 592, 400, 352, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_653, vertices_773, vertices_233, vertices_841, vertices_433, vertices_353, vertices_598, vertices_150, vertices_838, vertices_370, vertices_402, vertices_692, vertices_632, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_97, vertices_161, vertices_289, vertices_321, vertices_385, vertices_769, vertices_22, vertices_582, vertices_134, vertices_262, vertices_82, vertices_146, vertices_274, vertices_322, vertices_386, vertices_148, vertices_532, vertices_644, vertices_772, vertices_104, vertices_168, vertices_552, vertices_584, vertices_648, vertices_112, vertices_176, vertices_304, vertices_560, vertices_592, vertices_400, vertices_352, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_653), (false, vertices_773), (false, vertices_233), (false, vertices_841), (false, vertices_433), (false, vertices_353), (true, vertices_22), (true, vertices_582), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_322), (true, vertices_148), (true, vertices_532), (true, vertices_552), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 15 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_353) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_582) then 16 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_582), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
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
cert_row_4 0 0 3 4 5 7 370 82 2
cert_row_2 1 0 1 5 8 582
cert_row_4 2 1 3 4 6 8 692 148 2
cert_row_4 3 2 3 4 5 8 632 104 1
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 1 0 1 3 5 22 598 3
cert_coverFacet 1 150
cert_cover_2 1 1 0 3 6 22 150 3
cert_coverFacet 2 838
cert_cover_5 2 1 0 1 5 7 582 838 3
cert_coverFacet 3 370
cert_cover_5 3 0 0 3 4 5 82 370 2
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 692
cert_cover_5 5 2 1 3 4 6 148 692 2
cert_coverFacet 6 632
cert_cover_5 6 3 2 3 4 5 104 632 1
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0142

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0143.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0143

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 155, 283, 675, 241, 817, 270, 526, 714, 364, 588, 740, 804, 472, 368, 27, 131, 259, 515, 49, 145, 273, 161, 545, 769, 14, 262, 518, 138, 266, 522, 642, 76, 268, 524, 100, 292, 548, 580, 772, 152, 280, 200, 328, 584, 112, 304, 208, 336, 224, 352, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_155, vertices_283, vertices_675, vertices_241, vertices_817, vertices_270, vertices_526, vertices_714, vertices_364, vertices_588, vertices_740, vertices_804, vertices_472, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_131, vertices_259, vertices_515, vertices_49, vertices_145, vertices_273, vertices_161, vertices_545, vertices_769, vertices_14, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_642, vertices_76, vertices_268, vertices_524, vertices_100, vertices_292, vertices_548, vertices_580, vertices_772, vertices_152, vertices_280, vertices_200, vertices_328, vertices_584, vertices_112, vertices_304, vertices_208, vertices_336, vertices_224, vertices_352, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_155), (false, vertices_283), (false, vertices_675), (false, vertices_241), (false, vertices_817), (true, vertices_14), (true, vertices_522), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_580), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_336), (true, vertices_352), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 15 21 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_155) then 18 else
  if p.val = (false, vertices_283) then 19 else
  if p.val = (false, vertices_675) then 20 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 138 2
cert_row_4 1 1 4 5 6 8 740 100 3
cert_row_4 2 1 2 4 5 7 364 76 2
cert_row_4 3 2 3 5 6 7 472 152 2
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 714
cert_cover_5 2 0 0 2 5 6 138 714 2
cert_coverFacet 3 364
cert_cover_5 3 2 1 2 4 5 76 364 2
cert_coverFacet 4 588
cert_cover_2 4 2 1 5 8 76 588 3
cert_coverFacet 5 740
cert_cover_5 5 1 1 4 5 6 100 740 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 152 472 2
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0143

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0144.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0144

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 279, 333, 229, 689, 465, 590, 270, 550, 906, 818, 612, 744, 456, 912, 23, 37, 69, 261, 49, 145, 273, 161, 193, 321, 14, 38, 262, 518, 266, 522, 50, 274, 546, 770, 76, 268, 100, 548, 580, 200, 328, 584, 392, 648, 560, 400, 656, 784, 224, 608, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_279, vertices_333, vertices_229, vertices_689, vertices_465, vertices_590, vertices_270, vertices_550, vertices_906, vertices_818, vertices_612, vertices_744, vertices_456, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_37, vertices_69, vertices_261, vertices_49, vertices_145, vertices_273, vertices_161, vertices_193, vertices_321, vertices_14, vertices_38, vertices_262, vertices_518, vertices_266, vertices_522, vertices_50, vertices_274, vertices_546, vertices_770, vertices_76, vertices_268, vertices_100, vertices_548, vertices_580, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_560, vertices_400, vertices_656, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_279), (false, vertices_333), (false, vertices_229), (false, vertices_689), (false, vertices_465), (true, vertices_14), (true, vertices_518), (true, vertices_266), (true, vertices_522), (true, vertices_546), (true, vertices_770), (true, vertices_548), (true, vertices_580), (true, vertices_200), (true, vertices_584), (true, vertices_392), (true, vertices_648), (true, vertices_784), (true, vertices_608), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 16 else
  if p.val = (false, vertices_279) then 17 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_229) then 20 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 0 3 4 7 8 818 50 3
cert_row_4 2 0 2 6 7 8 906 266 2
cert_row_4 3 2 4 5 6 8 744 200 1
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 906
cert_cover_5 3 2 0 2 6 7 266 906 2
cert_coverFacet 4 818
cert_cover_5 4 1 0 3 4 7 50 818 3
cert_coverFacet 5 612
cert_cover_2 5 4 1 5 8 100 612 3
cert_coverFacet 6 744
cert_cover_5 6 3 2 4 5 6 200 744 1
cert_coverFacet 7 456
cert_cover_2 7 5 2 6 7 200 456 3
cert_coverFacet 8 912
cert_cover_2 8 6 3 7 8 400 912 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0144

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0145.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0145

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 789, 357, 677, 185, 537, 305, 838, 218, 346, 778, 738, 612, 792, 496, 37, 261, 517, 25, 137, 521, 49, 273, 529, 161, 289, 641, 90, 138, 266, 522, 194, 322, 578, 642, 770, 100, 548, 324, 580, 772, 152, 280, 536, 776, 176, 304, 208, 336, 784, 224, 352, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_789, vertices_357, vertices_677, vertices_185, vertices_537, vertices_305, vertices_838, vertices_218, vertices_346, vertices_778, vertices_738, vertices_612, vertices_792, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_25, vertices_137, vertices_521, vertices_49, vertices_273, vertices_529, vertices_161, vertices_289, vertices_641, vertices_90, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_536, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_784, vertices_224, vertices_352, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_789), (false, vertices_357), (false, vertices_677), (false, vertices_185), (false, vertices_537), (false, vertices_305), (true, vertices_90), (true, vertices_266), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_580), (true, vertices_280), (true, vertices_776), (true, vertices_208), (true, vertices_336), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_185) then 22 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (true, vertices_90) then 16 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 537 1 305 266 194 322 578 770 580 280 776 208 336 224 608 651 90 789 357 677 185
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 6 90 218 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 7 90 346 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 194 738 1
cert_coverFacet 5 612
cert_cover_2 5 4 1 5 8 100 612 3
cert_coverFacet 6 792
cert_cover_2 6 3 2 7 8 280 792 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 176 496 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0145

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0146.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0146

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 267, 835, 613, 121, 281, 465, 902, 410, 666, 692, 484, 836, 568, 240, 11, 259, 515, 25, 41, 265, 81, 273, 97, 545, 321, 577, 154, 266, 522, 386, 642, 770, 100, 164, 548, 324, 580, 388, 644, 772, 56, 280, 536, 552, 112, 176, 560, 208, 400, 656, 224, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_267, vertices_835, vertices_613, vertices_121, vertices_281, vertices_465, vertices_902, vertices_410, vertices_666, vertices_692, vertices_484, vertices_836, vertices_568, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_259, vertices_515, vertices_25, vertices_41, vertices_265, vertices_81, vertices_273, vertices_97, vertices_545, vertices_321, vertices_577, vertices_154, vertices_266, vertices_522, vertices_386, vertices_642, vertices_770, vertices_100, vertices_164, vertices_548, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_280, vertices_536, vertices_552, vertices_112, vertices_176, vertices_560, vertices_208, vertices_400, vertices_656, vertices_224, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_267), (false, vertices_835), (false, vertices_613), (false, vertices_121), (false, vertices_281), (false, vertices_465), (true, vertices_154), (true, vertices_386), (true, vertices_642), (true, vertices_164), (true, vertices_324), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_536), (true, vertices_176), (true, vertices_560), (true, vertices_656), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 15 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_121) then 21 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_154) then 17 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_224) then 13 else
  0
cert_priority
cert_nodeAtPriority_23 267 281 386 642 164 324 388 644 772 536 176 560 656 224 555 835 154 613 121 465
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
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0146

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0147.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0147

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 61, 525, 213, 837, 361, 113, 30, 526, 662, 186, 426, 962, 708, 496, 13, 21, 69, 517, 41, 265, 521, 49, 81, 97, 321, 769, 14, 22, 518, 26, 170, 266, 522, 146, 386, 642, 770, 28, 524, 148, 196, 580, 644, 56, 296, 112, 176, 208, 352, 416, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_61, vertices_525, vertices_213, vertices_837, vertices_361, vertices_113, vertices_30, vertices_526, vertices_662, vertices_186, vertices_426, vertices_962, vertices_708, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_69, vertices_517, vertices_41, vertices_265, vertices_521, vertices_49, vertices_81, vertices_97, vertices_321, vertices_769, vertices_14, vertices_22, vertices_518, vertices_26, vertices_170, vertices_266, vertices_522, vertices_146, vertices_386, vertices_642, vertices_770, vertices_28, vertices_524, vertices_148, vertices_196, vertices_580, vertices_644, vertices_56, vertices_296, vertices_112, vertices_176, vertices_208, vertices_352, vertices_416, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_61), (false, vertices_525), (false, vertices_213), (false, vertices_837), (false, vertices_361), (false, vertices_113), (true, vertices_14), (true, vertices_22), (true, vertices_518), (true, vertices_26), (true, vertices_170), (true, vertices_146), (true, vertices_386), (true, vertices_642), (true, vertices_644), (true, vertices_176), (true, vertices_416), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_61) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_113) then 1 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_22) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_170) then 16 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_448) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 525 1 113 14 22 518 26 146 386 642 644 176 416 448 704 779 170 61 213 837 361
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 6 170
cert_row_4 1 0 1 3 6 8 662 22 3
cert_row_4 2 0 5 6 7 8 962 386 1
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 662
cert_cover_5 2 1 0 1 3 6 22 662 3
cert_coverFacet 3 186
cert_cover_5 3 0 0 2 3 4 26 186 3
cert_coverFacet 4 426
cert_cover_5 4 0 0 2 4 7 170 426 3
cert_coverFacet 5 962
cert_cover_5 5 2 0 5 6 7 386 962 1
cert_coverFacet 6 708
cert_cover_2 6 5 1 6 8 196 708 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0147

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0148.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0148

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 301, 525, 677, 409, 241, 305, 838, 218, 346, 778, 738, 780, 372, 612, 13, 37, 517, 137, 265, 521, 49, 145, 273, 161, 289, 641, 90, 138, 266, 522, 194, 322, 578, 642, 770, 268, 524, 100, 292, 548, 324, 580, 772, 152, 280, 776, 112, 304, 208, 336, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_301, vertices_525, vertices_677, vertices_409, vertices_241, vertices_305, vertices_838, vertices_218, vertices_346, vertices_778, vertices_738, vertices_780, vertices_372, vertices_612] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_517, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_273, vertices_161, vertices_289, vertices_641, vertices_90, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_268, vertices_524, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_776, vertices_112, vertices_304, vertices_208, vertices_336, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_301), (false, vertices_525), (false, vertices_677), (false, vertices_409), (false, vertices_241), (false, vertices_305), (true, vertices_90), (true, vertices_266), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_100), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_776), (true, vertices_336), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (true, vertices_90) then 16 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 525 1 305 266 194 322 578 770 100 324 580 772 776 336 608 651 90 301 677 409 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 4 5 6 8 738 194 1
cert_row_4 2 0 1 5 7 8 838 322 1
cert_row_4 3 1 3 4 5 7 372 100 1
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 2 0 1 5 7 322 838 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 6 90 218 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 7 90 346 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 738
cert_cover_5 4 1 0 4 5 6 194 738 1
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 372
cert_cover_5 6 3 1 3 4 5 100 372 1
cert_coverFacet 7 612
cert_cover_2 7 4 1 5 8 100 612 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0148

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0149.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0149

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 23, 563, 285, 713, 393, 913, 310, 358, 582, 738, 460, 588, 496, 688, 7, 19, 515, 13, 21, 137, 265, 521, 273, 529, 385, 641, 22, 294, 70, 518, 50, 98, 546, 578, 76, 268, 524, 276, 324, 580, 200, 584, 392, 176, 304, 560, 400, 656, 224, 352, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_23, vertices_563, vertices_285, vertices_713, vertices_393, vertices_913, vertices_310, vertices_358, vertices_582, vertices_738, vertices_460, vertices_588, vertices_496, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_19, vertices_515, vertices_13, vertices_21, vertices_137, vertices_265, vertices_521, vertices_273, vertices_529, vertices_385, vertices_641, vertices_22, vertices_294, vertices_70, vertices_518, vertices_50, vertices_98, vertices_546, vertices_578, vertices_76, vertices_268, vertices_524, vertices_276, vertices_324, vertices_580, vertices_200, vertices_584, vertices_392, vertices_176, vertices_304, vertices_560, vertices_400, vertices_656, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_23), (false, vertices_563), (false, vertices_285), (false, vertices_713), (false, vertices_393), (false, vertices_913), (true, vertices_294), (true, vertices_70), (true, vertices_98), (true, vertices_578), (true, vertices_76), (true, vertices_324), (true, vertices_580), (true, vertices_176), (true, vertices_304), (true, vertices_224), (true, vertices_352), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 15 else
  if p.val = (false, vertices_23) then 0 else
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_285) then 19 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_393) then 1 else
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
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
cert_nodeAtPriority_23 23 393 70 98 578 76 324 580 176 304 224 352 672 448 527 563 294 285 713 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 6 8 738 98 3
cert_row_2 1 0 1 4 7 294
cert_row_4 2 1 2 5 6 7 460 76 3
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 8 0 1 3
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 1 0 1 3 4 22 310 3
cert_coverFacet 1 358
cert_cover_5 1 1 0 1 4 5 294 358 3
cert_coverFacet 2 582
cert_cover_2 2 1 0 5 8 70 582 3
cert_coverFacet 3 738
cert_cover_5 3 0 0 4 5 6 98 738 3
cert_coverFacet 4 460
cert_cover_5 4 2 1 2 5 6 76 460 3
cert_coverFacet 5 588
cert_cover_2 5 2 1 5 8 76 588 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 176 496 2
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0149

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2733 : Certifies 2733 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0119.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2734 : Certifies 2734 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0120.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2735 : Certifies 2735 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0121.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2736 : Certifies 2736 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0122.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2737 : Certifies 2737 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0123.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2738 : Certifies 2738 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0124.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2739 : Certifies 2739 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0125.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2740 : Certifies 2740 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0126.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2741 : Certifies 2741 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0127.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2742 : Certifies 2742 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0128.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2743 : Certifies 2743 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0129.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2744 : Certifies 2744 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0130.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2745 : Certifies 2745 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0132.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2746 : Certifies 2746 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0133.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2747 : Certifies 2747 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0134.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2748 : Certifies 2748 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0135.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2749 : Certifies 2749 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0136.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2750 : Certifies 2750 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0137.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2751 : Certifies 2751 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0138.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2752 : Certifies 2752 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0139.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2753 : Certifies 2753 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0140.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2754 : Certifies 2754 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0141.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2755 : Certifies 2755 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0142.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2756 : Certifies 2756 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0143.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2757 : Certifies 2757 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0144.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2758 : Certifies 2758 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0145.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2759 : Certifies 2759 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0146.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2760 : Certifies 2760 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0147.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2761 : Certifies 2761 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0148.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2762 : Certifies 2762 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0149.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B090 (j : Fin 30) :
    Certifies (2733 + j.val) := by
  fin_cases j
  · exact projection_2733
  · exact projection_2734
  · exact projection_2735
  · exact projection_2736
  · exact projection_2737
  · exact projection_2738
  · exact projection_2739
  · exact projection_2740
  · exact projection_2741
  · exact projection_2742
  · exact projection_2743
  · exact projection_2744
  · exact projection_2745
  · exact projection_2746
  · exact projection_2747
  · exact projection_2748
  · exact projection_2749
  · exact projection_2750
  · exact projection_2751
  · exact projection_2752
  · exact projection_2753
  · exact projection_2754
  · exact projection_2755
  · exact projection_2756
  · exact projection_2757
  · exact projection_2758
  · exact projection_2759
  · exact projection_2760
  · exact projection_2761
  · exact projection_2762

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
