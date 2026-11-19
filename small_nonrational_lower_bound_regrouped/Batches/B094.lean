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
/- Source: ProjectionCertificates/R_m15e10q1_0242.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0242

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 787, 451, 541, 405, 362, 226, 674, 802, 220, 620, 708, 824, 472, 736, 131, 259, 515, 21, 133, 517, 273, 529, 385, 98, 162, 290, 546, 194, 322, 642, 770, 28, 76, 524, 148, 196, 580, 644, 216, 280, 536, 104, 296, 552, 328, 400, 784, 224, 608, 672, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_787, vertices_451, vertices_541, vertices_405, vertices_362, vertices_226, vertices_674, vertices_802, vertices_220, vertices_620, vertices_708, vertices_824, vertices_472, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_21, vertices_133, vertices_517, vertices_273, vertices_529, vertices_385, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_642, vertices_770, vertices_28, vertices_76, vertices_524, vertices_148, vertices_196, vertices_580, vertices_644, vertices_216, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_328, vertices_400, vertices_784, vertices_224, vertices_608, vertices_672, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_787), (false, vertices_451), (false, vertices_541), (false, vertices_405), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_76), (true, vertices_196), (true, vertices_580), (true, vertices_216), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_800), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 18 else
  if p.val = (false, vertices_787) then 19 else
  if p.val = (false, vertices_451) then 20 else
  if p.val = (false, vertices_541) then 22 else
  if p.val = (false, vertices_405) then 23 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_216) then 25 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_672) then 14 else
  if p.val = (true, vertices_800) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 24 => Sum.inl 2
  | 25 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 5 6 216
cert_row_4 1 0 2 4 5 7 362 98 1
cert_row_4 2 1 2 4 5 8 620 76 2
cert_row_4 3 2 3 4 7 8 824 280 2
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 362
cert_cover_5 0 1 0 2 4 5 98 362 1
cert_coverFacet 1 226
cert_cover_2 1 4 0 5 6 98 226 3
cert_coverFacet 2 674
cert_cover_2 2 4 0 6 8 162 674 3
cert_coverFacet 3 802
cert_cover_2 3 4 0 7 8 290 802 3
cert_coverFacet 4 220
cert_cover_5 4 0 1 2 3 5 28 220 3
cert_coverFacet 5 620
cert_cover_5 5 2 1 2 4 5 76 620 2
cert_coverFacet 6 708
cert_cover_2 6 5 1 6 8 196 708 3
cert_coverFacet 7 824
cert_cover_5 7 3 2 3 4 7 280 824 2
cert_coverFacet 8 472
cert_cover_5 8 0 2 3 5 7 216 472 3
cert_coverFacet 9 736
cert_cover_2 9 5 4 6 8 224 736 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0242

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0243.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0243

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 901, 617, 777, 721, 481, 782, 118, 662, 358, 58, 538, 468, 568, 624, 41, 265, 521, 97, 289, 193, 577, 385, 641, 769, 22, 102, 262, 518, 26, 42, 266, 522, 50, 530, 290, 84, 148, 324, 388, 644, 772, 56, 536, 552, 776, 112, 560, 208, 592, 656, 352, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_901, vertices_617, vertices_777, vertices_721, vertices_481, vertices_782, vertices_118, vertices_662, vertices_358, vertices_58, vertices_538, vertices_468, vertices_568, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_265, vertices_521, vertices_97, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_22, vertices_102, vertices_262, vertices_518, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_530, vertices_290, vertices_84, vertices_148, vertices_324, vertices_388, vertices_644, vertices_772, vertices_56, vertices_536, vertices_552, vertices_776, vertices_112, vertices_560, vertices_208, vertices_592, vertices_656, vertices_352, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_901), (false, vertices_617), (false, vertices_777), (false, vertices_721), (false, vertices_481), (true, vertices_22), (true, vertices_102), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_522), (true, vertices_50), (true, vertices_530), (true, vertices_84), (true, vertices_148), (true, vertices_324), (true, vertices_56), (true, vertices_536), (true, vertices_112), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_102) then 17 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_50) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_560) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 777 22 262 518 26 522 50 530 84 148 324 56 536 112 560 299 102 901 617 721 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 5 102
cert_row_4 1 0 1 2 7 8 782 262 2
cert_row_4 2 0 1 3 6 8 662 22 3
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 262 782 2
cert_coverFacet 1 118
cert_cover_5 1 0 0 1 3 4 22 118 3
cert_coverFacet 2 662
cert_cover_5 2 2 0 1 3 6 22 662 3
cert_coverFacet 3 358
cert_cover_5 3 0 0 1 4 7 102 358 3
cert_coverFacet 4 58
cert_cover_2 4 2 0 3 4 26 58 3
cert_coverFacet 5 538
cert_cover_2 5 2 0 3 8 26 538 3
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 84 468 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coverFacet 8 624
cert_cover_2 8 4 3 5 8 112 624 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0243

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0245.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0245

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 901, 345, 617, 777, 481, 118, 150, 422, 602, 658, 610, 796, 372, 660, 73, 265, 521, 97, 161, 545, 321, 385, 641, 769, 22, 38, 134, 82, 146, 530, 98, 162, 546, 578, 642, 116, 148, 276, 532, 292, 388, 644, 772, 88, 280, 536, 584, 776, 336, 656, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_901, vertices_345, vertices_617, vertices_777, vertices_481, vertices_118, vertices_150, vertices_422, vertices_602, vertices_658, vertices_610, vertices_796, vertices_372, vertices_660] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_321, vertices_385, vertices_641, vertices_769, vertices_22, vertices_38, vertices_134, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_578, vertices_642, vertices_116, vertices_148, vertices_276, vertices_532, vertices_292, vertices_388, vertices_644, vertices_772, vertices_88, vertices_280, vertices_536, vertices_584, vertices_776, vertices_336, vertices_656, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_901), (false, vertices_345), (false, vertices_617), (false, vertices_777), (false, vertices_481), (true, vertices_22), (true, vertices_38), (true, vertices_134), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_98), (true, vertices_578), (true, vertices_116), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_536), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_901) then 18 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_116) then 19 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_292) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_116), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 7 422 38 3
cert_row_2 1 1 3 4 5 116
cert_row_4 2 0 2 3 5 8 602 82 1
cert_row_4 3 1 2 3 7 8 796 276 1
cert_rows
cert_pivot_2 6 4 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 1 0 1 3 4 22 118 3
cert_coverFacet 1 150
cert_cover_2 1 1 0 3 6 22 150 3
cert_coverFacet 2 422
cert_cover_5 2 0 0 1 4 6 38 422 3
cert_coverFacet 3 602
cert_cover_5 3 2 0 2 3 5 82 602 1
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 610
cert_cover_2 5 4 0 5 8 98 610 3
cert_coverFacet 6 796
cert_cover_5 6 3 1 2 3 7 276 796 1
cert_coverFacet 7 372
cert_cover_5 7 1 1 3 4 7 116 372 3
cert_coverFacet 8 660
cert_cover_2 8 3 1 6 8 148 660 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0245

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0246.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0246

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 117, 661, 453, 905, 369, 566, 58, 282, 618, 778, 716, 612, 312, 488, 21, 69, 133, 113, 273, 529, 321, 385, 641, 769, 26, 42, 266, 522, 50, 274, 530, 546, 770, 52, 532, 100, 548, 196, 580, 644, 56, 280, 104, 296, 200, 584, 392, 648, 776, 304, 352, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_117, vertices_661, vertices_453, vertices_905, vertices_369, vertices_566, vertices_58, vertices_282, vertices_618, vertices_778, vertices_716, vertices_612, vertices_312, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_133, vertices_113, vertices_273, vertices_529, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_546, vertices_770, vertices_52, vertices_532, vertices_100, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_280, vertices_104, vertices_296, vertices_200, vertices_584, vertices_392, vertices_648, vertices_776, vertices_304, vertices_352, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_117), (false, vertices_661), (false, vertices_453), (false, vertices_905), (false, vertices_369), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_546), (true, vertices_548), (true, vertices_580), (true, vertices_56), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_584), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_117) then 23 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_905) then 21 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 50 1
cert_row_4 1 0 2 4 5 8 618 42 3
cert_row_4 2 1 2 5 6 8 716 196 1
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 50 566 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 618
cert_cover_5 3 1 0 2 4 5 42 618 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 716
cert_cover_5 5 2 1 2 5 6 196 716 1
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 104 488 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0246

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0247.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0247

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 789, 121, 665, 425, 369, 342, 614, 774, 682, 226, 450, 604, 616, 480, 25, 41, 137, 113, 273, 529, 289, 385, 641, 769, 70, 262, 518, 98, 162, 546, 194, 322, 386, 642, 770, 84, 276, 532, 580, 772, 88, 536, 104, 168, 552, 584, 648, 336, 224, 352, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_789, vertices_121, vertices_665, vertices_425, vertices_369, vertices_342, vertices_614, vertices_774, vertices_682, vertices_226, vertices_450, vertices_604, vertices_616, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_137, vertices_113, vertices_273, vertices_529, vertices_289, vertices_385, vertices_641, vertices_769, vertices_70, vertices_262, vertices_518, vertices_98, vertices_162, vertices_546, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_84, vertices_276, vertices_532, vertices_580, vertices_772, vertices_88, vertices_536, vertices_104, vertices_168, vertices_552, vertices_584, vertices_648, vertices_336, vertices_224, vertices_352, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_789), (false, vertices_121), (false, vertices_665), (false, vertices_425), (false, vertices_369), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_322), (true, vertices_84), (true, vertices_580), (true, vertices_552), (true, vertices_584), (true, vertices_224), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 19 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_121) then 23 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 70 2
cert_row_4 1 0 2 4 6 8 682 162 1
cert_row_4 2 0 1 4 5 8 614 70 2
cert_row_4 3 1 2 3 5 8 604 84 1
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 70 342 2
cert_coverFacet 1 614
cert_cover_5 1 2 0 1 4 5 70 614 2
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 682
cert_cover_5 3 1 0 2 4 6 162 682 1
cert_coverFacet 4 226
cert_cover_2 4 4 0 5 6 98 226 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 604
cert_cover_5 6 3 1 2 3 5 84 604 1
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coverFacet 8 480
cert_cover_2 8 5 4 6 7 224 480 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0247

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0248.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0248

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 709, 617, 777, 913, 481, 558, 118, 662, 282, 538, 370, 468, 612, 792, 41, 265, 521, 97, 289, 193, 577, 385, 641, 769, 22, 38, 518, 26, 42, 266, 522, 114, 274, 530, 290, 84, 148, 100, 548, 196, 580, 644, 280, 536, 552, 776, 336, 400, 656, 784, 352, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_709, vertices_617, vertices_777, vertices_913, vertices_481, vertices_558, vertices_118, vertices_662, vertices_282, vertices_538, vertices_370, vertices_468, vertices_612, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_265, vertices_521, vertices_97, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_22, vertices_38, vertices_518, vertices_26, vertices_42, vertices_266, vertices_522, vertices_114, vertices_274, vertices_530, vertices_290, vertices_84, vertices_148, vertices_100, vertices_548, vertices_196, vertices_580, vertices_644, vertices_280, vertices_536, vertices_552, vertices_776, vertices_336, vertices_400, vertices_656, vertices_784, vertices_352, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_709), (false, vertices_617), (false, vertices_777), (false, vertices_913), (false, vertices_481), (true, vertices_22), (true, vertices_38), (true, vertices_518), (true, vertices_26), (true, vertices_522), (true, vertices_114), (true, vertices_274), (true, vertices_530), (true, vertices_84), (true, vertices_148), (true, vertices_100), (true, vertices_548), (true, vertices_280), (true, vertices_536), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_913) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_114) then 17 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_336) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 777 22 38 518 26 522 274 530 84 148 100 548 280 536 336 299 114 709 617 913 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 38 2
cert_row_2 1 0 3 4 5 114
cert_row_4 2 0 1 3 6 8 662 22 3
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 38 558 2
cert_coverFacet 1 118
cert_cover_5 1 1 0 1 3 4 22 118 3
cert_coverFacet 2 662
cert_cover_5 2 2 0 1 3 6 22 662 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 370
cert_cover_5 5 1 0 3 4 7 114 370 3
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 84 468 3
cert_coverFacet 7 612
cert_cover_2 7 4 1 5 8 100 612 3
cert_coverFacet 8 792
cert_cover_2 8 3 2 7 8 280 792 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0248

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0249.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0249

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 661, 809, 713, 241, 305, 785, 590, 790, 454, 298, 778, 482, 436, 708, 41, 73, 521, 49, 145, 273, 529, 97, 289, 193, 641, 769, 70, 262, 518, 42, 74, 266, 522, 98, 290, 450, 770, 148, 276, 532, 196, 580, 388, 644, 296, 584, 776, 176, 304, 784, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_661, vertices_809, vertices_713, vertices_241, vertices_305, vertices_785, vertices_590, vertices_790, vertices_454, vertices_298, vertices_778, vertices_482, vertices_436, vertices_708] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_521, vertices_49, vertices_145, vertices_273, vertices_529, vertices_97, vertices_289, vertices_193, vertices_641, vertices_769, vertices_70, vertices_262, vertices_518, vertices_42, vertices_74, vertices_266, vertices_522, vertices_98, vertices_290, vertices_450, vertices_770, vertices_148, vertices_276, vertices_532, vertices_196, vertices_580, vertices_388, vertices_644, vertices_296, vertices_584, vertices_776, vertices_176, vertices_304, vertices_784, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_661), (false, vertices_809), (false, vertices_713), (false, vertices_241), (false, vertices_305), (false, vertices_785), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_450), (true, vertices_770), (true, vertices_276), (true, vertices_196), (true, vertices_580), (true, vertices_388), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 15 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (false, vertices_785) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_450) then 16 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_450), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
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
cert_row_4 0 0 1 2 5 8 590 70 2
cert_row_2 1 0 5 6 7 450
cert_row_4 2 0 1 3 7 8 790 262 2
cert_row_4 3 1 3 4 6 7 436 148 2
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 70 590 2
cert_coverFacet 1 790
cert_cover_5 1 2 0 1 3 7 262 790 2
cert_coverFacet 2 454
cert_cover_5 2 1 0 1 5 6 70 454 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 482
cert_cover_5 5 1 0 4 5 6 98 482 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 148 436 2
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0249

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0250.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0250

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 331, 787, 565, 213, 465, 714, 778, 684, 436, 708, 312, 568, 792, 488, 67, 259, 515, 21, 69, 517, 209, 273, 529, 321, 74, 266, 522, 578, 770, 52, 148, 164, 548, 196, 580, 644, 56, 280, 536, 168, 296, 552, 200, 328, 648, 776, 304, 560, 400, 784, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_331, vertices_787, vertices_565, vertices_213, vertices_465, vertices_714, vertices_778, vertices_684, vertices_436, vertices_708, vertices_312, vertices_568, vertices_792, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_21, vertices_69, vertices_517, vertices_209, vertices_273, vertices_529, vertices_321, vertices_74, vertices_266, vertices_522, vertices_578, vertices_770, vertices_52, vertices_148, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_648, vertices_776, vertices_304, vertices_560, vertices_400, vertices_784, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_331), (false, vertices_787), (false, vertices_565), (false, vertices_213), (false, vertices_465), (true, vertices_522), (true, vertices_164), (true, vertices_644), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_200), (true, vertices_648), (true, vertices_776), (true, vertices_304), (true, vertices_416), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 21 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 16 else
  if p.val = (false, vertices_331) then 17 else
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_565) then 20 else
  if p.val = (false, vertices_213) then 23 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_164) then 1 else
  if p.val = (true, vertices_644) then 2 else
  if p.val = (true, vertices_56) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 74 3
cert_row_4 1 1 2 4 6 8 684 164 1
cert_row_4 2 1 3 4 6 7 436 52 3
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 714
cert_cover_5 0 0 0 2 5 6 74 714 3
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 164 684 1
cert_coverFacet 3 436
cert_cover_5 3 2 1 3 4 6 52 436 3
cert_coverFacet 4 708
cert_cover_2 4 5 1 6 8 196 708 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 168 488 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0250

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0251.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0251

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 397, 677, 773, 625, 481, 782, 186, 602, 426, 306, 338, 668, 368, 688, 133, 261, 517, 97, 161, 545, 321, 577, 385, 769, 26, 170, 266, 522, 50, 82, 274, 290, 322, 578, 770, 140, 268, 524, 644, 772, 152, 536, 392, 112, 176, 304, 560, 336, 592, 656, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_397, vertices_677, vertices_773, vertices_625, vertices_481, vertices_782, vertices_186, vertices_602, vertices_426, vertices_306, vertices_338, vertices_668, vertices_368, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_769, vertices_26, vertices_170, vertices_266, vertices_522, vertices_50, vertices_82, vertices_274, vertices_290, vertices_322, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_644, vertices_772, vertices_152, vertices_536, vertices_392, vertices_112, vertices_176, vertices_304, vertices_560, vertices_336, vertices_592, vertices_656, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_397), (false, vertices_677), (false, vertices_773), (false, vertices_625), (false, vertices_481), (true, vertices_26), (true, vertices_170), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_290), (true, vertices_524), (true, vertices_152), (true, vertices_536), (true, vertices_176), (true, vertices_304), (true, vertices_336), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_170) then 17 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_170), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
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
cert_row_2 0 0 2 4 6 170
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 2 3 5 8 602 26 3
cert_row_4 3 1 2 3 6 8 668 140 2
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 186
cert_cover_5 1 0 0 2 3 4 26 186 3
cert_coverFacet 2 602
cert_cover_5 2 2 0 2 3 5 26 602 3
cert_coverFacet 3 426
cert_cover_5 3 0 0 2 4 7 170 426 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 668
cert_cover_5 6 3 1 2 3 6 140 668 2
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0251

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0252.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0252

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 173, 589, 789, 421, 457, 310, 714, 178, 658, 786, 482, 556, 564, 696, 13, 165, 261, 517, 73, 137, 321, 577, 385, 769, 50, 146, 274, 530, 162, 290, 194, 322, 578, 642, 770, 44, 524, 52, 276, 532, 292, 548, 168, 552, 200, 584, 648, 176, 560, 656, 784, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_173, vertices_589, vertices_789, vertices_421, vertices_457, vertices_310, vertices_714, vertices_178, vertices_658, vertices_786, vertices_482, vertices_556, vertices_564, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_165, vertices_261, vertices_517, vertices_73, vertices_137, vertices_321, vertices_577, vertices_385, vertices_769, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_532, vertices_292, vertices_548, vertices_168, vertices_552, vertices_200, vertices_584, vertices_648, vertices_176, vertices_560, vertices_656, vertices_784, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_173), (false, vertices_589), (false, vertices_789), (false, vertices_421), (false, vertices_457), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_194), (true, vertices_642), (true, vertices_52), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_176), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_173) then 21 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_789) then 22 else
  if p.val = (false, vertices_421) then 23 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
cert_nodeAtPriority_42 50 1 146 2 274 530 162 290 194 642 52 548 552 648 176 560 656 835 589 457 173 789 421
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 50 1
cert_row_4 1 0 4 5 6 7 482 162 2
cert_row_4 2 0 2 5 6 8 714 194 1
cert_row_4 3 2 3 4 6 8 696 168 1
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 50 310 1
cert_coverFacet 1 714
cert_cover_5 1 2 0 2 5 6 194 714 1
cert_coverFacet 2 178
cert_cover_2 2 3 0 4 6 50 178 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 482
cert_cover_5 5 1 0 4 5 6 162 482 2
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 564
cert_cover_2 7 3 1 4 8 52 564 3
cert_coverFacet 8 696
cert_cover_5 8 3 2 3 4 6 168 696 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0252

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0253.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0253

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 787, 419, 313, 689, 590, 198, 450, 834, 188, 668, 364, 228, 856, 480, 131, 259, 515, 49, 273, 529, 161, 289, 641, 70, 134, 518, 194, 322, 578, 386, 770, 156, 44, 76, 524, 100, 164, 196, 644, 56, 280, 536, 296, 328, 584, 176, 656, 784, 224, 352, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_787, vertices_419, vertices_313, vertices_689, vertices_590, vertices_198, vertices_450, vertices_834, vertices_188, vertices_668, vertices_364, vertices_228, vertices_856, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_49, vertices_273, vertices_529, vertices_161, vertices_289, vertices_641, vertices_70, vertices_134, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_156, vertices_44, vertices_76, vertices_524, vertices_100, vertices_164, vertices_196, vertices_644, vertices_56, vertices_280, vertices_536, vertices_296, vertices_328, vertices_584, vertices_176, vertices_656, vertices_784, vertices_224, vertices_352, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_787), (false, vertices_419), (false, vertices_313), (false, vertices_689), (true, vertices_70), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_156), (true, vertices_44), (true, vertices_76), (true, vertices_524), (true, vertices_100), (true, vertices_164), (true, vertices_196), (true, vertices_536), (true, vertices_328), (true, vertices_584), (true, vertices_224), (true, vertices_352), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 18 else
  if p.val = (false, vertices_787) then 19 else
  if p.val = (false, vertices_419) then 20 else
  if p.val = (false, vertices_313) then 24 else
  if p.val = (false, vertices_689) then 26 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_156) then 22 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_448) then 15 else
  if p.val = (true, vertices_832) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 6 156
cert_row_4 1 0 1 2 5 8 590 70 2
cert_row_4 2 1 2 4 5 7 364 44 3
cert_row_4 3 2 3 5 7 8 856 280 2
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 70 590 2
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 834
cert_cover_2 3 5 0 7 8 322 834 3
cert_coverFacet 4 188
cert_cover_5 4 0 1 2 3 4 156 188 3
cert_coverFacet 5 668
cert_cover_5 5 0 1 2 3 8 156 668 3
cert_coverFacet 6 364
cert_cover_5 6 2 1 2 4 5 44 364 3
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coverFacet 8 856
cert_cover_5 8 3 2 3 5 7 280 856 2
cert_coverFacet 9 480
cert_cover_2 9 5 4 6 7 224 480 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0253

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0254.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0254

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 535, 357, 709, 617, 817, 654, 454, 570, 154, 402, 312, 472, 360, 712, 23, 69, 261, 517, 273, 529, 97, 289, 545, 577, 134, 262, 518, 26, 138, 522, 146, 274, 530, 386, 196, 324, 644, 56, 152, 280, 104, 296, 552, 200, 328, 584, 648, 304, 560, 400, 352, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_535, vertices_357, vertices_709, vertices_617, vertices_817, vertices_654, vertices_454, vertices_570, vertices_154, vertices_402, vertices_312, vertices_472, vertices_360, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_69, vertices_261, vertices_517, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_577, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_196, vertices_324, vertices_644, vertices_56, vertices_152, vertices_280, vertices_104, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_648, vertices_304, vertices_560, vertices_400, vertices_352, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_535), (false, vertices_357), (false, vertices_709), (false, vertices_617), (false, vertices_817), (true, vertices_134), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_386), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_200), (true, vertices_328), (true, vertices_648), (true, vertices_400), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 16 else
  if p.val = (false, vertices_535) then 17 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_62 134 26 138 522 146 386 56 152 280 296 200 328 648 400 448 279 535 357 709 617 817
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 26 3
cert_row_4 1 0 1 2 6 8 654 134 2
cert_row_4 2 0 1 5 6 7 454 134 2
cert_row_4 3 2 3 5 6 7 472 152 2
cert_rows
cert_pivot_2 4 8 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 134 654 2
cert_coverFacet 1 454
cert_cover_5 1 2 0 1 5 6 134 454 2
cert_coverFacet 2 570
cert_cover_5 2 0 0 2 3 4 26 570 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 472
cert_cover_5 6 3 2 3 5 6 152 472 2
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coverFacet 8 712
cert_cover_2 8 5 2 6 8 200 712 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0254

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0255.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0255

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 781, 117, 341, 677, 481, 286, 538, 778, 466, 594, 738, 60, 556, 632, 85, 37, 261, 517, 97, 161, 321, 385, 641, 769, 26, 266, 522, 82, 274, 530, 194, 578, 386, 642, 770, 28, 44, 268, 524, 52, 276, 548, 56, 536, 552, 776, 112, 336, 592, 224, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_781, vertices_117, vertices_341, vertices_677, vertices_481, vertices_286, vertices_538, vertices_778, vertices_466, vertices_594, vertices_738, vertices_60, vertices_556, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_85, vertices_37, vertices_261, vertices_517, vertices_97, vertices_161, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_524, vertices_52, vertices_276, vertices_548, vertices_56, vertices_536, vertices_552, vertices_776, vertices_112, vertices_336, vertices_592, vertices_224, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_781), (false, vertices_117), (false, vertices_341), (false, vertices_677), (false, vertices_481), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_578), (true, vertices_28), (true, vertices_44), (true, vertices_56), (true, vertices_536), (true, vertices_552), (true, vertices_592), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 17 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_117) then 20 else
  if p.val = (false, vertices_341) then 21 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 7 286 26 1
cert_row_4 1 0 3 5 6 7 466 82 3
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 26 286 1
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 466
cert_cover_5 3 1 0 3 5 6 82 466 3
cert_coverFacet 4 594
cert_cover_2 4 3 0 5 8 82 594 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 194 738 1
cert_coverFacet 6 60
cert_cover_2 6 2 1 3 4 28 60 3
cert_coverFacet 7 556
cert_cover_2 7 2 1 4 8 44 556 3
cert_coverFacet 8 632
cert_cover_5 8 3 2 3 4 5 56 632 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0255

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0256.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0256

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 805, 453, 681, 433, 705, 286, 782, 86, 186, 714, 210, 340, 824, 464, 69, 261, 517, 161, 289, 545, 193, 577, 385, 641, 270, 22, 70, 518, 26, 138, 522, 82, 146, 194, 578, 84, 276, 324, 772, 56, 280, 168, 552, 648, 776, 176, 304, 208, 336, 400, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_805, vertices_453, vertices_681, vertices_433, vertices_705, vertices_286, vertices_782, vertices_86, vertices_186, vertices_714, vertices_210, vertices_340, vertices_824, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_270, vertices_22, vertices_70, vertices_518, vertices_26, vertices_138, vertices_522, vertices_82, vertices_146, vertices_194, vertices_578, vertices_84, vertices_276, vertices_324, vertices_772, vertices_56, vertices_280, vertices_168, vertices_552, vertices_648, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_400, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_805), (false, vertices_453), (false, vertices_681), (false, vertices_433), (false, vertices_705), (true, vertices_270), (true, vertices_22), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_84), (true, vertices_276), (true, vertices_56), (true, vertices_280), (true, vertices_776), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 16 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_270) then 17 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 705 22 26 138 522 82 146 194 84 276 56 280 776 208 336 583 270 805 453 681 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 7 270
cert_row_4 1 0 2 5 6 8 714 138 2
cert_row_4 2 0 2 3 4 6 186 26 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 270 286 3
cert_coverFacet 1 782
cert_cover_5 1 0 0 1 2 8 270 782 3
cert_coverFacet 2 86
cert_cover_2 2 1 0 3 5 22 86 3
cert_coverFacet 3 186
cert_cover_5 3 2 0 2 3 4 26 186 3
cert_coverFacet 4 714
cert_cover_5 4 1 0 2 5 6 138 714 2
cert_coverFacet 5 210
cert_cover_2 5 3 0 5 6 82 210 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 824
cert_cover_5 7 3 2 3 4 7 56 824 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0256

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0257.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0257

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 675, 835, 805, 433, 449, 542, 590, 154, 658, 316, 332, 692, 836, 472, 67, 131, 515, 161, 289, 545, 193, 321, 385, 769, 526, 26, 74, 138, 146, 530, 578, 642, 28, 76, 268, 52, 532, 292, 548, 324, 580, 772, 152, 280, 200, 328, 176, 304, 400, 656, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_675, vertices_835, vertices_805, vertices_433, vertices_449, vertices_542, vertices_590, vertices_154, vertices_658, vertices_316, vertices_332, vertices_692, vertices_836, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_515, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_526, vertices_26, vertices_74, vertices_138, vertices_146, vertices_530, vertices_578, vertices_642, vertices_28, vertices_76, vertices_268, vertices_52, vertices_532, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_200, vertices_328, vertices_176, vertices_304, vertices_400, vertices_656, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_675), (false, vertices_835), (false, vertices_805), (false, vertices_433), (false, vertices_449), (true, vertices_526), (true, vertices_26), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_52), (true, vertices_532), (true, vertices_324), (true, vertices_580), (true, vertices_152), (true, vertices_280), (true, vertices_328), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 15 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 19 else
  if p.val = (false, vertices_675) then 20 else
  if p.val = (false, vertices_835) then 21 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_526) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
cert_nodeAtPriority_19 1 449 0 26 146 530 28 76 268 52 532 324 580 152 280 328 656 805 526 203 675 835 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 8 526
cert_row_4 1 1 3 4 6 8 692 52 3
cert_row_4 2 1 2 3 4 7 316 28 3
cert_row_4 3 2 3 5 6 7 472 152 2
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 526 542 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 5 526 590 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 316
cert_cover_5 4 2 1 2 3 4 28 316 3
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 692
cert_cover_5 6 1 1 3 4 6 52 692 3
cert_coverFacet 7 836
cert_cover_2 7 5 1 7 8 324 836 3
cert_coverFacet 8 472
cert_cover_5 8 3 2 3 5 6 152 472 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0257

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0258.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0258

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 301, 781, 229, 185, 713, 790, 326, 666, 370, 210, 706, 356, 824, 240, 269, 37, 69, 517, 41, 137, 521, 161, 193, 577, 70, 262, 518, 82, 146, 274, 530, 194, 322, 578, 642, 100, 292, 324, 772, 56, 152, 536, 296, 648, 776, 112, 176, 304, 208, 784, 224, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_301, vertices_781, vertices_229, vertices_185, vertices_713, vertices_790, vertices_326, vertices_666, vertices_370, vertices_210, vertices_706, vertices_356, vertices_824, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_269, vertices_37, vertices_69, vertices_517, vertices_41, vertices_137, vertices_521, vertices_161, vertices_193, vertices_577, vertices_70, vertices_262, vertices_518, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_100, vertices_292, vertices_324, vertices_772, vertices_56, vertices_152, vertices_536, vertices_296, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_784, vertices_224, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_301), (false, vertices_781), (false, vertices_229), (false, vertices_185), (false, vertices_713), (true, vertices_262), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_642), (true, vertices_324), (true, vertices_536), (true, vertices_112), (true, vertices_304), (true, vertices_208), (true, vertices_784), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 16 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_229) then 20 else
  if p.val = (false, vertices_185) then 22 else
  if p.val = (false, vertices_713) then 23 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 262 1 82 2 146 274 530 194 322 642 324 536 112 304 208 784 352 583 301 781 229 185 713
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 262 2
cert_row_4 1 0 2 3 6 8 666 146 1
cert_row_4 2 0 3 4 5 7 370 82 2
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 262 790 2
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 666
cert_cover_5 2 1 0 2 3 6 146 666 1
cert_coverFacet 3 370
cert_cover_5 3 2 0 3 4 5 82 370 2
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 356
cert_cover_2 6 4 1 5 7 100 356 3
cert_coverFacet 7 824
cert_cover_5 7 3 2 3 4 7 56 824 3
cert_coverFacet 8 240
cert_cover_2 8 4 3 5 6 112 240 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0258

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0259.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0259

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 653, 809, 457, 369, 225, 782, 310, 534, 242, 658, 802, 220, 348, 660, 137, 265, 521, 97, 161, 289, 545, 193, 321, 641, 22, 262, 518, 50, 146, 530, 162, 290, 546, 642, 770, 92, 140, 268, 524, 148, 276, 532, 644, 200, 328, 776, 112, 304, 208, 336, 656, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_653, vertices_809, vertices_457, vertices_369, vertices_225, vertices_782, vertices_310, vertices_534, vertices_242, vertices_658, vertices_802, vertices_220, vertices_348, vertices_660] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_22, vertices_262, vertices_518, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_92, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_644, vertices_200, vertices_328, vertices_776, vertices_112, vertices_304, vertices_208, vertices_336, vertices_656, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_653), (false, vertices_809), (false, vertices_457), (false, vertices_369), (false, vertices_225), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_290), (true, vertices_770), (true, vertices_92), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_208), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (false, vertices_225) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_92) then 19 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 225 2 22 1 262 3 518 50 146 530 290 770 268 148 276 532 208 656 675 653 92 809 457 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 262 2
cert_row_2 1 1 2 3 5 92
cert_row_4 2 0 1 3 4 7 310 22 3
cert_row_4 3 0 3 4 5 6 242 50 3
cert_rows
cert_pivot_2 8 2 1 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 262 782 2
cert_coverFacet 1 310
cert_cover_5 1 2 0 1 3 4 22 310 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 242
cert_cover_5 3 3 0 3 4 5 50 242 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 220
cert_cover_5 6 1 1 2 3 6 92 220 3
cert_coverFacet 7 348
cert_cover_5 7 1 1 2 3 7 92 348 3
cert_coverFacet 8 660
cert_cover_2 8 3 1 6 8 148 660 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0259

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0260.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0260

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 583, 541, 397, 345, 625, 654, 422, 690, 866, 184, 312, 664, 424, 368, 71, 13, 261, 517, 25, 265, 81, 529, 321, 577, 134, 262, 518, 162, 290, 546, 322, 578, 642, 140, 524, 388, 56, 152, 280, 536, 168, 296, 392, 648, 112, 176, 304, 560, 336, 656, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_583, vertices_541, vertices_397, vertices_345, vertices_625, vertices_654, vertices_422, vertices_690, vertices_866, vertices_184, vertices_312, vertices_664, vertices_424, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_71, vertices_13, vertices_261, vertices_517, vertices_25, vertices_265, vertices_81, vertices_529, vertices_321, vertices_577, vertices_134, vertices_262, vertices_518, vertices_162, vertices_290, vertices_546, vertices_322, vertices_578, vertices_642, vertices_140, vertices_524, vertices_388, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_392, vertices_648, vertices_112, vertices_176, vertices_304, vertices_560, vertices_336, vertices_656, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_583), (false, vertices_541), (false, vertices_397), (false, vertices_345), (false, vertices_625), (true, vertices_134), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_56), (true, vertices_152), (true, vertices_168), (true, vertices_296), (true, vertices_648), (true, vertices_176), (true, vertices_304), (true, vertices_656), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 16 else
  if p.val = (false, vertices_583) then 17 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_397) then 20 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_62 134 162 290 546 642 56 152 168 296 648 176 304 656 352 416 327 583 541 397 345 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 134 2
cert_row_4 1 0 1 4 6 7 422 134 2
cert_row_4 2 0 3 4 6 8 690 162 1
cert_row_4 3 0 4 5 7 8 866 290 2
cert_rows
cert_pivot_2 2 1 3 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 134 654 2
cert_coverFacet 1 422
cert_cover_5 1 1 0 1 4 6 134 422 2
cert_coverFacet 2 690
cert_cover_5 2 2 0 3 4 6 162 690 1
cert_coverFacet 3 866
cert_cover_5 3 3 0 4 5 7 290 866 2
cert_coverFacet 4 184
cert_cover_2 4 3 2 4 6 56 184 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 664
cert_cover_2 6 3 2 6 8 152 664 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0260

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0261.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0261

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 397, 789, 709, 433, 209, 206, 590, 570, 426, 114, 226, 812, 240, 816, 133, 261, 517, 81, 145, 273, 529, 193, 577, 385, 78, 42, 138, 522, 50, 82, 530, 98, 162, 194, 578, 140, 268, 524, 196, 580, 772, 296, 552, 392, 112, 176, 304, 560, 208, 784, 224, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_397, vertices_789, vertices_709, vertices_433, vertices_209, vertices_206, vertices_590, vertices_570, vertices_426, vertices_114, vertices_226, vertices_812, vertices_240, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_78, vertices_42, vertices_138, vertices_522, vertices_50, vertices_82, vertices_530, vertices_98, vertices_162, vertices_194, vertices_578, vertices_140, vertices_268, vertices_524, vertices_196, vertices_580, vertices_772, vertices_296, vertices_552, vertices_392, vertices_112, vertices_176, vertices_304, vertices_560, vertices_208, vertices_784, vertices_224, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_397), (false, vertices_789), (false, vertices_709), (false, vertices_433), (false, vertices_209), (true, vertices_78), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_50), (true, vertices_98), (true, vertices_162), (true, vertices_194), (true, vertices_524), (true, vertices_296), (true, vertices_552), (true, vertices_112), (true, vertices_560), (true, vertices_224), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 16 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_209) then 0 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
cert_nodeAtPriority_19 0 209 1 42 138 522 50 98 162 194 524 296 552 112 560 224 800 595 78 397 789 709 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 2 3 4 8 570 42 2
cert_row_4 2 0 2 4 6 7 426 42 3
cert_row_4 3 1 2 4 7 8 812 268 2
cert_rows
cert_pivot_2 5 3 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 6 78 206 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 570
cert_cover_5 2 1 0 2 3 4 42 570 2
cert_coverFacet 3 426
cert_cover_5 3 2 0 2 4 6 42 426 3
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 226
cert_cover_2 5 4 0 5 6 98 226 3
cert_coverFacet 6 812
cert_cover_5 6 3 1 2 4 7 268 812 2
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coverFacet 8 816
cert_cover_2 8 4 3 7 8 304 816 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0261

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0262.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0262

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 597, 405, 357, 457, 705, 310, 566, 154, 282, 810, 714, 620, 408, 360, 21, 69, 261, 145, 529, 193, 321, 577, 385, 641, 54, 26, 138, 266, 522, 146, 274, 530, 290, 546, 642, 276, 532, 100, 292, 548, 580, 152, 280, 104, 296, 552, 200, 328, 584, 392, 400, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_597, vertices_405, vertices_357, vertices_457, vertices_705, vertices_310, vertices_566, vertices_154, vertices_282, vertices_810, vertices_714, vertices_620, vertices_408, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_261, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_54, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_642, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_580, vertices_152, vertices_280, vertices_104, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_400, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_597), (false, vertices_405), (false, vertices_357), (false, vertices_457), (false, vertices_705), (true, vertices_54), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_290), (true, vertices_546), (true, vertices_548), (true, vertices_152), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_54) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_584) then 14 else
  0
cert_priority
cert_nodeAtPriority_51 705 26 138 266 522 274 290 546 548 152 280 104 296 552 584 659 54 597 405 357 457
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 0 2 4 7 8 810 266 2
cert_row_4 2 0 2 5 6 8 714 138 2
cert_row_4 3 1 2 4 5 8 620 100 1
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 7 54 310 3
cert_coverFacet 1 566
cert_cover_5 1 0 0 1 3 8 54 566 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 810
cert_cover_5 4 1 0 2 4 7 266 810 2
cert_coverFacet 5 714
cert_cover_5 5 2 0 2 5 6 138 714 2
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 100 620 1
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0262

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0263.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0263

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 229, 793, 681, 457, 609, 86, 790, 614, 410, 210, 450, 188, 572, 212, 137, 265, 521, 97, 161, 545, 193, 321, 577, 769, 22, 70, 518, 82, 146, 274, 194, 322, 578, 386, 770, 60, 84, 148, 532, 100, 164, 548, 196, 152, 280, 536, 168, 552, 392, 208, 784, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_229, vertices_793, vertices_681, vertices_457, vertices_609, vertices_86, vertices_790, vertices_614, vertices_410, vertices_210, vertices_450, vertices_188, vertices_572, vertices_212] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_769, vertices_22, vertices_70, vertices_518, vertices_82, vertices_146, vertices_274, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_60, vertices_84, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_152, vertices_280, vertices_536, vertices_168, vertices_552, vertices_392, vertices_208, vertices_784, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_229), (false, vertices_793), (false, vertices_681), (false, vertices_457), (false, vertices_609), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_194), (true, vertices_386), (true, vertices_60), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_548), (true, vertices_152), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (false, vertices_609) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_60) then 19 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_548) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_208) then 14 else
  0
cert_priority
cert_nodeAtPriority_43 609 2 22 1 70 518 82 146 274 194 386 84 148 532 548 152 208 835 229 60 793 681 457
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 8 614 70 2
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 1 3 7 8 790 22 3
cert_row_4 3 0 2 3 6 7 410 146 1
cert_rows
cert_pivot_2 5 4 1 0
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 790
cert_cover_5 1 2 0 1 3 7 22 790 3
cert_coverFacet 2 614
cert_cover_5 2 0 0 1 4 5 70 614 2
cert_coverFacet 3 410
cert_cover_5 3 3 0 2 3 6 146 410 1
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 188
cert_cover_5 6 1 1 2 3 6 60 188 3
cert_coverFacet 7 572
cert_cover_5 7 1 1 2 3 8 60 572 3
cert_coverFacet 8 212
cert_cover_2 8 3 1 5 6 84 212 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0263

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0264.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0264

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 205, 837, 601, 809, 393, 214, 598, 806, 426, 690, 120, 568, 232, 240, 69, 133, 261, 73, 137, 265, 521, 577, 385, 769, 86, 134, 262, 518, 146, 530, 162, 290, 546, 386, 196, 580, 772, 56, 88, 536, 104, 168, 296, 552, 200, 392, 112, 176, 560, 208, 592, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_205, vertices_837, vertices_601, vertices_809, vertices_393, vertices_214, vertices_598, vertices_806, vertices_426, vertices_690, vertices_120, vertices_568, vertices_232, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_73, vertices_137, vertices_265, vertices_521, vertices_577, vertices_385, vertices_769, vertices_86, vertices_134, vertices_262, vertices_518, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_196, vertices_580, vertices_772, vertices_56, vertices_88, vertices_536, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_392, vertices_112, vertices_176, vertices_560, vertices_208, vertices_592, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_205), (false, vertices_837), (false, vertices_601), (false, vertices_809), (false, vertices_393), (true, vertices_86), (true, vertices_518), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_56), (true, vertices_104), (true, vertices_168), (true, vertices_112), (true, vertices_176), (true, vertices_560), (true, vertices_208), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 16 else
  if p.val = (false, vertices_205) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_601) then 22 else
  if p.val = (false, vertices_809) then 23 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (true, vertices_86) then 17 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
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
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 1 4 7 8 806 262 2
cert_row_4 2 0 2 4 6 7 426 162 1
cert_row_4 3 0 3 4 6 8 690 146 2
cert_rows
cert_pivot_2 5 1 2 0
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 6 86 214 3
cert_coverFacet 1 598
cert_cover_5 1 0 0 1 3 8 86 598 3
cert_coverFacet 2 806
cert_cover_5 2 1 0 1 4 7 262 806 2
cert_coverFacet 3 426
cert_cover_5 3 2 0 2 4 6 162 426 1
cert_coverFacet 4 690
cert_cover_5 4 3 0 3 4 6 146 690 2
cert_coverFacet 5 120
cert_cover_2 5 3 2 4 5 56 120 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coverFacet 8 240
cert_cover_2 8 4 3 5 6 112 240 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0264

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0265.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0265

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 357, 681, 433, 849, 609, 302, 654, 342, 598, 154, 282, 620, 408, 424, 145, 273, 529, 97, 161, 289, 545, 321, 577, 641, 14, 86, 262, 518, 26, 138, 266, 146, 274, 530, 642, 44, 524, 100, 292, 324, 580, 152, 280, 168, 296, 552, 392, 648, 336, 592, 400, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_357, vertices_681, vertices_433, vertices_849, vertices_609, vertices_302, vertices_654, vertices_342, vertices_598, vertices_154, vertices_282, vertices_620, vertices_408, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_641, vertices_14, vertices_86, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_642, vertices_44, vertices_524, vertices_100, vertices_292, vertices_324, vertices_580, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_336, vertices_592, vertices_400, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_357), (false, vertices_681), (false, vertices_433), (false, vertices_849), (false, vertices_609), (true, vertices_14), (true, vertices_86), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_274), (true, vertices_44), (true, vertices_524), (true, vertices_580), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (false, vertices_609) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_86) then 17 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_274) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
cert_nodeAtPriority_40 609 14 262 518 26 138 266 274 44 524 580 152 280 296 392 659 86 357 681 433 849
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 1 2 4 7 302 14 3
cert_row_4 2 0 1 2 6 8 654 14 3
cert_row_4 3 1 2 4 5 8 620 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 1 0 1 2 4 14 302 3
cert_coverFacet 1 654
cert_cover_5 1 2 0 1 2 6 14 654 3
cert_coverFacet 2 342
cert_cover_5 2 0 0 1 3 7 86 342 3
cert_coverFacet 3 598
cert_cover_5 3 0 0 1 3 8 86 598 3
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 282
cert_cover_2 5 2 0 3 7 26 282 3
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 44 620 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0265

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0266.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0266

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 589, 181, 341, 677, 865, 654, 842, 394, 690, 402, 802, 204, 212, 472, 21, 165, 69, 517, 49, 273, 289, 545, 321, 577, 138, 266, 522, 50, 146, 274, 290, 546, 386, 642, 770, 76, 140, 524, 84, 148, 196, 644, 200, 328, 584, 392, 176, 208, 336, 400, 672, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_589, vertices_181, vertices_341, vertices_677, vertices_865, vertices_654, vertices_842, vertices_394, vertices_690, vertices_402, vertices_802, vertices_204, vertices_212, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_165, vertices_69, vertices_517, vertices_49, vertices_273, vertices_289, vertices_545, vertices_321, vertices_577, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_84, vertices_148, vertices_196, vertices_644, vertices_200, vertices_328, vertices_584, vertices_392, vertices_176, vertices_208, vertices_336, vertices_400, vertices_672, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_589), (false, vertices_181), (false, vertices_341), (false, vertices_677), (false, vertices_865), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_140), (true, vertices_196), (true, vertices_200), (true, vertices_328), (true, vertices_392), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 17 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 16 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_181) then 20 else
  if p.val = (false, vertices_341) then 21 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
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
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_4 1 0 3 4 6 8 690 50 3
cert_row_4 2 0 2 5 7 8 842 266 2
cert_row_4 3 2 3 5 6 7 472 200 1
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 842
cert_cover_5 1 2 0 2 5 7 266 842 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 690
cert_cover_5 3 1 0 3 4 6 50 690 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 204
cert_cover_2 6 2 1 5 6 76 204 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coverFacet 8 472
cert_cover_5 8 3 2 3 5 6 200 472 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0266

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0267.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0267

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 333, 653, 405, 617, 449, 662, 362, 818, 210, 338, 610, 316, 572, 464, 13, 133, 261, 73, 521, 193, 321, 577, 385, 641, 82, 146, 274, 530, 98, 290, 546, 194, 322, 578, 642, 60, 268, 524, 148, 276, 532, 644, 104, 296, 552, 328, 304, 560, 208, 336, 400, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_333, vertices_653, vertices_405, vertices_617, vertices_449, vertices_662, vertices_362, vertices_818, vertices_210, vertices_338, vertices_610, vertices_316, vertices_572, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_73, vertices_521, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_82, vertices_146, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_642, vertices_60, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_644, vertices_104, vertices_296, vertices_552, vertices_328, vertices_304, vertices_560, vertices_208, vertices_336, vertices_400, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_333), (false, vertices_653), (false, vertices_405), (false, vertices_617), (false, vertices_449), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_60), (true, vertices_532), (true, vertices_296), (true, vertices_304), (true, vertices_560), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 23 17 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_333) then 21 else
  if p.val = (false, vertices_653) then 22 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_617) then 24 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_60) then 19 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 449 1 82 3 146 2 274 530 98 290 546 322 532 296 304 560 208 336 707 405 60 333 653 617
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 2 4 5 7 362 98 1
cert_row_4 3 0 3 4 7 8 818 274 2
cert_rows
cert_pivot_2 6 1 2 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 362
cert_cover_5 1 2 0 2 4 5 98 362 1
cert_coverFacet 2 818
cert_cover_5 2 3 0 3 4 7 274 818 2
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 610
cert_cover_2 5 4 0 5 8 98 610 3
cert_coverFacet 6 316
cert_cover_5 6 1 1 2 3 7 60 316 3
cert_coverFacet 7 572
cert_cover_5 7 1 1 2 3 8 60 572 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0267

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0268.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0268

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 653, 601, 409, 369, 705, 398, 710, 774, 626, 354, 802, 316, 572, 804, 25, 137, 521, 81, 273, 193, 321, 577, 385, 641, 134, 262, 518, 98, 290, 546, 194, 322, 578, 386, 770, 60, 140, 268, 524, 292, 548, 644, 772, 280, 536, 392, 112, 304, 560, 592, 352, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_653, vertices_601, vertices_409, vertices_369, vertices_705, vertices_398, vertices_710, vertices_774, vertices_626, vertices_354, vertices_802, vertices_316, vertices_572, vertices_804] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_521, vertices_81, vertices_273, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_134, vertices_262, vertices_518, vertices_98, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_60, vertices_140, vertices_268, vertices_524, vertices_292, vertices_548, vertices_644, vertices_772, vertices_280, vertices_536, vertices_392, vertices_112, vertices_304, vertices_560, vertices_592, vertices_352, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_653), (false, vertices_601), (false, vertices_409), (false, vertices_369), (false, vertices_705), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_578), (true, vertices_770), (true, vertices_60), (true, vertices_268), (true, vertices_292), (true, vertices_548), (true, vertices_772), (true, vertices_560), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_60) then 19 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 705 2 134 1 262 3 518 98 290 546 578 770 268 292 548 772 560 800 451 653 60 601 409 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 1 5 6 8 710 134 2
cert_row_4 3 0 3 4 5 8 626 98 1
cert_rows
cert_pivot_2 7 2 1 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 710
cert_cover_5 1 2 0 1 5 6 134 710 2
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 626
cert_cover_5 3 3 0 3 4 5 98 626 1
cert_coverFacet 4 354
cert_cover_2 4 4 0 5 7 98 354 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 316
cert_cover_5 6 1 1 2 3 7 60 316 3
cert_coverFacet 7 572
cert_cover_5 7 1 1 2 3 8 60 572 3
cert_coverFacet 8 804
cert_cover_2 8 4 1 7 8 292 804 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0268

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0269.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0269

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 541, 141, 709, 409, 593, 481, 302, 558, 602, 282, 738, 354, 396, 932, 13, 133, 517, 25, 137, 81, 273, 529, 193, 321, 577, 385, 46, 26, 266, 522, 82, 274, 98, 290, 546, 322, 578, 140, 268, 524, 292, 548, 388, 644, 280, 536, 392, 592, 224, 352, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_541, vertices_141, vertices_709, vertices_409, vertices_593, vertices_481, vertices_302, vertices_558, vertices_602, vertices_282, vertices_738, vertices_354, vertices_396, vertices_932] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_25, vertices_137, vertices_81, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_46, vertices_26, vertices_266, vertices_522, vertices_82, vertices_274, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_140, vertices_268, vertices_524, vertices_292, vertices_548, vertices_388, vertices_644, vertices_280, vertices_536, vertices_392, vertices_592, vertices_224, vertices_352, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_541), (false, vertices_141), (false, vertices_709), (false, vertices_409), (false, vertices_593), (false, vertices_481), (true, vertices_46), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_578), (true, vertices_268), (true, vertices_292), (true, vertices_548), (true, vertices_388), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 15 else
  if p.val = (false, vertices_541) then 18 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_593) then 1 else
  if p.val = (false, vertices_481) then 24 else
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
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_53 0 141 1 593 26 266 522 98 290 546 578 268 292 548 388 672 339 46 541 709 409 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_2 1 0 1 2 4 46
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 1 4 6 7 8 932 292 2
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
cert_coverFacet 7 932
cert_cover_5 7 3 1 4 6 7 292 932 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0269

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0270.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0270

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 779, 707, 117, 805, 737, 410, 682, 450, 60, 284, 556, 780, 468, 248, 67, 259, 515, 37, 69, 261, 97, 545, 705, 769, 138, 266, 522, 194, 322, 386, 642, 28, 44, 268, 524, 52, 84, 276, 548, 324, 772, 56, 152, 280, 168, 552, 776, 112, 208, 400, 224, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_779, vertices_707, vertices_117, vertices_805, vertices_737, vertices_410, vertices_682, vertices_450, vertices_60, vertices_284, vertices_556, vertices_780, vertices_468, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_37, vertices_69, vertices_261, vertices_97, vertices_545, vertices_705, vertices_769, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_386, vertices_642, vertices_28, vertices_44, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_548, vertices_324, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_552, vertices_776, vertices_112, vertices_208, vertices_400, vertices_224, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_779), (false, vertices_707), (false, vertices_117), (false, vertices_805), (false, vertices_737), (true, vertices_138), (true, vertices_386), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_552), (true, vertices_208), (true, vertices_400), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 22 23 24 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 16 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_707) then 25 else
  if p.val = (false, vertices_117) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 138 2
cert_row_4 1 0 2 3 6 7 410 138 2
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 8 0 1 2
cert_heightProof 4
cert_coverFacet 0 410
cert_cover_5 0 1 0 2 3 6 138 410 2
cert_coverFacet 1 682
cert_cover_5 1 0 0 2 4 6 138 682 2
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 468
cert_cover_5 7 2 1 3 5 6 84 468 3
cert_coverFacet 8 248
cert_cover_5 8 3 2 3 4 5 56 248 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0270

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0271.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0271

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [275, 531, 803, 557, 665, 425, 465, 590, 342, 774, 722, 236, 484, 804, 712, 19, 259, 515, 41, 137, 521, 145, 273, 529, 289, 545, 385, 70, 262, 518, 82, 274, 530, 578, 770, 44, 76, 524, 228, 292, 548, 324, 772, 168, 200, 584, 648, 208, 336, 656, 416, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_275, vertices_531, vertices_803, vertices_557, vertices_665, vertices_425, vertices_465, vertices_590, vertices_342, vertices_774, vertices_722, vertices_236, vertices_484, vertices_804, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_259, vertices_515, vertices_41, vertices_137, vertices_521, vertices_145, vertices_273, vertices_529, vertices_289, vertices_545, vertices_385, vertices_70, vertices_262, vertices_518, vertices_82, vertices_274, vertices_530, vertices_578, vertices_770, vertices_44, vertices_76, vertices_524, vertices_228, vertices_292, vertices_548, vertices_324, vertices_772, vertices_168, vertices_200, vertices_584, vertices_648, vertices_208, vertices_336, vertices_656, vertices_416, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_275), (false, vertices_531), (false, vertices_803), (false, vertices_557), (false, vertices_665), (false, vertices_425), (false, vertices_465), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_82), (true, vertices_578), (true, vertices_76), (true, vertices_228), (true, vertices_292), (true, vertices_324), (true, vertices_772), (true, vertices_200), (true, vertices_584), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_531) then 1 else
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_557) then 17 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_228) then 18 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_228), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
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
cert_row_2 0 1 4 5 6 228
cert_row_4 1 0 1 2 5 8 590 70 2
cert_row_4 2 0 1 3 5 7 342 70 2
cert_row_4 3 0 3 5 6 8 722 82 3
cert_rows
cert_pivot_2 4 2 1 0
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 70 590 2
cert_coverFacet 1 342
cert_cover_5 1 2 0 1 3 5 70 342 2
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 722
cert_cover_5 3 3 0 3 5 6 82 722 3
cert_coverFacet 4 236
cert_cover_5 4 0 1 2 4 5 44 236 3
cert_coverFacet 5 484
cert_cover_5 5 0 1 4 5 7 228 484 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 712
cert_cover_2 7 5 2 6 8 200 712 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0271

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0272.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0272

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 109, 589, 309, 901, 625, 654, 602, 234, 210, 402, 898, 172, 420, 496, 77, 37, 261, 517, 49, 273, 529, 97, 577, 769, 74, 138, 522, 82, 146, 274, 530, 194, 386, 642, 770, 44, 140, 524, 164, 292, 388, 644, 104, 168, 584, 112, 304, 208, 592, 400, 224, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_109, vertices_589, vertices_309, vertices_901, vertices_625, vertices_654, vertices_602, vertices_234, vertices_210, vertices_402, vertices_898, vertices_172, vertices_420, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_77, vertices_37, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_97, vertices_577, vertices_769, vertices_74, vertices_138, vertices_522, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_524, vertices_164, vertices_292, vertices_388, vertices_644, vertices_104, vertices_168, vertices_584, vertices_112, vertices_304, vertices_208, vertices_592, vertices_400, vertices_224, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_109), (false, vertices_589), (false, vertices_309), (false, vertices_901), (false, vertices_625), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_140), (true, vertices_164), (true, vertices_168), (true, vertices_208), (true, vertices_400), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_309) then 21 else
  if p.val = (false, vertices_901) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 74 2 138 1 522 82 146 194 386 642 140 164 168 208 400 224 416 787 109 589 309 901 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_4 1 0 2 3 5 8 602 74 2
cert_row_4 2 0 2 4 5 6 234 74 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 8 0 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 602
cert_cover_5 1 1 0 2 3 5 74 602 2
cert_coverFacet 2 234
cert_cover_5 2 2 0 2 4 5 74 234 2
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 172
cert_cover_2 6 2 1 4 6 44 172 3
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0272

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2853 : Certifies 2853 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0242.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2854 : Certifies 2854 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0243.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2855 : Certifies 2855 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0245.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2856 : Certifies 2856 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0246.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2857 : Certifies 2857 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0247.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2858 : Certifies 2858 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0248.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2859 : Certifies 2859 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0249.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2860 : Certifies 2860 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0250.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2861 : Certifies 2861 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0251.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2862 : Certifies 2862 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0252.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2863 : Certifies 2863 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0253.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2864 : Certifies 2864 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0254.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2865 : Certifies 2865 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0255.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2866 : Certifies 2866 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0256.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2867 : Certifies 2867 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0257.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2868 : Certifies 2868 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0258.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2869 : Certifies 2869 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0259.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2870 : Certifies 2870 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0260.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2871 : Certifies 2871 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0261.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2872 : Certifies 2872 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0262.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2873 : Certifies 2873 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0263.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2874 : Certifies 2874 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0264.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2875 : Certifies 2875 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0265.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2876 : Certifies 2876 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0266.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2877 : Certifies 2877 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0267.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2878 : Certifies 2878 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0268.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2879 : Certifies 2879 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0269.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2880 : Certifies 2880 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0270.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2881 : Certifies 2881 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0271.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2882 : Certifies 2882 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0272.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B094 (j : Fin 30) :
    Certifies (2853 + j.val) := by
  fin_cases j
  · exact projection_2853
  · exact projection_2854
  · exact projection_2855
  · exact projection_2856
  · exact projection_2857
  · exact projection_2858
  · exact projection_2859
  · exact projection_2860
  · exact projection_2861
  · exact projection_2862
  · exact projection_2863
  · exact projection_2864
  · exact projection_2865
  · exact projection_2866
  · exact projection_2867
  · exact projection_2868
  · exact projection_2869
  · exact projection_2870
  · exact projection_2871
  · exact projection_2872
  · exact projection_2873
  · exact projection_2874
  · exact projection_2875
  · exact projection_2876
  · exact projection_2877
  · exact projection_2878
  · exact projection_2879
  · exact projection_2880
  · exact projection_2881
  · exact projection_2882

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
