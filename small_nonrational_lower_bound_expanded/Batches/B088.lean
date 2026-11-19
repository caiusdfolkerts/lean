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
/- Source: ProjectionCertificates/R_m15e10q1_0059.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0059

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 307, 611, 589, 229, 421, 666, 562, 402, 898, 220, 652, 900, 632, 496, 35, 259, 515, 165, 69, 261, 517, 97, 289, 577, 50, 146, 274, 530, 546, 386, 642, 770, 76, 140, 524, 196, 388, 644, 772, 88, 152, 536, 584, 648, 112, 304, 560, 208, 400, 224, 608, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_307, vertices_611, vertices_589, vertices_229, vertices_421, vertices_666, vertices_562, vertices_402, vertices_898, vertices_220, vertices_652, vertices_900, vertices_632, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_165, vertices_69, vertices_261, vertices_517, vertices_97, vertices_289, vertices_577, vertices_50, vertices_146, vertices_274, vertices_530, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_196, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_536, vertices_584, vertices_648, vertices_112, vertices_304, vertices_560, vertices_208, vertices_400, vertices_224, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_307), (false, vertices_611), (false, vertices_589), (false, vertices_229), (false, vertices_421), (true, vertices_146), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_140), (true, vertices_644), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_648), (true, vertices_112), (true, vertices_560), (true, vertices_208), (true, vertices_400), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 23 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_307) then 17 else
  if p.val = (false, vertices_611) then 18 else
  if p.val = (false, vertices_589) then 20 else
  if p.val = (false, vertices_229) then 21 else
  if p.val = (false, vertices_421) then 22 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 146 1
cert_row_4 1 1 2 3 5 6 220 76 2
cert_row_4 2 2 3 4 5 8 632 88 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 666
cert_cover_5 0 0 0 2 3 6 146 666 1
cert_coverFacet 1 562
cert_cover_2 1 3 0 4 8 50 562 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 898
cert_cover_2 3 6 0 7 8 386 898 3
cert_coverFacet 4 220
cert_cover_5 4 1 1 2 3 5 76 220 2
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 900
cert_cover_2 6 6 1 7 8 388 900 3
cert_coverFacet 7 632
cert_cover_5 7 2 2 3 4 5 88 632 2
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0059

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0060.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0060

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 285, 557, 357, 713, 329, 225, 406, 534, 422, 550, 722, 540, 856, 496, 13, 37, 261, 73, 265, 521, 97, 161, 545, 193, 321, 641, 22, 38, 390, 518, 146, 530, 162, 546, 642, 28, 524, 276, 532, 292, 548, 280, 536, 328, 584, 208, 336, 592, 400, 224, 352, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_285, vertices_557, vertices_357, vertices_713, vertices_329, vertices_225, vertices_406, vertices_534, vertices_422, vertices_550, vertices_722, vertices_540, vertices_856, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_261, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_641, vertices_22, vertices_38, vertices_390, vertices_518, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_28, vertices_524, vertices_276, vertices_532, vertices_292, vertices_548, vertices_280, vertices_536, vertices_328, vertices_584, vertices_208, vertices_336, vertices_592, vertices_400, vertices_224, vertices_352, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_285), (false, vertices_557), (false, vertices_357), (false, vertices_713), (false, vertices_329), (false, vertices_225), (true, vertices_22), (true, vertices_38), (true, vertices_390), (true, vertices_518), (true, vertices_146), (true, vertices_530), (true, vertices_532), (true, vertices_536), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_38) then 3 else
  if p.val = (true, vertices_390) then 16 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 329 1 225 22 38 518 146 530 532 536 208 336 592 400 416 675 390 285 557 357 713
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_4 1 0 3 5 6 8 722 146 2
cert_row_4 2 2 3 5 7 8 856 280 2
cert_row_4 3 3 4 5 6 7 496 208 1
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 22 406 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 422
cert_cover_5 2 0 0 1 4 6 38 422 3
cert_coverFacet 3 550
cert_cover_2 3 1 0 4 8 38 550 3
cert_coverFacet 4 722
cert_cover_5 4 1 0 3 5 6 146 722 2
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 856
cert_cover_5 6 2 2 3 5 7 280 856 2
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 208 496 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0060

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0061.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0061

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [143, 391, 557, 309, 713, 929, 526, 342, 534, 458, 586, 626, 564, 496, 736, 135, 13, 37, 261, 137, 521, 289, 545, 385, 641, 14, 22, 262, 518, 74, 138, 522, 82, 530, 322, 578, 386, 524, 52, 276, 532, 548, 200, 584, 112, 304, 560, 336, 224, 608, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_143, vertices_391, vertices_557, vertices_309, vertices_713, vertices_929, vertices_526, vertices_342, vertices_534, vertices_458, vertices_586, vertices_626, vertices_564, vertices_496, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_135, vertices_13, vertices_37, vertices_261, vertices_137, vertices_521, vertices_289, vertices_545, vertices_385, vertices_641, vertices_14, vertices_22, vertices_262, vertices_518, vertices_74, vertices_138, vertices_522, vertices_82, vertices_530, vertices_322, vertices_578, vertices_386, vertices_524, vertices_52, vertices_276, vertices_532, vertices_548, vertices_200, vertices_584, vertices_112, vertices_304, vertices_560, vertices_336, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_143), (false, vertices_391), (false, vertices_557), (false, vertices_309), (false, vertices_713), (false, vertices_929), (true, vertices_22), (true, vertices_518), (true, vertices_74), (true, vertices_522), (true, vertices_82), (true, vertices_530), (true, vertices_322), (true, vertices_578), (true, vertices_532), (true, vertices_112), (true, vertices_560), (true, vertices_336), (true, vertices_224), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_143) then 16 else
  if p.val = (false, vertices_391) then 17 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_309) then 20 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_143), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 22 3
cert_row_4 1 0 2 5 6 7 458 74 3
cert_row_4 2 0 3 4 5 8 626 82 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 342
cert_cover_5 1 0 0 1 3 5 22 342 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 458
cert_cover_5 3 1 0 2 5 6 74 458 3
cert_coverFacet 4 586
cert_cover_2 4 2 0 5 8 74 586 3
cert_coverFacet 5 626
cert_cover_5 5 2 0 3 4 5 82 626 2
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coverFacet 8 736
cert_cover_2 8 5 4 6 8 224 736 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0061

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0062.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0062

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 93, 565, 709, 369, 481, 806, 426, 714, 778, 284, 588, 780, 308, 472, 21, 69, 517, 49, 81, 353, 161, 545, 193, 641, 138, 266, 522, 162, 290, 546, 642, 770, 28, 76, 268, 524, 52, 276, 292, 548, 580, 772, 88, 280, 200, 584, 392, 776, 304, 336, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_93, vertices_565, vertices_709, vertices_369, vertices_481, vertices_806, vertices_426, vertices_714, vertices_778, vertices_284, vertices_588, vertices_780, vertices_308, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_517, vertices_49, vertices_81, vertices_353, vertices_161, vertices_545, vertices_193, vertices_641, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_28, vertices_76, vertices_268, vertices_524, vertices_52, vertices_276, vertices_292, vertices_548, vertices_580, vertices_772, vertices_88, vertices_280, vertices_200, vertices_584, vertices_392, vertices_776, vertices_304, vertices_336, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_93), (false, vertices_565), (false, vertices_709), (false, vertices_369), (false, vertices_481), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_770), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_292), (true, vertices_772), (true, vertices_280), (true, vertices_200), (true, vertices_584), (true, vertices_392), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 22 23 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_776) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_4 1 0 2 4 6 7 426 138 2
cert_row_4 2 0 2 5 6 8 714 138 2
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 426
cert_cover_5 1 1 0 2 4 6 138 426 2
cert_coverFacet 2 714
cert_cover_5 2 2 0 2 5 6 138 714 2
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 588
cert_cover_2 5 2 1 5 8 76 588 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coverFacet 8 472
cert_cover_5 8 3 2 3 5 6 88 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0062

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0063.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0063

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 787, 547, 387, 341, 625, 481, 902, 618, 650, 604, 364, 428, 652, 788, 35, 131, 259, 515, 81, 273, 529, 97, 161, 545, 321, 385, 42, 138, 522, 546, 386, 642, 770, 300, 76, 140, 524, 84, 276, 532, 324, 388, 644, 772, 104, 168, 584, 648, 592, 784, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_787, vertices_547, vertices_387, vertices_341, vertices_625, vertices_481, vertices_902, vertices_618, vertices_650, vertices_604, vertices_364, vertices_428, vertices_652, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_81, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_321, vertices_385, vertices_42, vertices_138, vertices_522, vertices_546, vertices_386, vertices_642, vertices_770, vertices_300, vertices_76, vertices_140, vertices_524, vertices_84, vertices_276, vertices_532, vertices_324, vertices_388, vertices_644, vertices_772, vertices_104, vertices_168, vertices_584, vertices_648, vertices_592, vertices_784, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_787), (false, vertices_547), (false, vertices_387), (false, vertices_341), (false, vertices_625), (false, vertices_481), (true, vertices_522), (true, vertices_642), (true, vertices_300), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_532), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_104), (true, vertices_584), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 15 else
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_300) then 19 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_648) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_300), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_2 1 1 2 4 7 300
cert_row_4 2 0 2 4 5 8 618 42 3
cert_row_4 3 1 2 3 5 8 604 76 2
cert_rows
cert_pivot_2 6 7 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 618
cert_cover_5 1 2 0 2 4 5 42 618 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 604
cert_cover_5 3 3 1 2 3 5 76 604 2
cert_coverFacet 4 364
cert_cover_5 4 1 1 2 4 5 300 364 3
cert_coverFacet 5 428
cert_cover_5 5 1 1 2 4 6 300 428 3
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0063

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0064.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0064

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 541, 117, 709, 345, 457, 806, 426, 778, 738, 284, 780, 308, 612, 496, 21, 69, 517, 25, 329, 137, 521, 81, 193, 641, 138, 266, 522, 162, 290, 546, 642, 770, 28, 268, 524, 52, 276, 100, 292, 548, 580, 772, 280, 392, 776, 112, 304, 336, 224, 608, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_541, vertices_117, vertices_709, vertices_345, vertices_457, vertices_806, vertices_426, vertices_778, vertices_738, vertices_284, vertices_780, vertices_308, vertices_612, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_517, vertices_25, vertices_329, vertices_137, vertices_521, vertices_81, vertices_193, vertices_641, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_52, vertices_276, vertices_100, vertices_292, vertices_548, vertices_580, vertices_772, vertices_280, vertices_392, vertices_776, vertices_112, vertices_304, vertices_336, vertices_224, vertices_608, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_541), (false, vertices_117), (false, vertices_709), (false, vertices_345), (false, vertices_457), (true, vertices_266), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_268), (true, vertices_276), (true, vertices_292), (true, vertices_548), (true, vertices_772), (true, vertices_776), (true, vertices_304), (true, vertices_224), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_541) then 18 else
  if p.val = (false, vertices_117) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 266 1 162 2 290 546 770 268 276 292 548 772 776 304 224 608 416 651 541 117 709 345 457
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_4 1 0 2 4 6 7 426 138 2
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 426
cert_cover_5 1 1 0 2 4 6 138 426 2
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 738
cert_cover_5 3 2 0 4 5 6 162 738 2
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 612
cert_cover_2 7 4 1 5 8 100 612 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0064

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0065.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0065

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 205, 453, 681, 433, 865, 334, 526, 406, 534, 370, 562, 610, 652, 692, 197, 73, 137, 521, 161, 289, 545, 321, 577, 385, 14, 22, 262, 518, 74, 522, 50, 274, 530, 98, 546, 322, 578, 76, 140, 524, 148, 532, 324, 388, 644, 648, 176, 304, 560, 400, 352, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_205, vertices_453, vertices_681, vertices_433, vertices_865, vertices_334, vertices_526, vertices_406, vertices_534, vertices_370, vertices_562, vertices_610, vertices_652, vertices_692] (by decide +kernel)
  polygons := literalFinset [vertices_197, vertices_73, vertices_137, vertices_521, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_14, vertices_22, vertices_262, vertices_518, vertices_74, vertices_522, vertices_50, vertices_274, vertices_530, vertices_98, vertices_546, vertices_322, vertices_578, vertices_76, vertices_140, vertices_524, vertices_148, vertices_532, vertices_324, vertices_388, vertices_644, vertices_648, vertices_176, vertices_304, vertices_560, vertices_400, vertices_352, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_205), (false, vertices_453), (false, vertices_681), (false, vertices_433), (false, vertices_865), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_546), (true, vertices_322), (true, vertices_524), (true, vertices_148), (true, vertices_532), (true, vertices_644), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 16 else
  if p.val = (false, vertices_205) then 18 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_322) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_148) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_644) then 13 else
  if p.val = (true, vertices_560) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 7 334 14 3
cert_row_4 1 0 3 4 5 7 370 50 3
cert_row_4 2 0 1 3 6 7 406 22 3
cert_row_4 3 1 3 4 6 8 692 148 2
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 406
cert_cover_5 2 2 0 1 3 6 22 406 3
cert_coverFacet 3 534
cert_cover_2 3 1 0 3 8 22 534 3
cert_coverFacet 4 370
cert_cover_5 4 1 0 3 4 5 50 370 3
cert_coverFacet 5 562
cert_cover_2 5 3 0 4 8 50 562 3
cert_coverFacet 6 610
cert_cover_2 6 4 0 5 8 98 610 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 692
cert_cover_5 8 3 1 3 4 6 148 692 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0065

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0066.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0066

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 341, 229, 805, 457, 673, 790, 570, 282, 234, 394, 674, 604, 620, 344, 37, 69, 261, 161, 545, 193, 321, 385, 641, 769, 26, 42, 138, 266, 274, 530, 162, 546, 386, 642, 770, 588, 84, 276, 532, 100, 548, 772, 88, 280, 536, 104, 552, 200, 328, 392, 336, 224, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_341, vertices_229, vertices_805, vertices_457, vertices_673, vertices_790, vertices_570, vertices_282, vertices_234, vertices_394, vertices_674, vertices_604, vertices_620, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_261, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_138, vertices_266, vertices_274, vertices_530, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_588, vertices_84, vertices_276, vertices_532, vertices_100, vertices_548, vertices_772, vertices_88, vertices_280, vertices_536, vertices_104, vertices_552, vertices_200, vertices_328, vertices_392, vertices_336, vertices_224, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_341), (false, vertices_229), (false, vertices_805), (false, vertices_457), (false, vertices_673), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_588), (true, vertices_532), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_104), (true, vertices_552)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_341) then 21 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_805) then 23 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (false, vertices_673) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_162) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_588) then 19 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_104) then 13 else
  if p.val = (true, vertices_552) then 14 else
  0
cert_priority
cert_nodeAtPriority_43 673 1 26 2 42 138 266 274 530 162 546 532 88 280 536 104 552 899 457 588 341 229 805
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_2 1 1 2 5 8 588
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 0 2 4 5 6 234 42 3
cert_rows
cert_pivot_2 7 1 3 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 570
cert_cover_5 1 2 0 2 3 4 26 570 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 234
cert_cover_5 3 3 0 2 4 5 42 234 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 604
cert_cover_5 6 1 1 2 3 5 588 604 2
cert_coverFacet 7 620
cert_cover_5 7 1 1 2 4 5 588 620 2
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0066

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0067.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0067

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 421, 617, 169, 457, 817, 310, 214, 454, 594, 786, 684, 564, 660, 728, 41, 73, 137, 161, 289, 545, 321, 577, 385, 769, 22, 198, 262, 82, 274, 530, 322, 578, 770, 52, 148, 532, 164, 292, 548, 388, 644, 168, 552, 200, 584, 648, 304, 560, 208, 592, 656, 784, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_421, vertices_617, vertices_169, vertices_457, vertices_817, vertices_310, vertices_214, vertices_454, vertices_594, vertices_786, vertices_684, vertices_564, vertices_660, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_137, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_769, vertices_22, vertices_198, vertices_262, vertices_82, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_52, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_168, vertices_552, vertices_200, vertices_584, vertices_648, vertices_304, vertices_560, vertices_208, vertices_592, vertices_656, vertices_784, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_421), (false, vertices_617), (false, vertices_169), (false, vertices_457), (false, vertices_817), (true, vertices_22), (true, vertices_198), (true, vertices_262), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_52), (true, vertices_148), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_648), (true, vertices_208), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_198) then 17 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 169 22 262 82 274 530 52 148 532 548 644 648 208 592 656 835 198 421 617 457 817
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 22 3
cert_row_2 1 0 1 5 6 198
cert_row_4 2 1 2 4 6 8 684 164 1
cert_row_4 3 2 3 5 6 8 728 200 1
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 22 310 3
cert_coverFacet 1 214
cert_cover_5 1 1 0 1 3 5 22 214 3
cert_coverFacet 2 454
cert_cover_5 2 1 0 1 5 7 198 454 3
cert_coverFacet 3 594
cert_cover_2 3 3 0 5 8 82 594 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 684
cert_cover_5 5 2 1 2 4 6 164 684 1
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 728
cert_cover_5 8 3 2 3 5 6 200 728 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0067

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0068.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0068

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 421, 709, 681, 817, 590, 214, 406, 122, 538, 786, 568, 232, 712, 496, 133, 261, 517, 161, 289, 545, 641, 769, 150, 70, 262, 518, 26, 74, 522, 82, 274, 530, 770, 196, 580, 388, 56, 536, 104, 168, 552, 200, 584, 648, 112, 304, 560, 208, 400, 784, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_421, vertices_709, vertices_681, vertices_817, vertices_590, vertices_214, vertices_406, vertices_122, vertices_538, vertices_786, vertices_568, vertices_232, vertices_712, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_150, vertices_70, vertices_262, vertices_518, vertices_26, vertices_74, vertices_522, vertices_82, vertices_274, vertices_530, vertices_770, vertices_196, vertices_580, vertices_388, vertices_56, vertices_536, vertices_104, vertices_168, vertices_552, vertices_200, vertices_584, vertices_648, vertices_112, vertices_304, vertices_560, vertices_208, vertices_400, vertices_784, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_421), (false, vertices_709), (false, vertices_681), (false, vertices_817), (true, vertices_150), (true, vertices_70), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_56), (true, vertices_536), (true, vertices_104), (true, vertices_200), (true, vertices_584), (true, vertices_112), (true, vertices_208), (true, vertices_400), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_817) then 25 else
  if p.val = (true, vertices_150) then 18 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_224) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_150), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
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
cert_row_4 0 0 1 2 5 8 590 70 2
cert_row_2 1 0 1 3 6 150
cert_row_4 2 0 2 3 4 5 122 26 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 8 1 0 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 70 590 2
cert_coverFacet 1 214
cert_cover_5 1 1 0 1 3 5 150 214 3
cert_coverFacet 2 406
cert_cover_5 2 1 0 1 3 7 150 406 3
cert_coverFacet 3 122
cert_cover_5 3 2 0 2 3 4 26 122 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coverFacet 8 712
cert_cover_2 8 5 2 6 8 200 712 3
cert_coverFacet 9 496
cert_cover_5 9 3 3 4 5 6 112 496 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0068

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0069.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0069

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 837, 665, 809, 457, 614, 570, 114, 210, 658, 188, 428, 116, 468, 804, 137, 265, 521, 193, 321, 577, 641, 769, 50, 82, 146, 530, 98, 546, 194, 578, 642, 172, 52, 84, 148, 100, 292, 548, 324, 580, 388, 772, 56, 152, 536, 296, 552, 392, 112, 208, 656, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_837, vertices_665, vertices_809, vertices_457, vertices_614, vertices_570, vertices_114, vertices_210, vertices_658, vertices_188, vertices_428, vertices_116, vertices_468, vertices_804] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_50, vertices_82, vertices_146, vertices_530, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_172, vertices_52, vertices_84, vertices_148, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_388, vertices_772, vertices_56, vertices_152, vertices_536, vertices_296, vertices_552, vertices_392, vertices_112, vertices_208, vertices_656, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_837), (false, vertices_665), (false, vertices_809), (false, vertices_457), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_98), (true, vertices_546), (true, vertices_172), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_388), (true, vertices_56), (true, vertices_112), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_809) then 23 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_172) then 20 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_56) then 13 else
  if p.val = (true, vertices_112) then 14 else
  if p.val = (true, vertices_208) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_172), by decide +kernel⟩
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
cert_row_4 0 1 3 5 6 7 468 84 3
cert_row_2 1 1 2 4 6 172
cert_row_4 2 0 1 4 5 8 614 98 1
cert_row_4 3 0 2 3 4 8 570 50 1
cert_rows
cert_pivot_2 7 6 1 0
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 2 0 1 4 5 98 614 1
cert_coverFacet 1 570
cert_cover_5 1 3 0 2 3 4 50 570 1
cert_coverFacet 2 114
cert_cover_2 2 3 0 4 5 50 114 3
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 188
cert_cover_5 5 1 1 2 3 4 172 188 2
cert_coverFacet 6 428
cert_cover_5 6 1 1 2 4 7 172 428 3
cert_coverFacet 7 116
cert_cover_2 7 3 1 4 5 52 116 3
cert_coverFacet 8 468
cert_cover_5 8 0 1 3 5 6 84 468 3
cert_coverFacet 9 804
cert_cover_2 9 4 1 7 8 292 804 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0069

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0070.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0070

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 309, 613, 709, 121, 465, 654, 806, 794, 394, 568, 216, 408, 744, 816, 37, 581, 133, 261, 49, 81, 273, 97, 193, 385, 134, 262, 518, 138, 266, 522, 386, 770, 292, 548, 644, 56, 88, 152, 280, 536, 104, 552, 200, 392, 648, 304, 560, 208, 400, 784, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_309, vertices_613, vertices_709, vertices_121, vertices_465, vertices_654, vertices_806, vertices_794, vertices_394, vertices_568, vertices_216, vertices_408, vertices_744, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_581, vertices_133, vertices_261, vertices_49, vertices_81, vertices_273, vertices_97, vertices_193, vertices_385, vertices_134, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_386, vertices_770, vertices_292, vertices_548, vertices_644, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_552, vertices_200, vertices_392, vertices_648, vertices_304, vertices_560, vertices_208, vertices_400, vertices_784, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_309), (false, vertices_613), (false, vertices_709), (false, vertices_121), (false, vertices_465), (true, vertices_518), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_770), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_552), (true, vertices_200), (true, vertices_392), (true, vertices_648), (true, vertices_560), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 16 else
  if p.val = (false, vertices_309) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_121) then 22 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
cert_nodeAtPriority_68 0 518 1 138 266 522 770 152 280 536 552 200 392 648 560 784 800 391 309 613 709 121 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 7 8 794 266 2
cert_row_4 1 0 1 4 7 8 806 262 2
cert_row_4 2 0 1 2 6 8 654 134 2
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 3 7 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 134 654 2
cert_coverFacet 1 806
cert_cover_5 1 1 0 1 4 7 262 806 2
cert_coverFacet 2 794
cert_cover_5 2 0 0 2 3 7 266 794 2
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 216
cert_cover_2 5 3 2 5 6 88 216 3
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 104 744 3
cert_coverFacet 8 816
cert_cover_2 8 4 3 7 8 304 816 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0070

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0071.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0071

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 589, 405, 453, 793, 361, 182, 646, 810, 306, 786, 738, 708, 616, 496, 21, 69, 389, 517, 73, 265, 521, 273, 529, 321, 22, 134, 518, 50, 274, 530, 162, 290, 546, 642, 770, 148, 196, 580, 644, 104, 296, 552, 584, 776, 176, 304, 400, 784, 224, 352, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_589, vertices_405, vertices_453, vertices_793, vertices_361, vertices_182, vertices_646, vertices_810, vertices_306, vertices_786, vertices_738, vertices_708, vertices_616, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_389, vertices_517, vertices_73, vertices_265, vertices_521, vertices_273, vertices_529, vertices_321, vertices_22, vertices_134, vertices_518, vertices_50, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_148, vertices_196, vertices_580, vertices_644, vertices_104, vertices_296, vertices_552, vertices_584, vertices_776, vertices_176, vertices_304, vertices_400, vertices_784, vertices_224, vertices_352, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_589), (false, vertices_405), (false, vertices_453), (false, vertices_793), (false, vertices_361), (true, vertices_134), (true, vertices_50), (true, vertices_274), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_770), (true, vertices_644), (true, vertices_552), (true, vertices_176), (true, vertices_304), (true, vertices_224), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 16 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_793) then 22 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 134 1 50 2 274 162 290 546 642 770 644 552 176 304 224 608 704 535 589 405 453 793 361
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 6 182 22 3
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 4 22 182 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 810
cert_cover_5 2 1 0 2 4 7 290 810 1
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 162 738 2
cert_coverFacet 6 708
cert_cover_2 6 5 1 6 8 196 708 3
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 176 496 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0071

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0072.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0072

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 589, 309, 213, 805, 345, 182, 714, 394, 818, 402, 674, 740, 456, 464, 21, 293, 69, 517, 73, 265, 521, 81, 273, 769, 138, 266, 522, 50, 146, 274, 162, 546, 386, 642, 770, 52, 148, 164, 548, 196, 580, 200, 328, 584, 392, 304, 208, 336, 400, 672, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_589, vertices_309, vertices_213, vertices_805, vertices_345, vertices_182, vertices_714, vertices_394, vertices_818, vertices_402, vertices_674, vertices_740, vertices_456, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_293, vertices_69, vertices_517, vertices_73, vertices_265, vertices_521, vertices_81, vertices_273, vertices_769, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_52, vertices_148, vertices_164, vertices_548, vertices_196, vertices_580, vertices_200, vertices_328, vertices_584, vertices_392, vertices_304, vertices_208, vertices_336, vertices_400, vertices_672, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_589), (false, vertices_309), (false, vertices_213), (false, vertices_805), (false, vertices_345), (true, vertices_138), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_164), (true, vertices_200), (true, vertices_392), (true, vertices_400), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_309) then 21 else
  if p.val = (false, vertices_213) then 22 else
  if p.val = (false, vertices_805) then 23 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_448) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_42 138 1 50 2 146 274 162 546 386 642 164 200 392 400 672 448 704 779 589 345 309 213 805
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 138 2
cert_row_4 1 0 3 4 7 8 818 50 3
cert_row_4 2 0 1 3 4 6 182 50 1
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 2 0 1 3 4 50 182 1
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 138 714 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 818
cert_cover_5 3 1 0 3 4 7 50 818 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 164 740 2
cert_coverFacet 7 456
cert_cover_2 7 5 2 6 7 200 456 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0072

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0073.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0073

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 589, 397, 325, 681, 465, 598, 426, 818, 210, 402, 674, 316, 572, 340, 13, 69, 261, 137, 521, 193, 321, 577, 385, 641, 82, 146, 274, 530, 162, 290, 546, 194, 578, 386, 642, 60, 268, 524, 84, 276, 532, 324, 580, 168, 296, 552, 392, 304, 560, 208, 336, 400, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_589, vertices_397, vertices_325, vertices_681, vertices_465, vertices_598, vertices_426, vertices_818, vertices_210, vertices_402, vertices_674, vertices_316, vertices_572, vertices_340] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_137, vertices_521, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_82, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_194, vertices_578, vertices_386, vertices_642, vertices_60, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_324, vertices_580, vertices_168, vertices_296, vertices_552, vertices_392, vertices_304, vertices_560, vertices_208, vertices_336, vertices_400, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_589), (false, vertices_397), (false, vertices_325), (false, vertices_681), (false, vertices_465), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_60), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_296), (true, vertices_304), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 23 17 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_589) then 21 else
  if p.val = (false, vertices_397) then 22 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_681) then 24 else
  if p.val = (false, vertices_465) then 18 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_60) then 19 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_560) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 325 1 82 3 146 2 274 530 162 290 546 386 84 276 532 296 304 560 707 465 60 589 397 681
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 82 1
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 2 4 6 7 426 162 1
cert_row_4 3 0 3 4 7 8 818 274 2
cert_rows
cert_pivot_2 5 1 2 0
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 82 598 1
cert_coverFacet 1 426
cert_cover_5 1 2 0 2 4 6 162 426 1
cert_coverFacet 2 818
cert_cover_5 2 3 0 3 4 7 274 818 2
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 316
cert_cover_5 6 1 1 2 3 7 60 316 3
cert_coverFacet 7 572
cert_cover_5 7 1 1 2 3 8 60 572 3
cert_coverFacet 8 340
cert_cover_2 8 3 1 5 7 84 340 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0073

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0074.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0074

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 589, 341, 805, 425, 457, 790, 186, 714, 306, 658, 802, 596, 496, 720, 69, 261, 517, 41, 73, 393, 521, 289, 545, 321, 42, 138, 522, 50, 146, 274, 530, 290, 546, 642, 770, 84, 276, 532, 580, 772, 168, 200, 584, 176, 304, 208, 336, 592, 656, 416, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_589, vertices_341, vertices_805, vertices_425, vertices_457, vertices_790, vertices_186, vertices_714, vertices_306, vertices_658, vertices_802, vertices_596, vertices_496, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_41, vertices_73, vertices_393, vertices_521, vertices_289, vertices_545, vertices_321, vertices_42, vertices_138, vertices_522, vertices_50, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_642, vertices_770, vertices_84, vertices_276, vertices_532, vertices_580, vertices_772, vertices_168, vertices_200, vertices_584, vertices_176, vertices_304, vertices_208, vertices_336, vertices_592, vertices_656, vertices_416, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_589), (false, vertices_341), (false, vertices_805), (false, vertices_425), (false, vertices_457), (true, vertices_138), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_642), (true, vertices_770), (true, vertices_532), (true, vertices_176), (true, vertices_304), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 16 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 138 1 50 2 146 274 530 290 642 770 532 176 304 208 592 656 704 555 589 341 805 425 457
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_4 1 0 2 5 6 8 714 138 2
cert_row_4 2 0 2 3 4 6 186 42 2
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 1 8 0 3
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 186
cert_cover_5 1 2 0 2 3 4 42 186 2
cert_coverFacet 2 714
cert_cover_5 2 1 0 2 5 6 138 714 2
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 176 496 2
cert_coverFacet 8 720
cert_cover_2 8 5 3 6 8 208 720 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0074

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0075.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0075

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 155, 563, 803, 661, 837, 122, 298, 394, 716, 452, 600, 664, 488, 880, 19, 547, 131, 259, 133, 261, 517, 145, 529, 769, 26, 42, 138, 266, 50, 290, 386, 196, 324, 580, 388, 644, 88, 152, 536, 104, 296, 200, 584, 392, 648, 112, 560, 592, 656, 352, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_155, vertices_563, vertices_803, vertices_661, vertices_837, vertices_122, vertices_298, vertices_394, vertices_716, vertices_452, vertices_600, vertices_664, vertices_488, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_547, vertices_131, vertices_259, vertices_133, vertices_261, vertices_517, vertices_145, vertices_529, vertices_769, vertices_26, vertices_42, vertices_138, vertices_266, vertices_50, vertices_290, vertices_386, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_88, vertices_152, vertices_536, vertices_104, vertices_296, vertices_200, vertices_584, vertices_392, vertices_648, vertices_112, vertices_560, vertices_592, vertices_656, vertices_352, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_155), (false, vertices_563), (false, vertices_803), (false, vertices_661), (false, vertices_837), (true, vertices_42), (true, vertices_266), (true, vertices_196), (true, vertices_88), (true, vertices_536), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_584), (true, vertices_392), (true, vertices_648), (true, vertices_112), (true, vertices_592), (true, vertices_352), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 15 23 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 16 else
  if p.val = (false, vertices_155) then 20 else
  if p.val = (false, vertices_563) then 21 else
  if p.val = (false, vertices_803) then 22 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_196) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 5 122 26 3
cert_row_4 1 1 2 5 6 8 716 196 1
cert_row_4 2 2 4 5 6 7 488 104 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 122
cert_cover_5 0 0 0 2 3 4 26 122 3
cert_coverFacet 1 298
cert_cover_2 1 2 0 4 7 42 298 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 716
cert_cover_5 3 1 1 2 5 6 196 716 1
cert_coverFacet 4 452
cert_cover_2 4 5 1 6 7 196 452 3
cert_coverFacet 5 600
cert_cover_2 5 3 2 5 8 88 600 3
cert_coverFacet 6 664
cert_cover_2 6 3 2 6 8 152 664 3
cert_coverFacet 7 488
cert_cover_5 7 2 2 4 5 6 104 488 3
cert_coverFacet 8 880
cert_cover_5 8 3 3 4 5 7 112 880 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0075

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0076.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0076

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 789, 709, 681, 305, 561, 481, 590, 774, 570, 218, 466, 786, 440, 712, 69, 261, 517, 49, 273, 529, 161, 289, 545, 193, 321, 641, 70, 262, 518, 26, 74, 522, 210, 274, 530, 322, 770, 580, 772, 56, 152, 168, 552, 200, 584, 648, 304, 560, 400, 784, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_789, vertices_709, vertices_681, vertices_305, vertices_561, vertices_481, vertices_590, vertices_774, vertices_570, vertices_218, vertices_466, vertices_786, vertices_440, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_70, vertices_262, vertices_518, vertices_26, vertices_74, vertices_522, vertices_210, vertices_274, vertices_530, vertices_322, vertices_770, vertices_580, vertices_772, vertices_56, vertices_152, vertices_168, vertices_552, vertices_200, vertices_584, vertices_648, vertices_304, vertices_560, vertices_400, vertices_784, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_789), (false, vertices_709), (false, vertices_681), (false, vertices_305), (false, vertices_561), (false, vertices_481), (true, vertices_518), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_210), (true, vertices_274), (true, vertices_530), (true, vertices_770), (true, vertices_56), (true, vertices_152), (true, vertices_200), (true, vertices_584), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 15 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (false, vertices_561) then 1 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_210) then 16 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
cert_nodeAtPriority_53 0 305 1 561 518 26 74 522 274 530 770 56 152 200 584 400 327 210 789 709 681 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 70 2
cert_row_2 1 0 3 5 6 210
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 70 590 2
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 570
cert_cover_5 2 2 0 2 3 4 26 570 3
cert_coverFacet 3 218
cert_cover_5 3 1 0 2 3 5 26 218 3
cert_coverFacet 4 466
cert_cover_5 4 1 0 3 5 7 210 466 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 440
cert_cover_5 6 3 2 3 4 6 56 440 3
cert_coverFacet 7 712
cert_cover_2 7 5 2 6 8 200 712 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0076

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0077.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0077

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 787, 451, 109, 809, 481, 662, 434, 706, 300, 716, 780, 244, 308, 788, 67, 259, 515, 41, 73, 521, 97, 289, 449, 769, 146, 274, 530, 194, 578, 386, 642, 44, 76, 268, 524, 52, 148, 276, 532, 100, 292, 196, 644, 772, 296, 584, 776, 176, 304, 784, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_787, vertices_451, vertices_109, vertices_809, vertices_481, vertices_662, vertices_434, vertices_706, vertices_300, vertices_716, vertices_780, vertices_244, vertices_308, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_41, vertices_73, vertices_521, vertices_97, vertices_289, vertices_449, vertices_769, vertices_146, vertices_274, vertices_530, vertices_194, vertices_578, vertices_386, vertices_642, vertices_44, vertices_76, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_532, vertices_100, vertices_292, vertices_196, vertices_644, vertices_772, vertices_296, vertices_584, vertices_776, vertices_176, vertices_304, vertices_784, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_787), (false, vertices_451), (false, vertices_109), (false, vertices_809), (false, vertices_481), (true, vertices_146), (true, vertices_642), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_196), (true, vertices_644), (true, vertices_772), (true, vertices_176), (true, vertices_304), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 23 24 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 16 else
  if p.val = (false, vertices_787) then 17 else
  if p.val = (false, vertices_451) then 25 else
  if p.val = (false, vertices_109) then 19 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 7 434 146 2
cert_row_4 1 0 1 3 6 8 662 146 1
cert_row_4 2 1 2 5 6 8 716 76 3
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 7 0 2 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 146 662 1
cert_coverFacet 1 434
cert_cover_5 1 0 0 3 4 6 146 434 2
cert_coverFacet 2 706
cert_cover_2 2 5 0 6 8 194 706 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 716
cert_cover_5 4 2 1 2 5 6 76 716 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 244
cert_cover_5 6 3 1 3 4 5 52 244 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coverFacet 8 788
cert_cover_2 8 3 1 7 8 276 788 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0077

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0078.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0078

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 173, 653, 117, 837, 361, 598, 666, 426, 210, 450, 834, 692, 240, 480, 141, 37, 69, 517, 41, 265, 521, 97, 321, 769, 138, 266, 522, 82, 146, 530, 194, 322, 578, 386, 770, 52, 84, 532, 164, 580, 644, 168, 296, 648, 112, 176, 208, 656, 224, 352, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_173, vertices_653, vertices_117, vertices_837, vertices_361, vertices_598, vertices_666, vertices_426, vertices_210, vertices_450, vertices_834, vertices_692, vertices_240, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_141, vertices_37, vertices_69, vertices_517, vertices_41, vertices_265, vertices_521, vertices_97, vertices_321, vertices_769, vertices_138, vertices_266, vertices_522, vertices_82, vertices_146, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_52, vertices_84, vertices_532, vertices_164, vertices_580, vertices_644, vertices_168, vertices_296, vertices_648, vertices_112, vertices_176, vertices_208, vertices_656, vertices_224, vertices_352, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_173), (false, vertices_653), (false, vertices_117), (false, vertices_837), (false, vertices_361), (true, vertices_138), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_532), (true, vertices_176), (true, vertices_208), (true, vertices_656), (true, vertices_224), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 21 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_173) then 18 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_117) then 22 else
  if p.val = (false, vertices_837) then 23 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 138 2 82 1 146 530 194 322 578 386 532 176 208 656 224 416 448 779 173 653 361 117 837
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 82 1
cert_row_4 1 0 2 4 6 7 426 138 2
cert_row_4 2 0 2 3 6 8 666 138 2
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 5 7 0 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 82 598 1
cert_coverFacet 1 666
cert_cover_5 1 2 0 2 3 6 138 666 2
cert_coverFacet 2 426
cert_cover_5 2 1 0 2 4 6 138 426 2
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 450
cert_cover_2 4 5 0 6 7 194 450 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 52 692 3
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coverFacet 8 480
cert_cover_2 8 5 4 6 7 224 480 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0078

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0079.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0079

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 535, 805, 453, 841, 721, 558, 422, 602, 154, 170, 440, 344, 808, 464, 23, 133, 261, 517, 145, 529, 193, 321, 577, 769, 38, 134, 518, 26, 42, 138, 522, 146, 530, 162, 292, 548, 388, 88, 152, 280, 168, 296, 552, 328, 584, 776, 208, 336, 592, 400, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_535, vertices_805, vertices_453, vertices_841, vertices_721, vertices_558, vertices_422, vertices_602, vertices_154, vertices_170, vertices_440, vertices_344, vertices_808, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_133, vertices_261, vertices_517, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_769, vertices_38, vertices_134, vertices_518, vertices_26, vertices_42, vertices_138, vertices_522, vertices_146, vertices_530, vertices_162, vertices_292, vertices_548, vertices_388, vertices_88, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_328, vertices_584, vertices_776, vertices_208, vertices_336, vertices_592, vertices_400, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_535), (false, vertices_805), (false, vertices_453), (false, vertices_841), (false, vertices_721), (true, vertices_38), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_162), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_336), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 16 else
  if p.val = (false, vertices_535) then 17 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_62 38 26 42 138 522 162 88 152 280 168 296 552 336 400 416 151 535 805 453 841 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_4 1 0 1 2 4 8 558 38 2
cert_row_4 2 0 1 4 6 7 422 38 3
cert_row_4 3 2 3 4 6 7 440 152 2
cert_rows
cert_pivot_2 5 8 0 2
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 38 558 2
cert_coverFacet 1 422
cert_cover_5 1 2 0 1 4 6 38 422 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 5 26 602 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 170
cert_cover_2 4 2 0 4 6 42 170 3
cert_coverFacet 5 440
cert_cover_5 5 3 2 3 4 6 152 440 2
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0079

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0080.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0080

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 179, 291, 643, 333, 713, 481, 566, 722, 802, 812, 588, 436, 468, 596, 35, 131, 259, 515, 73, 265, 521, 161, 289, 193, 321, 641, 50, 146, 530, 290, 546, 642, 770, 76, 268, 524, 52, 84, 404, 532, 292, 548, 324, 580, 584, 776, 176, 208, 592, 416, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_179, vertices_291, vertices_643, vertices_333, vertices_713, vertices_481, vertices_566, vertices_722, vertices_802, vertices_812, vertices_588, vertices_436, vertices_468, vertices_596] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_193, vertices_321, vertices_641, vertices_50, vertices_146, vertices_530, vertices_290, vertices_546, vertices_642, vertices_770, vertices_76, vertices_268, vertices_524, vertices_52, vertices_84, vertices_404, vertices_532, vertices_292, vertices_548, vertices_324, vertices_580, vertices_584, vertices_776, vertices_176, vertices_208, vertices_592, vertices_416, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_179), (false, vertices_291), (false, vertices_643), (false, vertices_333), (false, vertices_713), (false, vertices_481), (true, vertices_530), (true, vertices_546), (true, vertices_524), (true, vertices_52), (true, vertices_84), (true, vertices_404), (true, vertices_532), (true, vertices_292), (true, vertices_548), (true, vertices_580), (true, vertices_208), (true, vertices_592), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_179) then 16 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_643) then 1 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_404) then 19 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
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
cert_row_4 0 0 3 5 6 8 722 146 2
cert_row_2 1 1 3 6 7 404
cert_row_4 2 0 1 3 4 8 566 50 1
cert_row_4 3 1 2 4 7 8 812 268 2
cert_rows
cert_pivot_2 5 6 0 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 2 0 1 3 4 50 566 1
cert_coverFacet 1 722
cert_cover_5 1 0 0 3 5 6 146 722 2
cert_coverFacet 2 802
cert_cover_2 2 4 0 7 8 290 802 3
cert_coverFacet 3 812
cert_cover_5 3 3 1 2 4 7 268 812 2
cert_coverFacet 4 588
cert_cover_2 4 2 1 5 8 76 588 3
cert_coverFacet 5 436
cert_cover_5 5 1 1 3 4 6 52 436 3
cert_coverFacet 6 468
cert_cover_5 6 1 1 3 5 6 84 468 3
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0080

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0081.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0081

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 109, 781, 197, 389, 681, 241, 454, 794, 690, 210, 338, 316, 372, 568, 13, 69, 133, 261, 41, 521, 97, 161, 193, 385, 641, 769, 82, 146, 274, 530, 194, 322, 386, 642, 770, 44, 268, 308, 100, 196, 324, 388, 56, 280, 536, 552, 776, 112, 176, 560, 208, 336, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_109, vertices_781, vertices_197, vertices_389, vertices_681, vertices_241, vertices_454, vertices_794, vertices_690, vertices_210, vertices_338, vertices_316, vertices_372, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_133, vertices_261, vertices_41, vertices_521, vertices_97, vertices_161, vertices_193, vertices_385, vertices_641, vertices_769, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_308, vertices_100, vertices_196, vertices_324, vertices_388, vertices_56, vertices_280, vertices_536, vertices_552, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_336, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_109), (false, vertices_781), (false, vertices_197), (false, vertices_389), (false, vertices_681), (false, vertices_241), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_308), (true, vertices_324), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_560), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_109) then 17 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_308) then 19 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_336) then 13 else
  0
cert_priority
cert_nodeAtPriority_54 197 389 82 146 274 530 194 322 324 56 280 536 560 336 899 109 781 308 681 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 194 1
cert_row_2 1 1 3 4 7 308
cert_row_4 2 0 2 3 7 8 794 274 1
cert_row_4 3 0 3 4 6 8 690 146 2
cert_rows
cert_pivot_2 5 1 2 0
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 0 0 1 5 6 194 454 1
cert_coverFacet 1 794
cert_cover_5 1 2 0 2 3 7 274 794 1
cert_coverFacet 2 690
cert_cover_5 2 3 0 3 4 6 146 690 2
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 316
cert_cover_5 5 1 1 2 3 4 44 316 2
cert_coverFacet 6 372
cert_cover_5 6 1 1 3 4 5 308 372 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0081

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0082.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0082

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 157, 313, 681, 721, 785, 110, 270, 326, 298, 850, 738, 284, 236, 468, 25, 41, 137, 145, 273, 529, 289, 545, 641, 769, 14, 70, 262, 42, 266, 98, 290, 546, 322, 578, 770, 28, 108, 140, 268, 148, 276, 196, 324, 280, 168, 296, 208, 336, 592, 784, 224, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_157, vertices_313, vertices_681, vertices_721, vertices_785, vertices_110, vertices_270, vertices_326, vertices_298, vertices_850, vertices_738, vertices_284, vertices_236, vertices_468] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_137, vertices_145, vertices_273, vertices_529, vertices_289, vertices_545, vertices_641, vertices_769, vertices_14, vertices_70, vertices_262, vertices_42, vertices_266, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_108, vertices_140, vertices_268, vertices_148, vertices_276, vertices_196, vertices_324, vertices_280, vertices_168, vertices_296, vertices_208, vertices_336, vertices_592, vertices_784, vertices_224, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_157), (false, vertices_313), (false, vertices_681), (false, vertices_721), (false, vertices_785), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_42), (true, vertices_266), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_108), (true, vertices_268), (true, vertices_276), (true, vertices_196), (true, vertices_324), (true, vertices_336), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_108) then 19 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_324) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 785 2 14 1 70 3 262 42 266 98 322 578 268 276 196 324 336 224 803 157 108 313 681 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 4 5 6 8 738 98 3
cert_row_4 2 0 3 5 7 8 850 322 1
cert_row_4 3 1 3 5 6 7 468 148 2
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 326
cert_cover_2 2 1 0 5 7 70 326 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 850
cert_cover_5 4 2 0 3 5 7 322 850 1
cert_coverFacet 5 738
cert_cover_5 5 1 0 4 5 6 98 738 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 236
cert_cover_5 7 0 1 2 4 6 108 236 3
cert_coverFacet 8 468
cert_cover_5 8 3 1 3 5 6 148 468 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0082

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0083.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0083

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 61, 601, 233, 817, 673, 206, 334, 390, 850, 930, 284, 172, 436, 344, 25, 41, 73, 49, 529, 161, 545, 193, 577, 641, 78, 134, 262, 194, 322, 578, 386, 642, 770, 28, 44, 140, 268, 52, 276, 164, 388, 88, 280, 168, 200, 328, 304, 336, 592, 784, 416, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_61, vertices_601, vertices_233, vertices_817, vertices_673, vertices_206, vertices_334, vertices_390, vertices_850, vertices_930, vertices_284, vertices_172, vertices_436, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_73, vertices_49, vertices_529, vertices_161, vertices_545, vertices_193, vertices_577, vertices_641, vertices_78, vertices_134, vertices_262, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_140, vertices_268, vertices_52, vertices_276, vertices_164, vertices_388, vertices_88, vertices_280, vertices_168, vertices_200, vertices_328, vertices_304, vertices_336, vertices_592, vertices_784, vertices_416, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_61), (false, vertices_601), (false, vertices_233), (false, vertices_817), (false, vertices_673), (true, vertices_78), (true, vertices_134), (true, vertices_262), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_276), (true, vertices_164), (true, vertices_388), (true, vertices_280), (true, vertices_328), (true, vertices_336), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_61) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (false, vertices_673) then 0 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 673 134 262 322 386 770 140 268 276 164 388 280 328 336 416 707 78 61 601 233 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 3 5 7 8 850 322 1
cert_row_4 2 0 4 6 7 8 930 386 1
cert_row_4 3 1 3 4 6 7 436 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 6 78 206 3
cert_coverFacet 1 334
cert_cover_5 1 0 0 1 2 7 78 334 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 850
cert_cover_5 3 1 0 3 5 7 322 850 1
cert_coverFacet 4 930
cert_cover_5 4 2 0 4 6 7 386 930 1
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 172
cert_cover_2 6 2 1 4 6 44 172 3
cert_coverFacet 7 436
cert_cover_5 7 3 1 3 4 6 52 436 3
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0083

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0084.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0084

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 283, 147, 771, 229, 837, 465, 570, 842, 690, 620, 676, 312, 488, 432, 19, 131, 259, 515, 69, 133, 517, 145, 273, 193, 321, 769, 26, 266, 522, 562, 146, 642, 770, 100, 164, 548, 580, 644, 56, 280, 104, 296, 552, 328, 584, 176, 304, 400, 224, 416, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_283, vertices_147, vertices_771, vertices_229, vertices_837, vertices_465, vertices_570, vertices_842, vertices_690, vertices_620, vertices_676, vertices_312, vertices_488, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_69, vertices_133, vertices_517, vertices_145, vertices_273, vertices_193, vertices_321, vertices_769, vertices_26, vertices_266, vertices_522, vertices_562, vertices_146, vertices_642, vertices_770, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_56, vertices_280, vertices_104, vertices_296, vertices_552, vertices_328, vertices_584, vertices_176, vertices_304, vertices_400, vertices_224, vertices_416, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_283), (false, vertices_147), (false, vertices_771), (false, vertices_229), (false, vertices_837), (false, vertices_465), (true, vertices_522), (true, vertices_562), (true, vertices_548), (true, vertices_56), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_584), (true, vertices_176), (true, vertices_304), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_283) then 16 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_562) then 17 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_56) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_562), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
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
cert_row_2 0 0 3 4 8 562
cert_row_4 1 0 2 5 7 8 842 266 2
cert_row_4 2 1 2 4 5 8 620 100 1
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 570
cert_cover_5 0 0 0 2 3 4 26 570 3
cert_coverFacet 1 842
cert_cover_5 1 1 0 2 5 7 266 842 2
cert_coverFacet 2 690
cert_cover_5 2 0 0 3 4 6 562 690 3
cert_coverFacet 3 620
cert_cover_5 3 2 1 2 4 5 100 620 1
cert_coverFacet 4 676
cert_cover_2 4 4 1 6 8 164 676 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 104 488 3
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0084

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0085.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0085

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 301, 589, 549, 457, 721, 673, 310, 790, 842, 242, 594, 450, 780, 692, 13, 37, 517, 73, 265, 161, 289, 545, 193, 577, 385, 641, 278, 50, 82, 530, 162, 290, 194, 322, 578, 386, 770, 268, 524, 52, 532, 292, 548, 772, 328, 584, 776, 176, 208, 592, 656, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_301, vertices_589, vertices_549, vertices_457, vertices_721, vertices_673, vertices_310, vertices_790, vertices_842, vertices_242, vertices_594, vertices_450, vertices_780, vertices_692] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_517, vertices_73, vertices_265, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_278, vertices_50, vertices_82, vertices_530, vertices_162, vertices_290, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_268, vertices_524, vertices_52, vertices_532, vertices_292, vertices_548, vertices_772, vertices_328, vertices_584, vertices_776, vertices_176, vertices_208, vertices_592, vertices_656, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_301), (false, vertices_589), (false, vertices_549), (false, vertices_457), (false, vertices_721), (false, vertices_673), (true, vertices_278), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_52), (true, vertices_532), (true, vertices_772), (true, vertices_776), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 15 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_673) then 1 else
  if p.val = (true, vertices_278) then 16 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_176) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 549 1 673 50 82 530 194 322 578 770 52 532 772 776 176 419 278 301 589 457 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 322 1
cert_row_2 1 0 1 3 7 278
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 1 0 1 3 4 278 310 3
cert_coverFacet 1 790
cert_cover_5 1 1 0 1 3 8 278 790 3
cert_coverFacet 2 842
cert_cover_5 2 0 0 2 5 7 322 842 1
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 50 242 3
cert_coverFacet 4 594
cert_cover_2 4 3 0 5 8 82 594 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 692
cert_cover_5 7 3 1 3 4 6 52 692 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0085

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0086.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0086

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 93, 653, 453, 281, 777, 369, 794, 690, 306, 482, 620, 740, 120, 568, 13, 69, 133, 25, 265, 521, 81, 273, 321, 385, 641, 769, 50, 274, 530, 162, 290, 386, 642, 770, 76, 524, 612, 196, 644, 56, 88, 280, 536, 104, 552, 776, 112, 304, 560, 224, 352, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_93, vertices_653, vertices_453, vertices_281, vertices_777, vertices_369, vertices_794, vertices_690, vertices_306, vertices_482, vertices_620, vertices_740, vertices_120, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_133, vertices_25, vertices_265, vertices_521, vertices_81, vertices_273, vertices_321, vertices_385, vertices_641, vertices_769, vertices_50, vertices_274, vertices_530, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_76, vertices_524, vertices_612, vertices_196, vertices_644, vertices_56, vertices_88, vertices_280, vertices_536, vertices_104, vertices_552, vertices_776, vertices_112, vertices_304, vertices_560, vertices_224, vertices_352, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_93), (false, vertices_653), (false, vertices_453), (false, vertices_281), (false, vertices_777), (false, vertices_369), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_612), (true, vertices_56), (true, vertices_536), (true, vertices_104), (true, vertices_552), (true, vertices_560), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 19 16 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_612) then 21 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
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
cert_row_2 0 1 4 5 8 612
cert_row_4 1 0 2 3 7 8 794 274 1
cert_row_4 2 0 3 4 6 8 690 50 3
cert_row_4 3 0 4 5 6 7 482 162 2
cert_rows
cert_pivot_2 1 2 3 0
cert_heightProof 4
cert_coverFacet 0 794
cert_cover_5 0 1 0 2 3 7 274 794 1
cert_coverFacet 1 690
cert_cover_5 1 2 0 3 4 6 50 690 3
cert_coverFacet 2 306
cert_cover_2 2 3 0 4 7 50 306 3
cert_coverFacet 3 482
cert_cover_5 3 3 0 4 5 6 162 482 2
cert_coverFacet 4 620
cert_cover_5 4 0 1 2 4 5 76 620 2
cert_coverFacet 5 740
cert_cover_5 5 0 1 4 5 6 612 740 3
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0086

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0087.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0087

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [59, 539, 709, 681, 241, 849, 398, 170, 778, 370, 786, 418, 844, 652, 484, 27, 41, 521, 49, 81, 529, 161, 193, 577, 641, 42, 138, 266, 522, 50, 274, 530, 162, 290, 386, 770, 140, 268, 524, 196, 324, 580, 388, 644, 168, 648, 776, 112, 336, 784, 224, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_59, vertices_539, vertices_709, vertices_681, vertices_241, vertices_849, vertices_398, vertices_170, vertices_778, vertices_370, vertices_786, vertices_418, vertices_844, vertices_652, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_41, vertices_521, vertices_49, vertices_81, vertices_529, vertices_161, vertices_193, vertices_577, vertices_641, vertices_42, vertices_138, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_162, vertices_290, vertices_386, vertices_770, vertices_140, vertices_268, vertices_524, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_168, vertices_648, vertices_776, vertices_112, vertices_336, vertices_784, vertices_224, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_59), (false, vertices_539), (false, vertices_709), (false, vertices_681), (false, vertices_241), (false, vertices_849), (true, vertices_138), (true, vertices_266), (true, vertices_274), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_324), (true, vertices_388), (true, vertices_776), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_59) then 16 else
  if p.val = (false, vertices_539) then 17 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 7 370 50 3
cert_row_4 1 0 1 2 6 7 398 138 1
cert_row_4 2 1 2 5 7 8 844 268 2
cert_row_4 3 1 4 5 6 7 484 196 1
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 138 398 1
cert_coverFacet 1 170
cert_cover_2 1 2 0 4 6 42 170 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 370
cert_cover_5 3 0 0 3 4 5 50 370 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 844
cert_cover_5 6 2 1 2 5 7 268 844 2
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 484
cert_cover_5 8 3 1 4 5 6 196 484 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0087

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0088.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0088

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 557, 397, 837, 153, 537, 465, 806, 666, 682, 242, 354, 834, 300, 488, 13, 261, 517, 25, 137, 521, 81, 145, 529, 321, 577, 385, 650, 82, 146, 530, 98, 162, 290, 546, 322, 578, 770, 44, 268, 292, 548, 772, 152, 536, 168, 296, 552, 392, 208, 224, 352, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_557, vertices_397, vertices_837, vertices_153, vertices_537, vertices_465, vertices_806, vertices_666, vertices_682, vertices_242, vertices_354, vertices_834, vertices_300, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_261, vertices_517, vertices_25, vertices_137, vertices_521, vertices_81, vertices_145, vertices_529, vertices_321, vertices_577, vertices_385, vertices_650, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_44, vertices_268, vertices_292, vertices_548, vertices_772, vertices_152, vertices_536, vertices_168, vertices_296, vertices_552, vertices_392, vertices_208, vertices_224, vertices_352, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_557), (false, vertices_397), (false, vertices_837), (false, vertices_153), (false, vertices_537), (false, vertices_465), (true, vertices_650), (true, vertices_146), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_770), (true, vertices_292), (true, vertices_168), (true, vertices_296), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_153) then 0 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_650) then 16 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
cert_nodeAtPriority_15 0 153 1 537 146 98 162 290 546 322 770 292 168 296 224 352 595 650 557 397 837 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_2 1 0 2 6 8 650
cert_row_4 2 0 3 4 5 6 242 82 2
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 666
cert_cover_5 1 1 0 2 3 6 650 666 2
cert_coverFacet 2 682
cert_cover_5 2 1 0 2 4 6 650 682 2
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 82 242 2
cert_coverFacet 4 354
cert_cover_2 4 4 0 5 7 98 354 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 168 488 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0088

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2673 : Certifies 2673 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0059.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2674 : Certifies 2674 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0060.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2675 : Certifies 2675 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0061.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2676 : Certifies 2676 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0062.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2677 : Certifies 2677 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0063.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2678 : Certifies 2678 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0064.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2679 : Certifies 2679 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0065.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2680 : Certifies 2680 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0066.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2681 : Certifies 2681 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0067.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2682 : Certifies 2682 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0068.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2683 : Certifies 2683 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0069.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2684 : Certifies 2684 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0070.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2685 : Certifies 2685 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0071.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2686 : Certifies 2686 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0072.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2687 : Certifies 2687 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0073.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2688 : Certifies 2688 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0074.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2689 : Certifies 2689 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0075.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2690 : Certifies 2690 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0076.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2691 : Certifies 2691 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0077.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2692 : Certifies 2692 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0078.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2693 : Certifies 2693 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0079.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2694 : Certifies 2694 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0080.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2695 : Certifies 2695 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0081.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2696 : Certifies 2696 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0082.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2697 : Certifies 2697 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0083.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2698 : Certifies 2698 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0084.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2699 : Certifies 2699 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0085.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2700 : Certifies 2700 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0086.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2701 : Certifies 2701 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0087.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2702 : Certifies 2702 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0088.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B088 (j : Fin 30) :
    Certifies (2673 + j.val) := by
  fin_cases j
  · exact projection_2673
  · exact projection_2674
  · exact projection_2675
  · exact projection_2676
  · exact projection_2677
  · exact projection_2678
  · exact projection_2679
  · exact projection_2680
  · exact projection_2681
  · exact projection_2682
  · exact projection_2683
  · exact projection_2684
  · exact projection_2685
  · exact projection_2686
  · exact projection_2687
  · exact projection_2688
  · exact projection_2689
  · exact projection_2690
  · exact projection_2691
  · exact projection_2692
  · exact projection_2693
  · exact projection_2694
  · exact projection_2695
  · exact projection_2696
  · exact projection_2697
  · exact projection_2698
  · exact projection_2699
  · exact projection_2700
  · exact projection_2701
  · exact projection_2702

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
