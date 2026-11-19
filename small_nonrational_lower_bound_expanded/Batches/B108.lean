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
/- Source: ProjectionCertificates/R_m15e10q1_0679.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0679

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 781, 453, 601, 329, 737, 182, 790, 626, 674, 436, 120, 312, 792, 488, 133, 261, 517, 73, 265, 521, 193, 321, 577, 641, 22, 134, 518, 50, 530, 162, 546, 642, 180, 276, 388, 772, 56, 88, 280, 536, 104, 296, 328, 776, 112, 304, 592, 784, 224, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_781, vertices_453, vertices_601, vertices_329, vertices_737, vertices_182, vertices_790, vertices_626, vertices_674, vertices_436, vertices_120, vertices_312, vertices_792, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_193, vertices_321, vertices_577, vertices_641, vertices_22, vertices_134, vertices_518, vertices_50, vertices_530, vertices_162, vertices_546, vertices_642, vertices_180, vertices_276, vertices_388, vertices_772, vertices_56, vertices_88, vertices_280, vertices_536, vertices_104, vertices_296, vertices_328, vertices_776, vertices_112, vertices_304, vertices_592, vertices_784, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_781), (false, vertices_453), (false, vertices_601), (false, vertices_329), (false, vertices_737), (true, vertices_22), (true, vertices_50), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_180), (true, vertices_276), (true, vertices_56), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_112), (true, vertices_304), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_601) then 22 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_180) then 20 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_180), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 4 5 6 7 488 104 3
cert_row_2 1 1 3 4 6 180
cert_row_4 2 0 1 3 7 8 790 22 3
cert_row_4 3 0 3 4 5 8 626 50 3
cert_rows
cert_pivot_2 2 6 1 0
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 1 0 1 3 4 22 182 3
cert_coverFacet 1 790
cert_cover_5 1 2 0 1 3 7 22 790 3
cert_coverFacet 2 626
cert_cover_5 2 3 0 3 4 5 50 626 3
cert_coverFacet 3 674
cert_cover_2 3 4 0 6 8 162 674 3
cert_coverFacet 4 436
cert_cover_5 4 1 1 3 4 7 180 436 3
cert_coverFacet 5 120
cert_cover_2 5 3 2 4 5 56 120 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coverFacet 8 488
cert_cover_5 8 0 2 4 5 6 104 488 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0679

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0681.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0681

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [115, 275, 707, 387, 405, 617, 689, 902, 842, 338, 124, 348, 812, 180, 676, 19, 67, 131, 259, 49, 145, 273, 97, 545, 577, 385, 641, 82, 274, 322, 578, 386, 642, 770, 92, 44, 268, 52, 148, 276, 164, 548, 388, 644, 772, 104, 552, 328, 584, 776, 112, 176, 336, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_115, vertices_275, vertices_707, vertices_387, vertices_405, vertices_617, vertices_689, vertices_902, vertices_842, vertices_338, vertices_124, vertices_348, vertices_812, vertices_180, vertices_676] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_131, vertices_259, vertices_49, vertices_145, vertices_273, vertices_97, vertices_545, vertices_577, vertices_385, vertices_641, vertices_82, vertices_274, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_92, vertices_44, vertices_268, vertices_52, vertices_148, vertices_276, vertices_164, vertices_548, vertices_388, vertices_644, vertices_772, vertices_104, vertices_552, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_336, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_115), (false, vertices_275), (false, vertices_707), (false, vertices_387), (false, vertices_405), (false, vertices_617), (false, vertices_689), (true, vertices_322), (true, vertices_770), (true, vertices_92), (true, vertices_44), (true, vertices_268), (true, vertices_52), (true, vertices_164), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_328), (true, vertices_776), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_115) then 15 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_92) then 19 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_336) then 13 else
  0
cert_priority
cert_nodeAtPriority_44 275 387 322 770 44 268 52 164 548 644 772 328 776 336 115 707 405 92 617 689
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 5 92
cert_row_4 1 0 1 6 7 8 902 386 1
cert_row_4 2 0 2 5 7 8 842 322 1
cert_row_4 3 1 2 4 7 8 812 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 842
cert_cover_5 1 2 0 2 5 7 322 842 1
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 124
cert_cover_5 3 0 1 2 3 4 92 124 3
cert_coverFacet 4 348
cert_cover_5 4 0 1 2 3 7 92 348 3
cert_coverFacet 5 812
cert_cover_5 5 3 1 2 4 7 44 812 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 676
cert_cover_2 7 4 1 6 8 164 676 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0681

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0682.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0682

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 115, 147, 835, 781, 713, 209, 310, 406, 354, 668, 396, 564, 868, 752, 19, 67, 131, 259, 137, 265, 521, 81, 145, 193, 577, 769, 278, 50, 146, 98, 290, 322, 386, 140, 268, 524, 52, 148, 532, 292, 548, 388, 772, 392, 648, 112, 560, 208, 656, 352, 608, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_115, vertices_147, vertices_835, vertices_781, vertices_713, vertices_209, vertices_310, vertices_406, vertices_354, vertices_668, vertices_396, vertices_564, vertices_868, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_131, vertices_259, vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_193, vertices_577, vertices_769, vertices_278, vertices_50, vertices_146, vertices_98, vertices_290, vertices_322, vertices_386, vertices_140, vertices_268, vertices_524, vertices_52, vertices_148, vertices_532, vertices_292, vertices_548, vertices_388, vertices_772, vertices_392, vertices_648, vertices_112, vertices_560, vertices_208, vertices_656, vertices_352, vertices_608, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_115), (false, vertices_147), (false, vertices_835), (false, vertices_781), (false, vertices_713), (false, vertices_209), (true, vertices_278), (true, vertices_290), (true, vertices_140), (true, vertices_52), (true, vertices_148), (true, vertices_532), (true, vertices_292), (true, vertices_548), (true, vertices_388), (true, vertices_560), (true, vertices_656), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_115) then 19 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_835) then 20 else
  if p.val = (false, vertices_781) then 15 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_209) then 1 else
  if p.val = (true, vertices_278) then 16 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 1 147 0 209 290 140 52 148 532 292 548 388 560 656 352 608 781 278 395 115 835 713
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 7 278
cert_row_4 1 1 2 3 6 8 668 140 2
cert_row_4 2 1 4 5 7 8 868 292 2
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 278 310 3
cert_coverFacet 1 406
cert_cover_5 1 0 0 1 3 6 278 406 3
cert_coverFacet 2 354
cert_cover_2 2 4 0 5 7 98 354 3
cert_coverFacet 3 668
cert_cover_5 3 1 1 2 3 6 140 668 2
cert_coverFacet 4 396
cert_cover_2 4 2 1 6 7 140 396 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 868
cert_cover_5 6 2 1 4 5 7 292 868 2
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0682

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0683.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0683

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 267, 787, 611, 285, 153, 721, 806, 330, 354, 668, 428, 788, 740, 488, 11, 67, 259, 515, 25, 137, 265, 145, 273, 529, 193, 577, 74, 266, 98, 290, 546, 322, 770, 28, 140, 268, 276, 532, 164, 292, 548, 644, 772, 152, 424, 200, 328, 656, 784, 224, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_267, vertices_787, vertices_611, vertices_285, vertices_153, vertices_721, vertices_806, vertices_330, vertices_354, vertices_668, vertices_428, vertices_788, vertices_740, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_259, vertices_515, vertices_25, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_74, vertices_266, vertices_98, vertices_290, vertices_546, vertices_322, vertices_770, vertices_28, vertices_140, vertices_268, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_152, vertices_424, vertices_200, vertices_328, vertices_656, vertices_784, vertices_224, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_267), (false, vertices_787), (false, vertices_611), (false, vertices_285), (false, vertices_153), (false, vertices_721), (true, vertices_290), (true, vertices_322), (true, vertices_140), (true, vertices_532), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_424), (true, vertices_328), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_285) then 19 else
  if p.val = (false, vertices_153) then 1 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_424) then 21 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_153), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_424), by decide +kernel⟩
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
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_2 1 2 4 6 7 424
cert_row_4 2 1 2 3 6 8 668 28 3
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 0 7 2 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 330
cert_cover_2 1 2 0 5 7 74 330 3
cert_coverFacet 2 354
cert_cover_2 2 4 0 5 7 98 354 3
cert_coverFacet 3 668
cert_cover_5 3 2 1 2 3 6 28 668 3
cert_coverFacet 4 428
cert_cover_5 4 1 1 2 4 6 140 428 2
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 164 740 2
cert_coverFacet 7 488
cert_cover_5 7 1 2 4 5 6 424 488 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0683

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0684.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0684

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 285, 557, 53, 177, 913, 737, 78, 526, 614, 218, 410, 962, 92, 244, 13, 21, 37, 265, 521, 49, 145, 273, 161, 545, 641, 769, 14, 70, 518, 154, 74, 266, 522, 194, 578, 386, 770, 28, 76, 524, 52, 84, 100, 548, 88, 280, 176, 208, 400, 224, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_285, vertices_557, vertices_53, vertices_177, vertices_913, vertices_737, vertices_78, vertices_526, vertices_614, vertices_218, vertices_410, vertices_962, vertices_92, vertices_244] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_37, vertices_265, vertices_521, vertices_49, vertices_145, vertices_273, vertices_161, vertices_545, vertices_641, vertices_769, vertices_14, vertices_70, vertices_518, vertices_154, vertices_74, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_770, vertices_28, vertices_76, vertices_524, vertices_52, vertices_84, vertices_100, vertices_548, vertices_88, vertices_280, vertices_176, vertices_208, vertices_400, vertices_224, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_285), (false, vertices_557), (false, vertices_53), (false, vertices_177), (false, vertices_913), (false, vertices_737), (true, vertices_14), (true, vertices_70), (true, vertices_518), (true, vertices_154), (true, vertices_74), (true, vertices_194), (true, vertices_578), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_100), (true, vertices_88), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_53) then 0 else
  if p.val = (false, vertices_177) then 1 else
  if p.val = (false, vertices_913) then 22 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_70) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_154) then 16 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_208) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_53), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 0 1 4 5 8 614 70 2
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 614
cert_cover_5 2 2 0 1 4 5 70 614 2
cert_coverFacet 3 218
cert_cover_5 3 0 0 2 3 5 154 218 3
cert_coverFacet 4 410
cert_cover_5 4 0 0 2 3 7 154 410 3
cert_coverFacet 5 962
cert_cover_5 5 1 0 5 6 7 194 962 3
cert_coverFacet 6 92
cert_cover_2 6 2 1 3 5 28 92 3
cert_coverFacet 7 244
cert_cover_5 7 3 1 3 4 5 52 244 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0684

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0686.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0686

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [79, 271, 595, 803, 341, 913, 682, 298, 586, 236, 300, 212, 404, 932, 728, 15, 67, 259, 515, 69, 261, 81, 273, 529, 769, 42, 74, 266, 522, 290, 546, 578, 44, 76, 268, 84, 148, 276, 164, 292, 196, 388, 168, 296, 200, 584, 648, 208, 592, 400, 656, 672, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_79, vertices_271, vertices_595, vertices_803, vertices_341, vertices_913, vertices_682, vertices_298, vertices_586, vertices_236, vertices_300, vertices_212, vertices_404, vertices_932, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_15, vertices_67, vertices_259, vertices_515, vertices_69, vertices_261, vertices_81, vertices_273, vertices_529, vertices_769, vertices_42, vertices_74, vertices_266, vertices_522, vertices_290, vertices_546, vertices_578, vertices_44, vertices_76, vertices_268, vertices_84, vertices_148, vertices_276, vertices_164, vertices_292, vertices_196, vertices_388, vertices_168, vertices_296, vertices_200, vertices_584, vertices_648, vertices_208, vertices_592, vertices_400, vertices_656, vertices_672, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_79), (false, vertices_271), (false, vertices_595), (false, vertices_803), (false, vertices_341), (false, vertices_913), (true, vertices_42), (true, vertices_522), (true, vertices_44), (true, vertices_148), (true, vertices_164), (true, vertices_292), (true, vertices_196), (true, vertices_388), (true, vertices_168), (true, vertices_296), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_208), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 15 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_79) then 16 else
  if p.val = (false, vertices_271) then 17 else
  if p.val = (false, vertices_595) then 20 else
  if p.val = (false, vertices_803) then 21 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_913) then 24 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_79), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 42 3
cert_row_4 1 1 4 6 7 8 932 164 3
cert_row_4 2 1 2 4 5 6 236 44 3
cert_row_4 3 2 3 5 6 8 728 200 1
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 682
cert_cover_5 0 0 0 2 4 6 42 682 3
cert_coverFacet 1 298
cert_cover_2 1 2 0 4 7 42 298 3
cert_coverFacet 2 586
cert_cover_2 2 2 0 5 8 74 586 3
cert_coverFacet 3 236
cert_cover_5 3 2 1 2 4 5 44 236 3
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 212
cert_cover_2 5 3 1 5 6 84 212 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 932
cert_cover_5 7 1 1 4 6 7 164 932 3
cert_coverFacet 8 728
cert_cover_5 8 3 2 3 5 6 200 728 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0686

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0687.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0687

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 661, 229, 837, 793, 433, 174, 558, 410, 842, 610, 418, 652, 612, 664, 69, 133, 517, 145, 273, 529, 97, 161, 289, 321, 769, 46, 138, 266, 522, 98, 162, 290, 546, 322, 578, 386, 140, 524, 100, 164, 548, 580, 644, 152, 280, 536, 648, 776, 400, 656, 608, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_661, vertices_229, vertices_837, vertices_793, vertices_433, vertices_174, vertices_558, vertices_410, vertices_842, vertices_610, vertices_418, vertices_652, vertices_612, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_321, vertices_769, vertices_46, vertices_138, vertices_266, vertices_522, vertices_98, vertices_162, vertices_290, vertices_546, vertices_322, vertices_578, vertices_386, vertices_140, vertices_524, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_152, vertices_280, vertices_536, vertices_648, vertices_776, vertices_400, vertices_656, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_661), (false, vertices_229), (false, vertices_837), (false, vertices_793), (false, vertices_433), (true, vertices_46), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_162), (true, vertices_546), (true, vertices_578), (true, vertices_386), (true, vertices_140), (true, vertices_524), (true, vertices_548), (true, vertices_152), (true, vertices_648), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 14 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (true, vertices_46) then 15 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
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
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 2 3 6 7 410 138 2
cert_row_4 2 0 2 5 7 8 842 266 2
cert_rows_3
cert_pivot_3 3 1 0
cert_heightProof 3
cert_coverFacet 0 174
cert_cover_5 0 0 0 1 2 6 46 174 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 8 46 558 3
cert_coverFacet 2 410
cert_cover_5 2 1 0 2 3 6 138 410 2
cert_coverFacet 3 842
cert_cover_5 3 2 0 2 5 7 266 842 2
cert_coverFacet 4 610
cert_cover_2 4 4 0 5 8 98 610 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 612
cert_cover_2 7 4 1 5 8 100 612 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 3 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0687

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0688.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0688

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 557, 205, 117, 569, 393, 465, 654, 538, 394, 818, 962, 868, 708, 368, 13, 37, 69, 25, 553, 137, 265, 49, 81, 273, 193, 385, 26, 138, 266, 522, 274, 530, 386, 642, 770, 140, 524, 100, 548, 196, 580, 644, 536, 392, 112, 304, 560, 336, 352, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_557, vertices_205, vertices_117, vertices_569, vertices_393, vertices_465, vertices_654, vertices_538, vertices_394, vertices_818, vertices_962, vertices_868, vertices_708, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_25, vertices_553, vertices_137, vertices_265, vertices_49, vertices_81, vertices_273, vertices_193, vertices_385, vertices_26, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_140, vertices_524, vertices_100, vertices_548, vertices_196, vertices_580, vertices_644, vertices_536, vertices_392, vertices_112, vertices_304, vertices_560, vertices_336, vertices_352, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_557), (false, vertices_205), (false, vertices_117), (false, vertices_569), (false, vertices_393), (false, vertices_465), (true, vertices_138), (true, vertices_522), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_580), (true, vertices_644), (true, vertices_304), (true, vertices_352), (true, vertices_800), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 15 else
  if p.val = (false, vertices_557) then 20 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_117) then 18 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_704) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
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
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_4 1 0 3 4 7 8 818 274 2
cert_row_4 2 0 5 6 7 8 962 386 1
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 818
cert_cover_5 3 1 0 3 4 7 274 818 2
cert_coverFacet 4 962
cert_cover_5 4 2 0 5 6 7 386 962 1
cert_coverFacet 5 868
cert_cover_5 5 3 1 4 5 7 100 868 3
cert_coverFacet 6 708
cert_cover_2 6 5 1 6 8 196 708 3
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0688

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0689.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0689

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 179, 275, 707, 233, 113, 849, 654, 150, 278, 428, 844, 436, 376, 712, 19, 131, 259, 515, 49, 81, 273, 97, 161, 193, 577, 769, 22, 134, 262, 518, 146, 274, 642, 140, 268, 524, 148, 276, 420, 772, 104, 168, 296, 200, 328, 584, 648, 112, 176, 304, 336, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_179, vertices_275, vertices_707, vertices_233, vertices_113, vertices_849, vertices_654, vertices_150, vertices_278, vertices_428, vertices_844, vertices_436, vertices_376, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_49, vertices_81, vertices_273, vertices_97, vertices_161, vertices_193, vertices_577, vertices_769, vertices_22, vertices_134, vertices_262, vertices_518, vertices_146, vertices_274, vertices_642, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_420, vertices_772, vertices_104, vertices_168, vertices_296, vertices_200, vertices_328, vertices_584, vertices_648, vertices_112, vertices_176, vertices_304, vertices_336, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_179), (false, vertices_275), (false, vertices_707), (false, vertices_233), (false, vertices_113), (false, vertices_849), (true, vertices_22), (true, vertices_134), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_420), (true, vertices_296), (true, vertices_328), (true, vertices_584), (true, vertices_648), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_179) then 16 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_113) then 1 else
  if p.val = (false, vertices_849) then 23 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_420) then 19 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_304) then 13 else
  0
cert_priority
cert_nodeAtPriority_47 275 113 22 134 140 268 524 148 276 296 328 584 648 304 775 179 707 420 233 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 134 2
cert_row_2 1 1 4 6 7 420
cert_row_4 2 1 2 5 7 8 844 268 2
cert_row_4 3 2 3 4 5 7 376 104 1
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 134 654 2
cert_coverFacet 1 150
cert_cover_2 1 1 0 3 6 22 150 3
cert_coverFacet 2 278
cert_cover_2 2 1 0 3 7 22 278 3
cert_coverFacet 3 428
cert_cover_5 3 1 1 2 4 6 140 428 2
cert_coverFacet 4 844
cert_cover_5 4 2 1 2 5 7 268 844 2
cert_coverFacet 5 436
cert_cover_5 5 1 1 3 4 6 148 436 2
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 104 376 1
cert_coverFacet 7 712
cert_cover_2 7 5 2 6 8 200 712 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0689

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0690.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0690

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 227, 579, 387, 589, 357, 433, 714, 914, 668, 284, 332, 788, 248, 376, 67, 131, 259, 515, 69, 261, 517, 97, 161, 289, 577, 385, 194, 578, 386, 642, 770, 28, 76, 268, 524, 276, 532, 324, 772, 120, 152, 280, 200, 328, 584, 648, 176, 304, 400, 656, 784, 224, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_227, vertices_579, vertices_387, vertices_589, vertices_357, vertices_433, vertices_714, vertices_914, vertices_668, vertices_284, vertices_332, vertices_788, vertices_248, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_69, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_268, vertices_524, vertices_276, vertices_532, vertices_324, vertices_772, vertices_120, vertices_152, vertices_280, vertices_200, vertices_328, vertices_584, vertices_648, vertices_176, vertices_304, vertices_400, vertices_656, vertices_784, vertices_224, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_227), (false, vertices_579), (false, vertices_387), (false, vertices_589), (false, vertices_357), (false, vertices_433), (true, vertices_642), (true, vertices_28), (true, vertices_268), (true, vertices_276), (true, vertices_532), (true, vertices_120), (true, vertices_152), (true, vertices_280), (true, vertices_200), (true, vertices_328), (true, vertices_648), (true, vertices_656), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_227) then 16 else
  if p.val = (false, vertices_579) then 0 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_120) then 21 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_784) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_579), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_120), by decide +kernel⟩
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
cert_row_2 0 2 3 4 5 120
cert_row_4 1 0 2 5 6 8 714 194 1
cert_row_4 2 0 3 6 7 8 914 386 1
cert_row_4 3 1 2 3 6 8 668 28 3
cert_rows
cert_pivot_2 4 5 0 1
cert_heightProof 4
cert_coverFacet 0 714
cert_cover_5 0 1 0 2 5 6 194 714 1
cert_coverFacet 1 914
cert_cover_5 1 2 0 3 6 7 386 914 1
cert_coverFacet 2 668
cert_cover_5 2 3 1 2 3 6 28 668 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 332
cert_cover_2 4 2 1 5 7 76 332 3
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 248
cert_cover_5 6 0 2 3 4 6 120 248 3
cert_coverFacet 7 376
cert_cover_5 7 0 2 3 4 7 120 376 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0690

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0691.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0691

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 781, 569, 153, 433, 865, 206, 270, 838, 242, 354, 418, 220, 540, 628, 25, 137, 265, 521, 49, 145, 289, 545, 385, 769, 14, 70, 262, 138, 266, 98, 162, 290, 194, 322, 386, 28, 204, 268, 524, 84, 532, 580, 772, 152, 536, 112, 176, 560, 208, 352, 608, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_781, vertices_569, vertices_153, vertices_433, vertices_865, vertices_206, vertices_270, vertices_838, vertices_242, vertices_354, vertices_418, vertices_220, vertices_540, vertices_628] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_289, vertices_545, vertices_385, vertices_769, vertices_14, vertices_70, vertices_262, vertices_138, vertices_266, vertices_98, vertices_162, vertices_290, vertices_194, vertices_322, vertices_386, vertices_28, vertices_204, vertices_268, vertices_524, vertices_84, vertices_532, vertices_580, vertices_772, vertices_152, vertices_536, vertices_112, vertices_176, vertices_560, vertices_208, vertices_352, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_781), (false, vertices_569), (false, vertices_153), (false, vertices_433), (false, vertices_865), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_194), (true, vertices_322), (true, vertices_28), (true, vertices_204), (true, vertices_84), (true, vertices_532), (true, vertices_580), (true, vertices_112), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_153) then 0 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_204) then 19 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_580) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_208) then 14 else
  0
cert_priority
cert_nodeAtPriority_9 0 153 1 14 70 262 98 162 290 194 322 28 84 532 580 112 208 395 781 204 569 433 865
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 6 204
cert_row_4 1 0 1 5 7 8 838 70 3
cert_row_4 2 0 3 4 5 6 242 98 1
cert_row_4 3 1 3 4 5 8 628 84 2
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 838
cert_cover_5 2 1 0 1 5 7 70 838 3
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 98 242 1
cert_coverFacet 4 354
cert_cover_2 4 4 0 5 7 98 354 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 220
cert_cover_5 6 0 1 2 3 5 28 220 3
cert_coverFacet 7 540
cert_cover_2 7 2 1 3 8 28 540 3
cert_coverFacet 8 628
cert_cover_5 8 3 1 3 4 5 84 628 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0691

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0692.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0692

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 213, 533, 901, 457, 369, 654, 570, 362, 394, 306, 898, 620, 204, 628, 21, 133, 517, 81, 273, 529, 193, 321, 385, 769, 42, 138, 266, 522, 50, 274, 530, 290, 386, 642, 770, 76, 140, 524, 84, 532, 612, 196, 644, 104, 552, 200, 328, 392, 112, 304, 560, 352, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_213, vertices_533, vertices_901, vertices_457, vertices_369, vertices_654, vertices_570, vertices_362, vertices_394, vertices_306, vertices_898, vertices_620, vertices_204, vertices_628] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_81, vertices_273, vertices_529, vertices_193, vertices_321, vertices_385, vertices_769, vertices_42, vertices_138, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_290, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_84, vertices_532, vertices_612, vertices_196, vertices_644, vertices_104, vertices_552, vertices_200, vertices_328, vertices_392, vertices_112, vertices_304, vertices_560, vertices_352, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_213), (false, vertices_533), (false, vertices_901), (false, vertices_457), (false, vertices_369), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_290), (true, vertices_386), (true, vertices_642), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_612), (true, vertices_104), (true, vertices_552), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_612) then 20 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_560) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
cert_row_2 1 1 4 5 8 612
cert_row_4 2 0 2 3 4 8 570 42 2
cert_row_4 3 0 2 4 5 7 362 42 3
cert_rows
cert_pivot_2 6 1 3 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 570
cert_cover_5 1 2 0 2 3 4 42 570 2
cert_coverFacet 2 362
cert_cover_5 2 3 0 2 4 5 42 362 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 620
cert_cover_5 6 1 1 2 4 5 76 620 2
cert_coverFacet 7 204
cert_cover_2 7 2 1 5 6 76 204 3
cert_coverFacet 8 628
cert_cover_5 8 1 1 3 4 5 84 628 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0692

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0693.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0693

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 781, 569, 425, 177, 849, 206, 270, 838, 394, 242, 338, 236, 556, 628, 41, 265, 521, 49, 145, 273, 529, 161, 385, 769, 14, 70, 262, 138, 266, 82, 146, 274, 194, 322, 386, 44, 204, 268, 524, 100, 548, 580, 772, 168, 552, 392, 112, 176, 560, 336, 592, 224, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_781, vertices_569, vertices_425, vertices_177, vertices_849, vertices_206, vertices_270, vertices_838, vertices_394, vertices_242, vertices_338, vertices_236, vertices_556, vertices_628] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_265, vertices_521, vertices_49, vertices_145, vertices_273, vertices_529, vertices_161, vertices_385, vertices_769, vertices_14, vertices_70, vertices_262, vertices_138, vertices_266, vertices_82, vertices_146, vertices_274, vertices_194, vertices_322, vertices_386, vertices_44, vertices_204, vertices_268, vertices_524, vertices_100, vertices_548, vertices_580, vertices_772, vertices_168, vertices_552, vertices_392, vertices_112, vertices_176, vertices_560, vertices_336, vertices_592, vertices_224, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_781), (false, vertices_569), (false, vertices_425), (false, vertices_177), (false, vertices_849), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_138), (true, vertices_266), (true, vertices_82), (true, vertices_194), (true, vertices_322), (true, vertices_44), (true, vertices_204), (true, vertices_100), (true, vertices_548), (true, vertices_580), (true, vertices_112), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_82) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_204) then 19 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_580) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 177 2 14 1 70 3 262 138 266 82 194 322 44 100 548 580 112 224 403 781 204 569 425 849
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 6 204
cert_row_4 1 0 1 5 7 8 838 70 3
cert_row_4 2 0 3 4 5 6 242 82 2
cert_row_4 3 1 3 4 5 8 628 100 1
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 838
cert_cover_5 2 1 0 1 5 7 70 838 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 242
cert_cover_5 4 2 0 3 4 5 82 242 2
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 236
cert_cover_5 6 0 1 2 4 5 44 236 3
cert_coverFacet 7 556
cert_cover_2 7 2 1 4 8 44 556 3
cert_coverFacet 8 628
cert_cover_5 8 3 1 3 4 5 100 628 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0693

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0694.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0694

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 229, 805, 645, 457, 369, 654, 570, 346, 394, 306, 802, 604, 204, 628, 37, 133, 517, 97, 289, 193, 321, 385, 641, 769, 26, 138, 266, 522, 50, 274, 290, 546, 386, 642, 770, 76, 140, 524, 596, 100, 548, 196, 644, 88, 536, 200, 328, 392, 112, 304, 560, 336, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_229, vertices_805, vertices_645, vertices_457, vertices_369, vertices_654, vertices_570, vertices_346, vertices_394, vertices_306, vertices_802, vertices_604, vertices_204, vertices_628] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_97, vertices_289, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_50, vertices_274, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_596, vertices_100, vertices_548, vertices_196, vertices_644, vertices_88, vertices_536, vertices_200, vertices_328, vertices_392, vertices_112, vertices_304, vertices_560, vertices_336, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_229), (false, vertices_805), (false, vertices_645), (false, vertices_457), (false, vertices_369), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_290), (true, vertices_546), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_596), (true, vertices_88), (true, vertices_536), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_596) then 20 else
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
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
cert_row_2 1 1 3 5 8 596
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 0 2 3 5 7 346 26 3
cert_rows
cert_pivot_2 6 1 4 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 570
cert_cover_5 1 2 0 2 3 4 26 570 3
cert_coverFacet 2 346
cert_cover_5 2 3 0 2 3 5 26 346 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 604
cert_cover_5 6 1 1 2 3 5 76 604 2
cert_coverFacet 7 204
cert_cover_2 7 2 1 5 6 76 204 3
cert_coverFacet 8 628
cert_cover_5 8 1 1 3 4 5 596 628 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0694

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0695.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0695

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 789, 357, 549, 569, 217, 233, 902, 666, 210, 786, 482, 428, 556, 652, 37, 261, 517, 25, 41, 201, 81, 273, 529, 97, 545, 321, 82, 146, 274, 530, 194, 322, 386, 642, 770, 44, 140, 524, 292, 548, 388, 644, 772, 152, 536, 168, 552, 648, 208, 784, 224, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_789, vertices_357, vertices_549, vertices_569, vertices_217, vertices_233, vertices_902, vertices_666, vertices_210, vertices_786, vertices_482, vertices_428, vertices_556, vertices_652] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_25, vertices_41, vertices_201, vertices_81, vertices_273, vertices_529, vertices_97, vertices_545, vertices_321, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_524, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_152, vertices_536, vertices_168, vertices_552, vertices_648, vertices_208, vertices_784, vertices_224, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_789), (false, vertices_357), (false, vertices_549), (false, vertices_569), (false, vertices_217), (false, vertices_233), (true, vertices_146), (true, vertices_530), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_388), (true, vertices_644), (true, vertices_648), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 15 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_357) then 18 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_569) then 20 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
cert_nodeAtPriority_48 0 549 2 146 1 530 194 386 642 770 44 140 524 388 644 648 416 339 789 357 569 217 233
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 146 1
cert_row_4 1 0 1 6 7 8 902 386 1
cert_row_4 2 0 4 5 6 7 482 194 1
cert_row_4 3 1 2 4 6 7 428 44 3
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 666
cert_cover_5 1 0 0 2 3 6 146 666 1
cert_coverFacet 2 210
cert_cover_2 2 3 0 5 6 82 210 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 482
cert_cover_5 4 2 0 4 5 6 194 482 1
cert_coverFacet 5 428
cert_cover_5 5 3 1 2 4 6 44 428 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0695

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0696.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0696

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 789, 613, 421, 345, 361, 902, 154, 794, 394, 210, 738, 676, 248, 424, 37, 261, 517, 329, 81, 273, 529, 97, 289, 577, 26, 138, 266, 82, 146, 530, 194, 578, 386, 642, 770, 164, 548, 388, 644, 772, 88, 152, 280, 104, 168, 296, 392, 208, 784, 224, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_789, vertices_613, vertices_421, vertices_345, vertices_361, vertices_902, vertices_154, vertices_794, vertices_394, vertices_210, vertices_738, vertices_676, vertices_248, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_329, vertices_81, vertices_273, vertices_529, vertices_97, vertices_289, vertices_577, vertices_26, vertices_138, vertices_266, vertices_82, vertices_146, vertices_530, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_164, vertices_548, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_392, vertices_208, vertices_784, vertices_224, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_789), (false, vertices_613), (false, vertices_421), (false, vertices_345), (false, vertices_361), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_644), (true, vertices_152), (true, vertices_168), (true, vertices_392), (true, vertices_208), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 16 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 26 1 138 2 266 146 194 386 642 770 644 152 168 392 208 224 672 595 789 613 421 345 361
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_4 1 0 2 3 7 8 794 26 3
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 2 3 4 5 6 248 88 2
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 794
cert_cover_5 2 1 0 2 3 7 26 794 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 194 738 1
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 248
cert_cover_5 7 3 2 3 4 5 88 248 2
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0696

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0697.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0697

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 333, 181, 613, 389, 121, 281, 454, 710, 794, 690, 834, 676, 568, 872, 37, 69, 133, 261, 25, 73, 265, 49, 145, 273, 97, 385, 198, 146, 274, 530, 322, 578, 386, 642, 770, 164, 548, 324, 580, 388, 644, 56, 280, 536, 104, 552, 328, 776, 176, 560, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_333, vertices_181, vertices_613, vertices_389, vertices_121, vertices_281, vertices_454, vertices_710, vertices_794, vertices_690, vertices_834, vertices_676, vertices_568, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_133, vertices_261, vertices_25, vertices_73, vertices_265, vertices_49, vertices_145, vertices_273, vertices_97, vertices_385, vertices_198, vertices_146, vertices_274, vertices_530, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_164, vertices_548, vertices_324, vertices_580, vertices_388, vertices_644, vertices_56, vertices_280, vertices_536, vertices_104, vertices_552, vertices_328, vertices_776, vertices_176, vertices_560, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_333), (false, vertices_181), (false, vertices_613), (false, vertices_389), (false, vertices_121), (false, vertices_281), (true, vertices_198), (true, vertices_530), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_644), (true, vertices_536), (true, vertices_552), (true, vertices_776), (true, vertices_560), (true, vertices_672), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 15 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_121) then 22 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (true, vertices_198) then 16 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 389 1 281 530 322 578 642 770 644 536 552 776 560 672 832 403 198 333 181 613 121
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_4 1 0 3 4 6 8 690 146 2
cert_row_4 2 0 2 3 7 8 794 274 1
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 0 0 1 5 7 198 454 3
cert_coverFacet 1 710
cert_cover_5 1 0 0 1 5 8 198 710 3
cert_coverFacet 2 794
cert_cover_5 2 2 0 2 3 7 274 794 1
cert_coverFacet 3 690
cert_cover_5 3 1 0 3 4 6 146 690 2
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 676
cert_cover_2 5 4 1 6 8 164 676 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 872
cert_cover_5 7 3 2 4 5 7 104 872 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0697

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0698.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0698

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 141, 781, 613, 165, 185, 361, 902, 218, 458, 626, 658, 396, 692, 120, 13, 37, 133, 517, 41, 137, 265, 97, 161, 321, 577, 769, 202, 82, 146, 530, 322, 578, 386, 642, 770, 140, 268, 164, 548, 388, 644, 772, 56, 88, 152, 104, 328, 392, 112, 176, 560, 656, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_141, vertices_781, vertices_613, vertices_165, vertices_185, vertices_361, vertices_902, vertices_218, vertices_458, vertices_626, vertices_658, vertices_396, vertices_692, vertices_120] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_133, vertices_517, vertices_41, vertices_137, vertices_265, vertices_97, vertices_161, vertices_321, vertices_577, vertices_769, vertices_202, vertices_82, vertices_146, vertices_530, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_140, vertices_268, vertices_164, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_104, vertices_328, vertices_392, vertices_112, vertices_176, vertices_560, vertices_656, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_141), (false, vertices_781), (false, vertices_613), (false, vertices_165), (false, vertices_185), (false, vertices_361), (true, vertices_202), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_388), (true, vertices_644), (true, vertices_88), (true, vertices_392), (true, vertices_112), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 15 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_165) then 1 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (true, vertices_202) then 16 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_656) then 13 else
  0
cert_priority
cert_nodeAtPriority_25 0 141 1 165 82 146 530 386 642 388 644 88 392 112 560 656 835 202 781 613 185 361
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_4 1 0 1 6 7 8 902 386 1
cert_row_4 2 0 3 4 5 8 626 82 2
cert_row_4 3 1 3 4 6 8 692 164 1
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 5 202 218 2
cert_coverFacet 2 458
cert_cover_5 2 0 0 2 5 7 202 458 3
cert_coverFacet 3 626
cert_cover_5 3 2 0 3 4 5 82 626 2
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 164 692 1
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0698

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0699.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0699

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 781, 421, 549, 569, 153, 241, 838, 218, 602, 778, 482, 372, 564, 596, 37, 261, 517, 25, 137, 265, 521, 49, 145, 161, 545, 385, 90, 138, 266, 522, 194, 322, 578, 386, 770, 52, 84, 532, 292, 548, 324, 580, 772, 152, 536, 776, 112, 560, 208, 592, 224, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_781, vertices_421, vertices_549, vertices_569, vertices_153, vertices_241, vertices_838, vertices_218, vertices_602, vertices_778, vertices_482, vertices_372, vertices_564, vertices_596] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_25, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_161, vertices_545, vertices_385, vertices_90, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_52, vertices_84, vertices_532, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_152, vertices_536, vertices_776, vertices_112, vertices_560, vertices_208, vertices_592, vertices_224, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_781), (false, vertices_421), (false, vertices_549), (false, vertices_569), (false, vertices_153), (false, vertices_241), (true, vertices_90), (true, vertices_522), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_52), (true, vertices_84), (true, vertices_532), (true, vertices_324), (true, vertices_580), (true, vertices_592), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_153) then 1 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_90) then 16 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 549 1 153 522 194 322 578 770 52 84 532 324 580 592 352 395 90 781 421 569 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 4 5 6 7 482 194 1
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 6 90 218 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 8 90 602 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 482
cert_cover_5 4 2 0 4 5 6 194 482 1
cert_coverFacet 5 372
cert_cover_5 5 3 1 3 4 5 52 372 3
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0699

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0700.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0700

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 565, 149, 709, 617, 169, 457, 214, 342, 426, 306, 450, 844, 788, 824, 21, 133, 517, 41, 73, 137, 49, 145, 161, 545, 193, 577, 86, 50, 146, 274, 162, 290, 194, 322, 386, 148, 276, 532, 196, 324, 580, 772, 168, 296, 552, 328, 584, 392, 776, 304, 560, 784, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_565, vertices_149, vertices_709, vertices_617, vertices_169, vertices_457, vertices_214, vertices_342, vertices_426, vertices_306, vertices_450, vertices_844, vertices_788, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_41, vertices_73, vertices_137, vertices_49, vertices_145, vertices_161, vertices_545, vertices_193, vertices_577, vertices_86, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_194, vertices_322, vertices_386, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_580, vertices_772, vertices_168, vertices_296, vertices_552, vertices_328, vertices_584, vertices_392, vertices_776, vertices_304, vertices_560, vertices_784, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_565), (false, vertices_149), (false, vertices_709), (false, vertices_617), (false, vertices_169), (false, vertices_457), (true, vertices_86), (true, vertices_274), (true, vertices_290), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_276), (true, vertices_324), (true, vertices_772), (true, vertices_296), (true, vertices_776), (true, vertices_304), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 15 else
  if p.val = (false, vertices_565) then 18 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_169) then 1 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (true, vertices_86) then 16 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_784) then 13 else
  0
cert_priority
cert_nodeAtPriority_25 0 149 1 169 274 290 194 322 386 276 324 772 296 776 304 784 179 86 565 709 617 457
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 162 1
cert_row_2 1 0 1 3 5 86
cert_row_4 2 1 2 5 7 8 844 324 1
cert_row_4 3 2 3 4 7 8 824 296 1
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 1 0 1 3 6 86 214 3
cert_coverFacet 1 342
cert_cover_5 1 1 0 1 3 7 86 342 3
cert_coverFacet 2 426
cert_cover_5 2 0 0 2 4 6 162 426 1
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 450
cert_cover_2 4 5 0 6 7 194 450 3
cert_coverFacet 5 844
cert_cover_5 5 2 1 2 5 7 324 844 1
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 824
cert_cover_5 7 3 2 3 4 7 296 824 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0700

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0701.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0701

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 781, 57, 665, 433, 961, 110, 270, 598, 774, 482, 834, 124, 540, 752, 25, 41, 265, 521, 49, 145, 289, 385, 641, 769, 14, 70, 262, 518, 42, 266, 98, 290, 322, 578, 770, 28, 108, 268, 524, 84, 532, 772, 56, 536, 112, 176, 592, 656, 224, 416, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_781, vertices_57, vertices_665, vertices_433, vertices_961, vertices_110, vertices_270, vertices_598, vertices_774, vertices_482, vertices_834, vertices_124, vertices_540, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_521, vertices_49, vertices_145, vertices_289, vertices_385, vertices_641, vertices_769, vertices_14, vertices_70, vertices_262, vertices_518, vertices_42, vertices_266, vertices_98, vertices_290, vertices_322, vertices_578, vertices_770, vertices_28, vertices_108, vertices_268, vertices_524, vertices_84, vertices_532, vertices_772, vertices_56, vertices_536, vertices_112, vertices_176, vertices_592, vertices_656, vertices_224, vertices_416, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_781), (false, vertices_57), (false, vertices_665), (false, vertices_433), (false, vertices_961), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_28), (true, vertices_108), (true, vertices_84), (true, vertices_532), (true, vertices_112), (true, vertices_592), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 25 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_961) then 26 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_108) then 19 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_57), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
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
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 1 3 5 8 598 70 2
cert_row_4 2 0 4 5 6 7 482 98 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 598
cert_cover_5 2 1 0 1 3 5 70 598 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 482
cert_cover_5 4 2 0 4 5 6 98 482 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 124
cert_cover_5 6 0 1 2 3 4 28 124 3
cert_coverFacet 7 540
cert_cover_2 7 2 1 3 8 28 540 3
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 112 752 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0701

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0703.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0703

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 595, 147, 589, 405, 325, 369, 682, 818, 402, 418, 236, 652, 484, 632, 19, 131, 515, 69, 133, 261, 517, 81, 145, 273, 321, 577, 146, 274, 530, 162, 290, 546, 386, 642, 76, 140, 524, 228, 324, 388, 644, 104, 168, 552, 584, 648, 112, 304, 560, 592, 400, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_595, vertices_147, vertices_589, vertices_405, vertices_325, vertices_369, vertices_682, vertices_818, vertices_402, vertices_418, vertices_236, vertices_652, vertices_484, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_515, vertices_69, vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_273, vertices_321, vertices_577, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_76, vertices_140, vertices_524, vertices_228, vertices_324, vertices_388, vertices_644, vertices_104, vertices_168, vertices_552, vertices_584, vertices_648, vertices_112, vertices_304, vertices_560, vertices_592, vertices_400, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_595), (false, vertices_147), (false, vertices_589), (false, vertices_405), (false, vertices_325), (false, vertices_369), (true, vertices_274), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_140), (true, vertices_228), (true, vertices_104), (true, vertices_168), (true, vertices_552), (true, vertices_648), (true, vertices_560), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_595) then 16 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_325) then 1 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_228) then 20 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_228), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_2 0 1 4 5 6 228
cert_row_4 1 0 2 4 6 8 682 162 1
cert_row_4 2 0 3 4 7 8 818 274 2
cert_row_4 3 2 3 4 5 8 632 104 1
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 682
cert_cover_5 0 1 0 2 4 6 162 682 1
cert_coverFacet 1 818
cert_cover_5 1 2 0 3 4 7 274 818 2
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 418
cert_cover_2 3 4 0 6 7 162 418 3
cert_coverFacet 4 236
cert_cover_5 4 0 1 2 4 5 76 236 2
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 484
cert_cover_5 6 0 1 4 5 7 228 484 3
cert_coverFacet 7 632
cert_cover_5 7 3 2 3 4 5 104 632 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0703

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0705.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0705

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 653, 185, 281, 817, 737, 94, 526, 710, 346, 866, 156, 372, 180, 228, 25, 137, 265, 521, 49, 273, 161, 545, 641, 769, 14, 70, 518, 90, 266, 522, 322, 578, 770, 28, 140, 524, 52, 84, 148, 100, 164, 196, 644, 152, 280, 176, 304, 336, 224, 352, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_653, vertices_185, vertices_281, vertices_817, vertices_737, vertices_94, vertices_526, vertices_710, vertices_346, vertices_866, vertices_156, vertices_372, vertices_180, vertices_228] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_521, vertices_49, vertices_273, vertices_161, vertices_545, vertices_641, vertices_769, vertices_14, vertices_70, vertices_518, vertices_90, vertices_266, vertices_522, vertices_322, vertices_578, vertices_770, vertices_28, vertices_140, vertices_524, vertices_52, vertices_84, vertices_148, vertices_100, vertices_164, vertices_196, vertices_644, vertices_152, vertices_280, vertices_176, vertices_304, vertices_336, vertices_224, vertices_352, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_653), (false, vertices_185), (false, vertices_281), (false, vertices_817), (false, vertices_737), (true, vertices_14), (true, vertices_70), (true, vertices_518), (true, vertices_90), (true, vertices_322), (true, vertices_578), (true, vertices_28), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_100), (true, vertices_164), (true, vertices_196), (true, vertices_336), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_90) then 17 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_164) then 11 else
  if p.val = (true, vertices_196) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 281 14 70 518 322 578 28 52 84 148 100 164 196 336 352 779 90 653 185 817 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 5 6 8 710 70 3
cert_row_4 2 0 4 5 7 8 866 322 1
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 14 94 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 710
cert_cover_5 2 1 0 1 5 6 70 710 3
cert_coverFacet 3 346
cert_cover_5 3 0 0 2 3 7 90 346 3
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 322 866 1
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 372
cert_cover_5 6 3 1 3 4 5 52 372 3
cert_coverFacet 7 180
cert_cover_2 7 3 1 4 6 52 180 3
cert_coverFacet 8 228
cert_cover_2 8 4 1 5 6 100 228 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0705

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0706.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0706

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 331, 563, 899, 661, 425, 177, 838, 610, 204, 332, 908, 628, 212, 248, 75, 35, 259, 515, 41, 265, 49, 145, 529, 161, 385, 641, 98, 546, 322, 578, 770, 76, 140, 268, 84, 148, 532, 196, 324, 580, 644, 772, 104, 168, 200, 328, 392, 112, 176, 560, 208, 608, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_331, vertices_563, vertices_899, vertices_661, vertices_425, vertices_177, vertices_838, vertices_610, vertices_204, vertices_332, vertices_908, vertices_628, vertices_212, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_75, vertices_35, vertices_259, vertices_515, vertices_41, vertices_265, vertices_49, vertices_145, vertices_529, vertices_161, vertices_385, vertices_641, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_76, vertices_140, vertices_268, vertices_84, vertices_148, vertices_532, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_104, vertices_168, vertices_200, vertices_328, vertices_392, vertices_112, vertices_176, vertices_560, vertices_208, vertices_608, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_331), (false, vertices_563), (false, vertices_899), (false, vertices_661), (false, vertices_425), (false, vertices_177), (true, vertices_578), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_84), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_200), (true, vertices_112), (true, vertices_208), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 20 14 16 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 17 else
  if p.val = (false, vertices_331) then 18 else
  if p.val = (false, vertices_563) then 21 else
  if p.val = (false, vertices_899) then 22 else
  if p.val = (false, vertices_661) then 15 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 20 => Sum.inl 0
  | 21 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 7 8 838 322 1
cert_row_4 1 1 2 6 7 8 908 140 3
cert_row_4 2 1 3 4 5 8 628 84 2
cert_row_4 3 2 3 4 5 6 248 104 1
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 0 0 1 5 7 322 838 1
cert_coverFacet 1 610
cert_cover_2 1 4 0 5 8 98 610 3
cert_coverFacet 2 204
cert_cover_2 2 2 1 5 6 76 204 3
cert_coverFacet 3 332
cert_cover_2 3 2 1 5 7 76 332 3
cert_coverFacet 4 908
cert_cover_5 4 1 1 2 6 7 140 908 3
cert_coverFacet 5 628
cert_cover_5 5 2 1 3 4 5 84 628 2
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 248
cert_cover_5 7 3 2 3 4 5 104 248 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0706

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0708.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0708

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [59, 275, 611, 899, 709, 433, 225, 782, 282, 554, 220, 284, 620, 916, 248, 19, 35, 259, 515, 49, 273, 97, 161, 193, 577, 385, 641, 26, 42, 266, 522, 274, 546, 770, 28, 76, 268, 524, 148, 276, 196, 580, 644, 772, 56, 216, 280, 104, 552, 176, 400, 224, 608, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_59, vertices_275, vertices_611, vertices_899, vertices_709, vertices_433, vertices_225, vertices_782, vertices_282, vertices_554, vertices_220, vertices_284, vertices_620, vertices_916, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_515, vertices_49, vertices_273, vertices_97, vertices_161, vertices_193, vertices_577, vertices_385, vertices_641, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_546, vertices_770, vertices_28, vertices_76, vertices_268, vertices_524, vertices_148, vertices_276, vertices_196, vertices_580, vertices_644, vertices_772, vertices_56, vertices_216, vertices_280, vertices_104, vertices_552, vertices_176, vertices_400, vertices_224, vertices_608, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_59), (false, vertices_275), (false, vertices_611), (false, vertices_899), (false, vertices_709), (false, vertices_433), (false, vertices_225), (true, vertices_266), (true, vertices_522), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_772), (true, vertices_216), (true, vertices_280), (true, vertices_104), (true, vertices_552)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_59) then 15 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_216) then 21 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_552) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
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
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 1 2 4 5 8 620 76 2
cert_row_2 2 2 3 5 6 216
cert_row_4 3 1 3 6 7 8 916 148 3
cert_rows
cert_pivot_2 0 4 2 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 220
cert_cover_5 3 2 1 2 3 5 28 220 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 620
cert_cover_5 5 1 1 2 4 5 76 620 2
cert_coverFacet 6 916
cert_cover_5 6 3 1 3 6 7 148 916 3
cert_coverFacet 7 248
cert_cover_5 7 2 2 3 4 5 56 248 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0708

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0709.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0709

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 595, 803, 565, 185, 89, 297, 454, 710, 774, 436, 660, 804, 728, 488, 67, 259, 515, 25, 41, 73, 265, 49, 81, 529, 289, 545, 198, 262, 518, 322, 578, 770, 52, 148, 532, 292, 548, 388, 644, 772, 88, 152, 168, 296, 200, 328, 176, 592, 656, 416, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_595, vertices_803, vertices_565, vertices_185, vertices_89, vertices_297, vertices_454, vertices_710, vertices_774, vertices_436, vertices_660, vertices_804, vertices_728, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_25, vertices_41, vertices_73, vertices_265, vertices_49, vertices_81, vertices_529, vertices_289, vertices_545, vertices_198, vertices_262, vertices_518, vertices_322, vertices_578, vertices_770, vertices_52, vertices_148, vertices_532, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_168, vertices_296, vertices_200, vertices_328, vertices_176, vertices_592, vertices_656, vertices_416, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_595), (false, vertices_803), (false, vertices_565), (false, vertices_185), (false, vertices_89), (false, vertices_297), (true, vertices_198), (true, vertices_262), (true, vertices_518), (true, vertices_148), (true, vertices_292), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_200), (true, vertices_656), (true, vertices_416), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 18 else
  if p.val = (false, vertices_595) then 19 else
  if p.val = (false, vertices_803) then 20 else
  if p.val = (false, vertices_565) then 15 else
  if p.val = (false, vertices_185) then 22 else
  if p.val = (false, vertices_89) then 0 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (true, vertices_198) then 16 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_448) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 1 89 0 297 262 518 148 292 388 644 772 200 656 416 448 704 565 198 331 595 803 185
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_4 1 1 3 4 6 7 436 52 3
cert_row_4 2 2 3 5 6 8 728 88 3
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 0 0 1 5 7 198 454 3
cert_coverFacet 1 710
cert_cover_5 1 0 0 1 5 8 198 710 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 436
cert_cover_5 3 1 1 3 4 6 52 436 3
cert_coverFacet 4 660
cert_cover_2 4 3 1 6 8 148 660 3
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coverFacet 6 728
cert_cover_5 6 2 2 3 5 6 88 728 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 168 488 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0709

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0710.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0710

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 141, 781, 613, 425, 849, 353, 158, 534, 550, 626, 466, 482, 540, 920, 13, 37, 133, 517, 137, 265, 97, 161, 289, 321, 577, 769, 22, 38, 134, 518, 82, 146, 530, 98, 162, 546, 450, 28, 140, 524, 532, 548, 152, 536, 392, 776, 336, 592, 400, 784, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_141, vertices_781, vertices_613, vertices_425, vertices_849, vertices_353, vertices_158, vertices_534, vertices_550, vertices_626, vertices_466, vertices_482, vertices_540, vertices_920] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_133, vertices_517, vertices_137, vertices_265, vertices_97, vertices_161, vertices_289, vertices_321, vertices_577, vertices_769, vertices_22, vertices_38, vertices_134, vertices_518, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_450, vertices_28, vertices_140, vertices_524, vertices_532, vertices_548, vertices_152, vertices_536, vertices_392, vertices_776, vertices_336, vertices_592, vertices_400, vertices_784, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_141), (false, vertices_781), (false, vertices_613), (false, vertices_425), (false, vertices_849), (false, vertices_353), (true, vertices_22), (true, vertices_518), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_98), (true, vertices_546), (true, vertices_450), (true, vertices_28), (true, vertices_532), (true, vertices_152), (true, vertices_536), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 15 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_849) then 23 else
  if p.val = (false, vertices_353) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_450) then 16 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 141 1 353 22 518 82 146 530 98 546 28 532 152 536 400 167 450 781 613 425 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 6 158 22 2
cert_row_4 1 0 3 4 5 8 626 82 2
cert_row_2 2 0 5 6 7 450
cert_row_4 3 2 3 6 7 8 920 152 3
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 22 158 2
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 626
cert_cover_5 3 1 0 3 4 5 82 626 2
cert_coverFacet 4 466
cert_cover_5 4 2 0 3 5 6 82 466 3
cert_coverFacet 5 482
cert_cover_5 5 2 0 4 5 6 98 482 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 920
cert_cover_5 7 3 2 3 6 7 152 920 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0710

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0712.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0712

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 531, 835, 357, 185, 601, 233, 902, 666, 402, 204, 844, 652, 436, 228, 19, 259, 515, 25, 169, 73, 49, 529, 97, 289, 321, 577, 146, 274, 530, 386, 642, 770, 76, 140, 524, 100, 164, 292, 196, 324, 388, 644, 772, 152, 536, 200, 584, 648, 176, 304, 400, 224, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_531, vertices_835, vertices_357, vertices_185, vertices_601, vertices_233, vertices_902, vertices_666, vertices_402, vertices_204, vertices_844, vertices_652, vertices_436, vertices_228] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_259, vertices_515, vertices_25, vertices_169, vertices_73, vertices_49, vertices_529, vertices_97, vertices_289, vertices_321, vertices_577, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_100, vertices_164, vertices_292, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_152, vertices_536, vertices_200, vertices_584, vertices_648, vertices_176, vertices_304, vertices_400, vertices_224, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_531), (false, vertices_835), (false, vertices_357), (false, vertices_185), (false, vertices_601), (false, vertices_233), (true, vertices_146), (true, vertices_386), (true, vertices_642), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_164), (true, vertices_196), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_648), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 15 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_357) then 18 else
  if p.val = (false, vertices_185) then 20 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 5 7 8 844 76 3
cert_row_4 1 0 2 3 6 8 666 146 1
cert_row_4 2 0 1 6 7 8 902 386 1
cert_row_4 3 1 3 4 6 7 436 164 1
cert_rows
cert_pivot_2 5 2 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 2 0 1 6 7 386 902 1
cert_coverFacet 1 666
cert_cover_5 1 1 0 2 3 6 146 666 1
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 204
cert_cover_2 3 2 1 5 6 76 204 3
cert_coverFacet 4 844
cert_cover_5 4 0 1 2 5 7 76 844 3
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 164 436 1
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0712

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0713.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0713

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [43, 587, 307, 899, 709, 425, 201, 790, 58, 538, 604, 244, 308, 932, 248, 11, 35, 259, 515, 41, 73, 137, 289, 193, 577, 385, 641, 26, 42, 522, 50, 274, 530, 770, 52, 84, 276, 532, 164, 292, 196, 580, 644, 772, 56, 88, 536, 168, 200, 584, 240, 304, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_43, vertices_587, vertices_307, vertices_899, vertices_709, vertices_425, vertices_201, vertices_790, vertices_58, vertices_538, vertices_604, vertices_244, vertices_308, vertices_932, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_515, vertices_41, vertices_73, vertices_137, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_26, vertices_42, vertices_522, vertices_50, vertices_274, vertices_530, vertices_770, vertices_52, vertices_84, vertices_276, vertices_532, vertices_164, vertices_292, vertices_196, vertices_580, vertices_644, vertices_772, vertices_56, vertices_88, vertices_536, vertices_168, vertices_200, vertices_584, vertices_240, vertices_304, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_43), (false, vertices_587), (false, vertices_307), (false, vertices_899), (false, vertices_709), (false, vertices_425), (false, vertices_201), (true, vertices_26), (true, vertices_530), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_292), (true, vertices_772), (true, vertices_56), (true, vertices_88), (true, vertices_536), (true, vertices_240)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_43) then 0 else
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_307) then 16 else
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_240) then 23 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_43), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_4 1 1 2 3 5 8 604 84 1
cert_row_2 2 3 4 5 6 240
cert_row_4 3 1 4 6 7 8 932 164 3
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 604
cert_cover_5 3 1 1 2 3 5 84 604 1
cert_coverFacet 4 244
cert_cover_5 4 2 1 3 4 5 52 244 3
cert_coverFacet 5 308
cert_cover_2 5 3 1 4 7 52 308 3
cert_coverFacet 6 932
cert_cover_5 6 3 1 4 6 7 164 932 3
cert_coverFacet 7 248
cert_cover_5 7 2 2 3 4 5 56 248 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0713

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0714.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0714

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 109, 653, 117, 405, 809, 305, 342, 714, 818, 594, 450, 204, 452, 632, 13, 21, 101, 133, 41, 521, 49, 273, 289, 385, 641, 769, 82, 274, 530, 194, 322, 578, 386, 642, 770, 76, 140, 84, 276, 196, 324, 388, 104, 552, 200, 584, 648, 112, 304, 560, 592, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_109, vertices_653, vertices_117, vertices_405, vertices_809, vertices_305, vertices_342, vertices_714, vertices_818, vertices_594, vertices_450, vertices_204, vertices_452, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_101, vertices_133, vertices_41, vertices_521, vertices_49, vertices_273, vertices_289, vertices_385, vertices_641, vertices_769, vertices_82, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_84, vertices_276, vertices_196, vertices_324, vertices_388, vertices_104, vertices_552, vertices_200, vertices_584, vertices_648, vertices_112, vertices_304, vertices_560, vertices_592, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_109), (false, vertices_653), (false, vertices_117), (false, vertices_405), (false, vertices_809), (false, vertices_305), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_196), (true, vertices_324), (true, vertices_200), (true, vertices_584), (true, vertices_560), (true, vertices_592), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 19 16 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_109) then 20 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_117) then 21 else
  if p.val = (false, vertices_405) then 22 else
  if p.val = (false, vertices_809) then 18 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
cert_nodeAtPriority_48 0 305 1 82 2 274 530 194 322 578 196 324 200 584 560 592 448 899 653 809 109 117 405
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 82 1
cert_row_4 1 0 2 5 6 8 714 194 1
cert_row_4 2 0 3 4 7 8 818 274 2
cert_row_4 3 2 3 4 5 8 632 104 1
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 82 342 1
cert_coverFacet 1 714
cert_cover_5 1 1 0 2 5 6 194 714 1
cert_coverFacet 2 818
cert_cover_5 2 2 0 3 4 7 274 818 2
cert_coverFacet 3 594
cert_cover_2 3 3 0 5 8 82 594 3
cert_coverFacet 4 450
cert_cover_2 4 5 0 6 7 194 450 3
cert_coverFacet 5 204
cert_cover_2 5 2 1 5 6 76 204 3
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 632
cert_cover_5 7 3 2 3 4 5 104 632 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0714

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3273 : Certifies 3273 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0679.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3274 : Certifies 3274 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0681.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3275 : Certifies 3275 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0682.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3276 : Certifies 3276 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0683.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3277 : Certifies 3277 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0684.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3278 : Certifies 3278 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0686.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3279 : Certifies 3279 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0687.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3280 : Certifies 3280 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0688.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3281 : Certifies 3281 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0689.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3282 : Certifies 3282 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0690.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3283 : Certifies 3283 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0691.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3284 : Certifies 3284 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0692.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3285 : Certifies 3285 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0693.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3286 : Certifies 3286 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0694.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3287 : Certifies 3287 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0695.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3288 : Certifies 3288 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0696.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3289 : Certifies 3289 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0697.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3290 : Certifies 3290 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0698.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3291 : Certifies 3291 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0699.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3292 : Certifies 3292 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0700.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3293 : Certifies 3293 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0701.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3294 : Certifies 3294 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0703.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3295 : Certifies 3295 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0705.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3296 : Certifies 3296 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0706.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3297 : Certifies 3297 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0708.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3298 : Certifies 3298 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0709.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3299 : Certifies 3299 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0710.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3300 : Certifies 3300 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0712.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3301 : Certifies 3301 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0713.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3302 : Certifies 3302 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0714.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B108 (j : Fin 30) :
    Certifies (3273 + j.val) := by
  fin_cases j
  · exact projection_3273
  · exact projection_3274
  · exact projection_3275
  · exact projection_3276
  · exact projection_3277
  · exact projection_3278
  · exact projection_3279
  · exact projection_3280
  · exact projection_3281
  · exact projection_3282
  · exact projection_3283
  · exact projection_3284
  · exact projection_3285
  · exact projection_3286
  · exact projection_3287
  · exact projection_3288
  · exact projection_3289
  · exact projection_3290
  · exact projection_3291
  · exact projection_3292
  · exact projection_3293
  · exact projection_3294
  · exact projection_3295
  · exact projection_3296
  · exact projection_3297
  · exact projection_3298
  · exact projection_3299
  · exact projection_3300
  · exact projection_3301
  · exact projection_3302

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
