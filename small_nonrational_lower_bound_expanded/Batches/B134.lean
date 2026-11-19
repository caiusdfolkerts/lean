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
/- Source: ProjectionCertificates/R_m16e10q1_0163.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0163

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 179, 563, 451, 589, 329, 737, 406, 786, 60, 284, 556, 460, 244, 612, 824, 51, 131, 259, 515, 73, 265, 521, 161, 545, 193, 321, 577, 146, 274, 530, 386, 770, 28, 44, 76, 268, 524, 52, 148, 276, 100, 548, 196, 580, 388, 56, 280, 552, 328, 776, 176, 560, 784, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_179, vertices_563, vertices_451, vertices_589, vertices_329, vertices_737, vertices_406, vertices_786, vertices_60, vertices_284, vertices_556, vertices_460, vertices_244, vertices_612, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_51, vertices_131, vertices_259, vertices_515, vertices_73, vertices_265, vertices_521, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_146, vertices_274, vertices_530, vertices_386, vertices_770, vertices_28, vertices_44, vertices_76, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_100, vertices_548, vertices_196, vertices_580, vertices_388, vertices_56, vertices_280, vertices_552, vertices_328, vertices_776, vertices_176, vertices_560, vertices_784, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_179), (false, vertices_563), (false, vertices_451), (false, vertices_589), (false, vertices_329), (false, vertices_737), (true, vertices_274), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_100), (true, vertices_548), (true, vertices_196), (true, vertices_388), (true, vertices_56), (true, vertices_280), (true, vertices_552), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 20 16 18 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_179) then 21 else
  if p.val = (false, vertices_563) then 22 else
  if p.val = (false, vertices_451) then 23 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_552) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inl 0
  | 21 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
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
cert_row_4 0 0 1 3 6 7 406 146 1
cert_row_4 1 2 3 4 7 8 824 56 3
cert_row_4 2 1 2 5 6 7 460 76 3
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 0 8 2 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 146 406 1
cert_coverFacet 1 786
cert_cover_2 1 3 0 7 8 274 786 3
cert_coverFacet 2 60
cert_cover_2 2 2 1 3 4 28 60 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 556
cert_cover_2 4 2 1 4 8 44 556 3
cert_coverFacet 5 460
cert_cover_5 5 2 1 2 5 6 76 460 3
cert_coverFacet 6 244
cert_cover_5 6 3 1 3 4 5 52 244 3
cert_coverFacet 7 612
cert_cover_2 7 4 1 5 8 100 612 3
cert_coverFacet 8 824
cert_cover_5 8 1 2 3 4 7 56 824 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0163

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0164.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0164

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 781, 181, 597, 389, 345, 401, 678, 362, 426, 650, 626, 564, 900, 904, 496, 21, 133, 261, 517, 73, 265, 521, 81, 145, 273, 577, 385, 298, 74, 138, 522, 98, 162, 546, 578, 642, 52, 532, 164, 548, 388, 644, 772, 328, 392, 648, 776, 112, 176, 560, 336, 592, 400, 352, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_781, vertices_181, vertices_597, vertices_389, vertices_345, vertices_401, vertices_678, vertices_362, vertices_426, vertices_650, vertices_626, vertices_564, vertices_900, vertices_904, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_577, vertices_385, vertices_298, vertices_74, vertices_138, vertices_522, vertices_98, vertices_162, vertices_546, vertices_578, vertices_642, vertices_52, vertices_532, vertices_164, vertices_548, vertices_388, vertices_644, vertices_772, vertices_328, vertices_392, vertices_648, vertices_776, vertices_112, vertices_176, vertices_560, vertices_336, vertices_592, vertices_400, vertices_352, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_781), (false, vertices_181), (false, vertices_597), (false, vertices_389), (false, vertices_345), (false, vertices_401), (true, vertices_298), (true, vertices_138), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_642), (true, vertices_548), (true, vertices_644), (true, vertices_392), (true, vertices_648), (true, vertices_112), (true, vertices_560), (true, vertices_352), (true, vertices_416), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 17 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_181) then 21 else
  if p.val = (false, vertices_597) then 22 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_345) then 24 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (true, vertices_298) then 18 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_416) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
cert_nodeAtPriority_5 0 389 1 401 138 98 162 546 642 548 644 392 648 112 560 352 416 896 587 298 781 181 597 345
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 7 298
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 0 3 4 5 8 626 98 1
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 362
cert_cover_5 1 0 0 2 4 5 298 362 3
cert_coverFacet 2 426
cert_cover_5 2 0 0 2 4 6 298 426 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 626
cert_cover_5 4 2 0 3 4 5 98 626 1
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 900
cert_cover_2 6 6 1 7 8 388 900 3
cert_coverFacet 7 904
cert_cover_2 7 6 2 7 8 392 904 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0164

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0165.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0165

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 267, 835, 613, 233, 393, 465, 790, 410, 666, 684, 372, 180, 660, 836, 240, 11, 259, 515, 41, 137, 265, 97, 545, 193, 321, 577, 385, 154, 266, 522, 274, 530, 770, 52, 148, 276, 532, 100, 164, 548, 324, 580, 644, 772, 168, 552, 392, 648, 112, 176, 208, 336, 400, 656, 224, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_267, vertices_835, vertices_613, vertices_233, vertices_393, vertices_465, vertices_790, vertices_410, vertices_666, vertices_684, vertices_372, vertices_180, vertices_660, vertices_836, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_259, vertices_515, vertices_41, vertices_137, vertices_265, vertices_97, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_154, vertices_266, vertices_522, vertices_274, vertices_530, vertices_770, vertices_52, vertices_148, vertices_276, vertices_532, vertices_100, vertices_164, vertices_548, vertices_324, vertices_580, vertices_644, vertices_772, vertices_168, vertices_552, vertices_392, vertices_648, vertices_112, vertices_176, vertices_208, vertices_336, vertices_400, vertices_656, vertices_224, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_267), (false, vertices_835), (false, vertices_613), (false, vertices_233), (false, vertices_393), (false, vertices_465), (true, vertices_154), (true, vertices_274), (true, vertices_530), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_324), (true, vertices_644), (true, vertices_772), (true, vertices_648), (true, vertices_112), (true, vertices_176), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 17 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_393) then 1 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (true, vertices_154) then 19 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_656) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_4 0 1 3 4 5 7 372 52 3
cert_row_4 1 0 1 3 7 8 790 274 1
cert_row_2 2 0 2 3 6 154
cert_row_4 3 1 2 4 6 8 684 164 1
cert_rows
cert_pivot_2 5 7 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 274 790 1
cert_coverFacet 1 410
cert_cover_5 1 2 0 2 3 7 154 410 3
cert_coverFacet 2 666
cert_cover_5 2 2 0 2 3 8 154 666 3
cert_coverFacet 3 684
cert_cover_5 3 3 1 2 4 6 164 684 1
cert_coverFacet 4 372
cert_cover_5 4 0 1 3 4 5 52 372 3
cert_coverFacet 5 180
cert_cover_2 5 3 1 4 6 52 180 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 836
cert_cover_2 7 5 1 7 8 324 836 3
cert_coverFacet 8 240
cert_cover_2 8 4 3 5 6 112 240 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0165

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0166.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0166

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 803, 707, 653, 229, 549, 353, 782, 282, 538, 594, 188, 316, 804, 728, 496, 67, 259, 515, 37, 133, 517, 97, 289, 545, 193, 321, 641, 26, 266, 522, 82, 274, 530, 578, 770, 60, 140, 268, 524, 164, 292, 548, 772, 152, 280, 536, 648, 176, 304, 208, 336, 592, 224, 352, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_803, vertices_707, vertices_653, vertices_229, vertices_549, vertices_353, vertices_782, vertices_282, vertices_538, vertices_594, vertices_188, vertices_316, vertices_804, vertices_728, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_37, vertices_133, vertices_517, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_26, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_578, vertices_770, vertices_60, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_772, vertices_152, vertices_280, vertices_536, vertices_648, vertices_176, vertices_304, vertices_208, vertices_336, vertices_592, vertices_224, vertices_352, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_803), (false, vertices_707), (false, vertices_653), (false, vertices_229), (false, vertices_549), (false, vertices_353), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_530), (true, vertices_60), (true, vertices_268), (true, vertices_292), (true, vertices_772), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_176), (true, vertices_304), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 24 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 17 else
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_707) then 19 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_353) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_60) then 23 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_592) then 15 else
  0
cert_priority
cert_nodeAtPriority_6 549 353 26 266 522 530 268 292 772 152 280 536 176 304 208 592 339 803 707 653 229 60
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 3 5 6 8 728 152 2
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 594
cert_cover_2 3 3 0 5 8 82 594 3
cert_coverFacet 4 188
cert_cover_5 4 1 1 2 3 6 60 188 3
cert_coverFacet 5 316
cert_cover_5 5 1 1 2 3 7 60 316 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 728
cert_cover_5 7 2 2 3 5 6 152 728 2
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 176 496 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0166

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0167.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0167

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 141, 781, 709, 465, 865, 62, 158, 362, 626, 338, 402, 556, 692, 808, 720, 13, 133, 517, 137, 265, 193, 321, 577, 385, 769, 30, 42, 138, 266, 50, 82, 146, 274, 98, 322, 386, 44, 140, 524, 52, 148, 548, 644, 296, 552, 776, 560, 208, 336, 592, 400, 656, 352, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_141, vertices_781, vertices_709, vertices_465, vertices_865, vertices_62, vertices_158, vertices_362, vertices_626, vertices_338, vertices_402, vertices_556, vertices_692, vertices_808, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_137, vertices_265, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_30, vertices_42, vertices_138, vertices_266, vertices_50, vertices_82, vertices_146, vertices_274, vertices_98, vertices_322, vertices_386, vertices_44, vertices_140, vertices_524, vertices_52, vertices_148, vertices_548, vertices_644, vertices_296, vertices_552, vertices_776, vertices_560, vertices_208, vertices_336, vertices_592, vertices_400, vertices_656, vertices_352, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_141), (false, vertices_781), (false, vertices_709), (false, vertices_465), (false, vertices_865), (true, vertices_30), (true, vertices_42), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_98), (true, vertices_322), (true, vertices_44), (true, vertices_52), (true, vertices_148), (true, vertices_548), (true, vertices_296), (true, vertices_552), (true, vertices_560), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (false, vertices_865) then 27 else
  if p.val = (true, vertices_30) then 19 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_592) then 15 else
  if p.val = (true, vertices_656) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_30), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 7 362 42 3
cert_row_2 1 0 1 2 3 30
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 1 0 1 2 4 30 62 3
cert_coverFacet 1 158
cert_cover_5 1 1 0 1 2 6 30 158 3
cert_coverFacet 2 362
cert_cover_5 2 0 0 2 4 5 42 362 3
cert_coverFacet 3 626
cert_cover_5 3 2 0 3 4 5 50 626 3
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 692
cert_cover_5 7 3 1 3 4 6 52 692 3
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coverFacet 9 720
cert_cover_2 9 5 3 6 8 208 720 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0167

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0168.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0168

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 299, 523, 451, 569, 865, 705, 158, 526, 410, 540, 116, 564, 468, 740, 376, 11, 131, 259, 515, 41, 521, 289, 545, 193, 321, 577, 641, 14, 134, 518, 154, 266, 522, 386, 28, 524, 52, 84, 148, 532, 100, 548, 196, 644, 56, 280, 536, 296, 112, 560, 336, 400, 352, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_299, vertices_523, vertices_451, vertices_569, vertices_865, vertices_705, vertices_158, vertices_526, vertices_410, vertices_540, vertices_116, vertices_564, vertices_468, vertices_740, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_131, vertices_259, vertices_515, vertices_41, vertices_521, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_14, vertices_134, vertices_518, vertices_154, vertices_266, vertices_522, vertices_386, vertices_28, vertices_524, vertices_52, vertices_84, vertices_148, vertices_532, vertices_100, vertices_548, vertices_196, vertices_644, vertices_56, vertices_280, vertices_536, vertices_296, vertices_112, vertices_560, vertices_336, vertices_400, vertices_352, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_299), (false, vertices_523), (false, vertices_451), (false, vertices_569), (false, vertices_865), (false, vertices_705), (true, vertices_14), (true, vertices_154), (true, vertices_28), (true, vertices_524), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_100), (true, vertices_548), (true, vertices_196), (true, vertices_280), (true, vertices_112), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 16 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 17 else
  if p.val = (false, vertices_299) then 19 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_451) then 20 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_865) then 26 else
  if p.val = (false, vertices_705) then 1 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_154) then 21 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
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
cert_row_2 0 0 2 3 6 154
cert_row_4 1 1 4 5 6 8 740 100 3
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 14 158 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 410
cert_cover_5 2 0 0 2 3 7 154 410 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 116
cert_cover_2 4 3 1 4 5 52 116 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 468
cert_cover_5 6 2 1 3 5 6 84 468 3
cert_coverFacet 7 740
cert_cover_5 7 1 1 4 5 6 100 740 3
cert_coverFacet 8 376
cert_cover_5 8 3 2 3 4 5 56 376 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0168

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0169.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0169

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 309, 533, 677, 409, 233, 297, 838, 218, 346, 786, 738, 620, 300, 332, 788, 21, 37, 517, 41, 137, 265, 145, 273, 529, 161, 289, 641, 90, 146, 274, 530, 194, 322, 578, 642, 770, 44, 76, 268, 276, 532, 292, 548, 324, 580, 772, 152, 280, 104, 296, 200, 328, 784, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_309, vertices_533, vertices_677, vertices_409, vertices_233, vertices_297, vertices_838, vertices_218, vertices_346, vertices_786, vertices_738, vertices_620, vertices_300, vertices_332, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_517, vertices_41, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_641, vertices_90, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_44, vertices_76, vertices_268, vertices_276, vertices_532, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_104, vertices_296, vertices_200, vertices_328, vertices_784, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_309), (false, vertices_533), (false, vertices_677), (false, vertices_409), (false, vertices_233), (false, vertices_297), (true, vertices_90), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_328), (true, vertices_784), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_309) then 20 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_409) then 23 else
  if p.val = (false, vertices_233) then 24 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (true, vertices_90) then 18 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_608) then 15 else
  0
cert_priority
cert_nodeAtPriority_39 0 533 1 297 274 194 322 578 770 44 76 268 324 580 772 328 784 608 659 90 309 677 409 233
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
cert_coverFacet 5 620
cert_cover_5 5 3 1 2 4 5 44 620 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 332
cert_cover_2 7 2 1 5 7 76 332 3
cert_coverFacet 8 788
cert_cover_2 8 3 1 7 8 276 788 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0169

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0170.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0170

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 181, 533, 453, 569, 737, 833, 286, 542, 106, 554, 458, 866, 404, 248, 408, 21, 133, 261, 517, 49, 529, 161, 545, 193, 321, 577, 769, 30, 262, 518, 42, 74, 266, 522, 98, 546, 322, 770, 148, 276, 532, 388, 56, 152, 280, 536, 104, 552, 200, 392, 176, 400, 224, 608, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_181, vertices_533, vertices_453, vertices_569, vertices_737, vertices_833, vertices_286, vertices_542, vertices_106, vertices_554, vertices_458, vertices_866, vertices_404, vertices_248, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_49, vertices_529, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_769, vertices_30, vertices_262, vertices_518, vertices_42, vertices_74, vertices_266, vertices_522, vertices_98, vertices_546, vertices_322, vertices_770, vertices_148, vertices_276, vertices_532, vertices_388, vertices_56, vertices_152, vertices_280, vertices_536, vertices_104, vertices_552, vertices_200, vertices_392, vertices_176, vertices_400, vertices_224, vertices_608, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_181), (false, vertices_533), (false, vertices_453), (false, vertices_569), (false, vertices_737), (false, vertices_833), (true, vertices_30), (true, vertices_42), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_98), (true, vertices_546), (true, vertices_322), (true, vertices_276), (true, vertices_152), (true, vertices_280), (true, vertices_104), (true, vertices_200), (true, vertices_392), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_181) then 20 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (false, vertices_833) then 1 else
  if p.val = (true, vertices_30) then 18 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 1 533 0 833 42 74 266 522 98 546 322 276 152 280 104 200 392 400 775 30 181 453 569 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 0 4 5 7 8 866 98 3
cert_row_4 2 0 2 5 6 7 458 74 3
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 7 30 286 3
cert_coverFacet 1 542
cert_cover_5 1 0 0 1 2 8 30 542 3
cert_coverFacet 2 106
cert_cover_2 2 2 0 4 5 42 106 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 458
cert_cover_5 4 2 0 2 5 6 74 458 3
cert_coverFacet 5 866
cert_cover_5 5 1 0 4 5 7 98 866 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 248
cert_cover_5 7 3 2 3 4 5 56 248 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0170

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0171.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0171

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 203, 395, 611, 309, 549, 481, 602, 778, 908, 628, 404, 660, 248, 664, 432, 139, 67, 259, 515, 37, 261, 517, 97, 289, 545, 193, 385, 74, 266, 522, 578, 770, 52, 148, 276, 532, 548, 388, 644, 772, 88, 152, 536, 200, 392, 648, 776, 112, 176, 304, 592, 400, 656, 224, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_203, vertices_395, vertices_611, vertices_309, vertices_549, vertices_481, vertices_602, vertices_778, vertices_908, vertices_628, vertices_404, vertices_660, vertices_248, vertices_664, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_139, vertices_67, vertices_259, vertices_515, vertices_37, vertices_261, vertices_517, vertices_97, vertices_289, vertices_545, vertices_193, vertices_385, vertices_74, vertices_266, vertices_522, vertices_578, vertices_770, vertices_52, vertices_148, vertices_276, vertices_532, vertices_548, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_536, vertices_200, vertices_392, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_592, vertices_400, vertices_656, vertices_224, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_203), (false, vertices_395), (false, vertices_611), (false, vertices_309), (false, vertices_549), (false, vertices_481), (true, vertices_522), (true, vertices_148), (true, vertices_532), (true, vertices_388), (true, vertices_644), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_648), (true, vertices_776), (true, vertices_112), (true, vertices_176), (true, vertices_592), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 16 23 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_203) then 20 else
  if p.val = (false, vertices_395) then 21 else
  if p.val = (false, vertices_611) then 22 else
  if p.val = (false, vertices_309) then 18 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_656) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_549), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
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
cert_row_4 0 0 2 3 5 8 602 74 2
cert_row_4 1 1 2 6 7 8 908 388 1
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 2 3 4 5 6 248 88 2
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 602
cert_cover_5 0 0 0 2 3 5 74 602 2
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 908
cert_cover_5 2 1 1 2 6 7 388 908 1
cert_coverFacet 3 628
cert_cover_5 3 2 1 3 4 5 52 628 3
cert_coverFacet 4 404
cert_cover_2 4 3 1 6 7 148 404 3
cert_coverFacet 5 660
cert_cover_2 5 3 1 6 8 148 660 3
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 88 248 2
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0171

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0172.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0172

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 541, 269, 357, 677, 185, 297, 838, 218, 346, 786, 738, 284, 788, 612, 488, 13, 37, 261, 517, 25, 41, 265, 145, 529, 161, 289, 641, 90, 146, 274, 530, 194, 322, 578, 642, 770, 28, 268, 276, 532, 100, 548, 324, 580, 772, 152, 280, 168, 296, 200, 328, 784, 224, 352, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_541, vertices_269, vertices_357, vertices_677, vertices_185, vertices_297, vertices_838, vertices_218, vertices_346, vertices_786, vertices_738, vertices_284, vertices_788, vertices_612, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_261, vertices_517, vertices_25, vertices_41, vertices_265, vertices_145, vertices_529, vertices_161, vertices_289, vertices_641, vertices_90, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_268, vertices_276, vertices_532, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_168, vertices_296, vertices_200, vertices_328, vertices_784, vertices_224, vertices_352, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_541), (false, vertices_269), (false, vertices_357), (false, vertices_677), (false, vertices_185), (false, vertices_297), (true, vertices_90), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_276), (true, vertices_580), (true, vertices_772), (true, vertices_280), (true, vertices_200), (true, vertices_328), (true, vertices_784), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_541) then 20 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_185) then 24 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (true, vertices_90) then 18 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_608) then 15 else
  0
cert_priority
cert_nodeAtPriority_5 0 269 1 297 274 194 322 578 770 276 580 772 280 200 328 784 224 608 659 90 541 357 677 185
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 3 1 0 2
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
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 612
cert_cover_2 7 4 1 5 8 100 612 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 168 488 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0172

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0173.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0173

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 299, 523, 451, 553, 721, 865, 158, 526, 410, 316, 620, 116, 596, 660, 496, 11, 131, 259, 515, 41, 521, 289, 545, 193, 321, 577, 641, 14, 134, 518, 154, 266, 522, 386, 28, 44, 524, 52, 84, 148, 532, 100, 580, 644, 280, 296, 552, 112, 304, 208, 592, 400, 656, 352, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_299, vertices_523, vertices_451, vertices_553, vertices_721, vertices_865, vertices_158, vertices_526, vertices_410, vertices_316, vertices_620, vertices_116, vertices_596, vertices_660, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_131, vertices_259, vertices_515, vertices_41, vertices_521, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_14, vertices_134, vertices_518, vertices_154, vertices_266, vertices_522, vertices_386, vertices_28, vertices_44, vertices_524, vertices_52, vertices_84, vertices_148, vertices_532, vertices_100, vertices_580, vertices_644, vertices_280, vertices_296, vertices_552, vertices_112, vertices_304, vertices_208, vertices_592, vertices_400, vertices_656, vertices_352, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_299), (false, vertices_523), (false, vertices_451), (false, vertices_553), (false, vertices_721), (false, vertices_865), (true, vertices_14), (true, vertices_154), (true, vertices_28), (true, vertices_44), (true, vertices_524), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_100), (true, vertices_580), (true, vertices_280), (true, vertices_112), (true, vertices_304), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 16 22 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 17 else
  if p.val = (false, vertices_299) then 19 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_451) then 20 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (false, vertices_865) then 26 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_154) then 21 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 1 2 4 5 8 620 44 3
cert_row_4 2 1 2 3 4 7 316 28 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 8 1 3
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 14 158 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 410
cert_cover_5 2 0 0 2 3 7 154 410 3
cert_coverFacet 3 316
cert_cover_5 3 2 1 2 3 4 28 316 3
cert_coverFacet 4 620
cert_cover_5 4 1 1 2 4 5 44 620 3
cert_coverFacet 5 116
cert_cover_2 5 3 1 4 5 52 116 3
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0173

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0174.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0174

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 653, 233, 297, 721, 865, 158, 526, 310, 838, 186, 298, 340, 596, 660, 496, 41, 137, 265, 521, 97, 289, 193, 577, 641, 769, 14, 22, 262, 518, 154, 42, 266, 522, 50, 290, 770, 140, 524, 84, 148, 276, 532, 324, 580, 644, 168, 296, 176, 304, 208, 336, 592, 656, 224, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_653, vertices_233, vertices_297, vertices_721, vertices_865, vertices_158, vertices_526, vertices_310, vertices_838, vertices_186, vertices_298, vertices_340, vertices_596, vertices_660, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_265, vertices_521, vertices_97, vertices_289, vertices_193, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_518, vertices_154, vertices_42, vertices_266, vertices_522, vertices_50, vertices_290, vertices_770, vertices_140, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_324, vertices_580, vertices_644, vertices_168, vertices_296, vertices_176, vertices_304, vertices_208, vertices_336, vertices_592, vertices_656, vertices_224, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_653), (false, vertices_233), (false, vertices_297), (false, vertices_721), (false, vertices_865), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_154), (true, vertices_42), (true, vertices_50), (true, vertices_290), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_324), (true, vertices_580), (true, vertices_176), (true, vertices_304), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (false, vertices_865) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_154) then 19 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_50) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_324) then 12 else
  if p.val = (true, vertices_580) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_304) then 15 else
  if p.val = (true, vertices_336) then 16 else
  0
cert_priority
cert_nodeAtPriority_66 297 14 22 262 518 42 50 290 84 148 276 532 324 580 176 304 336 779 154 653 233 721 865
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 0 1 5 7 8 838 262 2
cert_row_4 2 0 1 3 4 7 310 22 3
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 2 8 0 3
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 14 158 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 310
cert_cover_5 2 2 0 1 3 4 22 310 3
cert_coverFacet 3 838
cert_cover_5 3 1 0 1 5 7 262 838 2
cert_coverFacet 4 186
cert_cover_5 4 0 0 2 3 4 154 186 3
cert_coverFacet 5 298
cert_cover_2 5 2 0 4 7 42 298 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 660
cert_cover_2 8 3 1 6 8 148 660 3
cert_coverFacet 9 496
cert_cover_5 9 3 3 4 5 6 176 496 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0174

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0175.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0175

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 93, 525, 837, 681, 201, 481, 158, 174, 534, 550, 434, 850, 556, 596, 472, 13, 69, 517, 73, 137, 521, 161, 289, 545, 193, 321, 769, 142, 22, 38, 518, 146, 274, 530, 162, 290, 546, 770, 28, 44, 524, 84, 532, 548, 580, 88, 152, 168, 552, 200, 336, 592, 400, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_93, vertices_525, vertices_837, vertices_681, vertices_201, vertices_481, vertices_158, vertices_174, vertices_534, vertices_550, vertices_434, vertices_850, vertices_556, vertices_596, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_73, vertices_137, vertices_521, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_769, vertices_142, vertices_22, vertices_38, vertices_518, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_770, vertices_28, vertices_44, vertices_524, vertices_84, vertices_532, vertices_548, vertices_580, vertices_88, vertices_152, vertices_168, vertices_552, vertices_200, vertices_336, vertices_592, vertices_400, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_93), (false, vertices_525), (false, vertices_837), (false, vertices_681), (false, vertices_201), (false, vertices_481), (true, vertices_142), (true, vertices_22), (true, vertices_38), (true, vertices_518), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_44), (true, vertices_532), (true, vertices_548), (true, vertices_152), (true, vertices_336), (true, vertices_592), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_93) then 20 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_142) then 18 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_38) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_162) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 1 525 0 201 22 38 518 146 274 530 162 44 532 548 152 336 592 400 803 142 93 837 681 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 6 142
cert_row_4 1 0 3 4 6 7 434 146 2
cert_row_4 2 0 3 5 7 8 850 274 2
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 142 158 3
cert_coverFacet 1 174
cert_cover_5 1 0 0 1 2 4 142 174 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 550
cert_cover_2 3 1 0 4 8 38 550 3
cert_coverFacet 4 434
cert_cover_5 4 1 0 3 4 6 146 434 2
cert_coverFacet 5 850
cert_cover_5 5 2 0 3 5 7 274 850 2
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 472
cert_cover_5 8 3 2 3 5 6 88 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0175

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0176.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0176

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 45, 589, 213, 421, 801, 961, 542, 314, 466, 594, 866, 156, 172, 596, 440, 13, 37, 69, 133, 41, 521, 289, 545, 193, 577, 385, 769, 26, 42, 522, 82, 274, 530, 290, 546, 322, 578, 28, 44, 140, 524, 84, 148, 532, 164, 580, 312, 152, 168, 208, 592, 400, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_45, vertices_589, vertices_213, vertices_421, vertices_801, vertices_961, vertices_542, vertices_314, vertices_466, vertices_594, vertices_866, vertices_156, vertices_172, vertices_596, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_133, vertices_41, vertices_521, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_26, vertices_42, vertices_522, vertices_82, vertices_274, vertices_530, vertices_290, vertices_546, vertices_322, vertices_578, vertices_28, vertices_44, vertices_140, vertices_524, vertices_84, vertices_148, vertices_532, vertices_164, vertices_580, vertices_312, vertices_152, vertices_168, vertices_208, vertices_592, vertices_400, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_45), (false, vertices_589), (false, vertices_213), (false, vertices_421), (false, vertices_801), (false, vertices_961), (true, vertices_26), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_322), (true, vertices_578), (true, vertices_28), (true, vertices_140), (true, vertices_532), (true, vertices_312), (true, vertices_152), (true, vertices_168), (true, vertices_592), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 24 25 26 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 17 else
  if p.val = (false, vertices_45) then 0 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_801) then 1 else
  if p.val = (false, vertices_961) then 27 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_312) then 23 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(true, vertices_312), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 26 1
cert_row_2 1 2 3 4 7 312
cert_row_4 2 0 3 5 6 7 466 82 3
cert_row_4 3 0 4 5 7 8 866 290 2
cert_rows
cert_pivot_2 1 2 3 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 26 542 1
cert_coverFacet 1 314
cert_cover_5 1 1 0 2 3 4 26 314 3
cert_coverFacet 2 466
cert_cover_5 2 2 0 3 5 6 82 466 3
cert_coverFacet 3 594
cert_cover_2 3 3 0 5 8 82 594 3
cert_coverFacet 4 866
cert_cover_5 4 3 0 4 5 7 290 866 2
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 172
cert_cover_2 6 2 1 4 6 44 172 3
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 440
cert_cover_5 8 1 2 3 4 6 312 440 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0176

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0177.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0177

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 181, 533, 613, 361, 465, 417, 662, 346, 618, 394, 650, 402, 812, 908, 420, 21, 37, 517, 81, 145, 529, 97, 161, 289, 321, 577, 385, 74, 138, 266, 522, 82, 146, 274, 530, 578, 386, 642, 780, 148, 532, 164, 292, 548, 388, 644, 104, 296, 552, 328, 392, 648, 336, 400, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_181, vertices_533, vertices_613, vertices_361, vertices_465, vertices_417, vertices_662, vertices_346, vertices_618, vertices_394, vertices_650, vertices_402, vertices_812, vertices_908, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_517, vertices_81, vertices_145, vertices_529, vertices_97, vertices_161, vertices_289, vertices_321, vertices_577, vertices_385, vertices_74, vertices_138, vertices_266, vertices_522, vertices_82, vertices_146, vertices_274, vertices_530, vertices_578, vertices_386, vertices_642, vertices_780, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_104, vertices_296, vertices_552, vertices_328, vertices_392, vertices_648, vertices_336, vertices_400, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_181), (false, vertices_533), (false, vertices_613), (false, vertices_361), (false, vertices_465), (false, vertices_417), (true, vertices_74), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_386), (true, vertices_642), (true, vertices_780), (true, vertices_292), (true, vertices_388), (true, vertices_644), (true, vertices_552), (true, vertices_392), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 17 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (false, vertices_417) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_274) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_642) then 9 else
  if p.val = (true, vertices_780) then 21 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_644) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_648) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_2 1 1 2 7 8 780
cert_row_4 2 0 2 3 5 7 346 74 2
cert_row_4 3 0 2 4 5 8 618 74 2
cert_rows
cert_pivot_2 6 1 3 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 346
cert_cover_5 1 2 0 2 3 5 74 346 2
cert_coverFacet 2 618
cert_cover_5 2 3 0 2 4 5 74 618 2
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 812
cert_cover_5 6 1 1 2 4 7 780 812 2
cert_coverFacet 7 908
cert_cover_5 7 1 1 2 6 7 780 908 2
cert_coverFacet 8 420
cert_cover_2 8 4 1 6 7 164 420 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0177

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0178.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0178

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 115, 531, 419, 93, 541, 229, 389, 794, 306, 588, 964, 248, 312, 936, 712, 19, 35, 259, 515, 29, 69, 133, 261, 517, 81, 529, 97, 161, 385, 50, 274, 530, 290, 770, 76, 524, 196, 580, 388, 772, 56, 88, 280, 536, 168, 296, 200, 584, 648, 776, 112, 304, 224, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_115, vertices_531, vertices_419, vertices_93, vertices_541, vertices_229, vertices_389, vertices_794, vertices_306, vertices_588, vertices_964, vertices_248, vertices_312, vertices_936, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_515, vertices_29, vertices_69, vertices_133, vertices_261, vertices_517, vertices_81, vertices_529, vertices_97, vertices_161, vertices_385, vertices_50, vertices_274, vertices_530, vertices_290, vertices_770, vertices_76, vertices_524, vertices_196, vertices_580, vertices_388, vertices_772, vertices_56, vertices_88, vertices_280, vertices_536, vertices_168, vertices_296, vertices_200, vertices_584, vertices_648, vertices_776, vertices_112, vertices_304, vertices_224, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_115), (false, vertices_531), (false, vertices_419), (false, vertices_93), (false, vertices_541), (false, vertices_229), (false, vertices_389), (true, vertices_274), (true, vertices_580), (true, vertices_56), (true, vertices_280), (true, vertices_168), (true, vertices_296), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_776), (true, vertices_304), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 23 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_115) then 17 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_419) then 18 else
  if p.val = (false, vertices_93) then 20 else
  if p.val = (false, vertices_541) then 21 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_56) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_704) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
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
cert_row_4 0 0 2 3 7 8 794 274 1
cert_row_4 1 1 5 6 7 8 964 196 3
cert_row_4 2 2 3 4 5 6 248 56 3
cert_row_4 3 2 4 6 7 8 936 168 3
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 794
cert_cover_5 0 0 0 2 3 7 274 794 1
cert_coverFacet 1 306
cert_cover_2 1 3 0 4 7 50 306 3
cert_coverFacet 2 588
cert_cover_2 2 2 1 5 8 76 588 3
cert_coverFacet 3 964
cert_cover_5 3 1 1 5 6 7 196 964 3
cert_coverFacet 4 248
cert_cover_5 4 2 2 3 4 5 56 248 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 936
cert_cover_5 6 3 2 4 6 7 168 936 3
cert_coverFacet 7 712
cert_cover_2 7 5 2 6 8 200 712 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0178

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0179.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0179

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 535, 395, 675, 817, 481, 270, 526, 714, 124, 540, 460, 308, 356, 600, 752, 23, 131, 259, 515, 273, 529, 161, 289, 545, 385, 14, 262, 518, 138, 266, 522, 642, 28, 76, 268, 524, 52, 276, 532, 100, 292, 324, 88, 536, 200, 584, 392, 112, 304, 560, 592, 224, 352, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_535, vertices_395, vertices_675, vertices_817, vertices_481, vertices_270, vertices_526, vertices_714, vertices_124, vertices_540, vertices_460, vertices_308, vertices_356, vertices_600, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_131, vertices_259, vertices_515, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_385, vertices_14, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_642, vertices_28, vertices_76, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_100, vertices_292, vertices_324, vertices_88, vertices_536, vertices_200, vertices_584, vertices_392, vertices_112, vertices_304, vertices_560, vertices_592, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_535), (false, vertices_395), (false, vertices_675), (false, vertices_817), (false, vertices_481), (true, vertices_14), (true, vertices_522), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_100), (true, vertices_292), (true, vertices_324), (true, vertices_88), (true, vertices_536), (true, vertices_200), (true, vertices_584), (true, vertices_112), (true, vertices_592), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 20 17 23 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 18 else
  if p.val = (false, vertices_535) then 19 else
  if p.val = (false, vertices_395) then 21 else
  if p.val = (false, vertices_675) then 22 else
  if p.val = (false, vertices_817) then 25 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_112) then 14 else
  if p.val = (true, vertices_592) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 20 => Sum.inl 0
  | 21 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 138 2
cert_row_4 1 1 2 5 6 7 460 76 3
cert_row_4 2 1 2 3 4 5 124 28 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 7 1 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 714
cert_cover_5 2 0 0 2 5 6 138 714 2
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 4 28 124 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 460
cert_cover_5 5 1 1 2 5 6 76 460 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 356
cert_cover_2 7 4 1 5 7 100 356 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coverFacet 9 752
cert_cover_5 9 3 3 4 5 6 112 752 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0179

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0180.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0180

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 93, 525, 581, 681, 457, 865, 158, 174, 534, 550, 818, 466, 556, 852, 216, 13, 69, 517, 73, 137, 521, 161, 289, 545, 321, 577, 385, 142, 22, 38, 518, 146, 274, 530, 162, 290, 546, 386, 28, 44, 524, 84, 532, 548, 580, 88, 152, 168, 552, 200, 208, 336, 784, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_93, vertices_525, vertices_581, vertices_681, vertices_457, vertices_865, vertices_158, vertices_174, vertices_534, vertices_550, vertices_818, vertices_466, vertices_556, vertices_852, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_73, vertices_137, vertices_521, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_142, vertices_22, vertices_38, vertices_518, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_28, vertices_44, vertices_524, vertices_84, vertices_532, vertices_548, vertices_580, vertices_88, vertices_152, vertices_168, vertices_552, vertices_200, vertices_208, vertices_336, vertices_784, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_93), (false, vertices_525), (false, vertices_581), (false, vertices_681), (false, vertices_457), (false, vertices_865), (true, vertices_142), (true, vertices_22), (true, vertices_38), (true, vertices_518), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_44), (true, vertices_532), (true, vertices_548), (true, vertices_152), (true, vertices_208), (true, vertices_336), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 17 else
  if p.val = (false, vertices_93) then 20 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_581) then 1 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (false, vertices_865) then 26 else
  if p.val = (true, vertices_142) then 18 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_38) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_142), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
cert_row_2 0 0 1 2 6 142
cert_row_4 1 0 3 4 7 8 818 274 2
cert_row_4 2 0 3 5 6 7 466 146 2
cert_row_4 3 1 3 5 7 8 852 84 3
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 142 158 3
cert_coverFacet 1 174
cert_cover_5 1 0 0 1 2 4 142 174 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 550
cert_cover_2 3 1 0 4 8 38 550 3
cert_coverFacet 4 818
cert_cover_5 4 1 0 3 4 7 274 818 2
cert_coverFacet 5 466
cert_cover_5 5 2 0 3 5 6 146 466 2
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 852
cert_cover_5 7 3 1 3 5 7 84 852 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0180

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0181.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0181

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 29, 45, 405, 357, 569, 241, 782, 410, 666, 738, 834, 284, 620, 836, 688, 13, 21, 37, 261, 25, 41, 49, 145, 97, 193, 321, 385, 154, 266, 522, 194, 322, 578, 386, 642, 770, 28, 44, 268, 524, 276, 100, 324, 580, 772, 280, 536, 552, 176, 560, 400, 656, 224, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_29, vertices_45, vertices_405, vertices_357, vertices_569, vertices_241, vertices_782, vertices_410, vertices_666, vertices_738, vertices_834, vertices_284, vertices_620, vertices_836, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_37, vertices_261, vertices_25, vertices_41, vertices_49, vertices_145, vertices_97, vertices_193, vertices_321, vertices_385, vertices_154, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_524, vertices_276, vertices_100, vertices_324, vertices_580, vertices_772, vertices_280, vertices_536, vertices_552, vertices_176, vertices_560, vertices_400, vertices_656, vertices_224, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_29), (false, vertices_45), (false, vertices_405), (false, vertices_357), (false, vertices_569), (false, vertices_241), (true, vertices_154), (true, vertices_266), (true, vertices_522), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_268), (true, vertices_524), (true, vertices_580), (true, vertices_772), (true, vertices_280), (true, vertices_656), (true, vertices_608), (true, vertices_672), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 17 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_45) then 1 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (true, vertices_154) then 18 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_672) then 14 else
  if p.val = (true, vertices_832) then 15 else
  0
cert_priority
cert_nodeAtPriority_50 1 29 0 45 266 522 578 642 770 268 524 580 772 280 656 608 672 832 451 154 405 357 569 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 1 2 4 5 8 620 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 7 154 410 3
cert_coverFacet 2 666
cert_cover_5 2 0 0 2 3 8 154 666 3
cert_coverFacet 3 738
cert_cover_5 3 2 0 4 5 6 194 738 1
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 44 620 3
cert_coverFacet 7 836
cert_cover_2 7 5 1 7 8 324 836 3
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0181

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0182.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0182

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 565, 293, 709, 121, 593, 481, 654, 806, 282, 538, 458, 818, 312, 728, 360, 37, 133, 261, 517, 49, 81, 529, 97, 289, 193, 577, 385, 134, 262, 518, 26, 138, 266, 522, 274, 530, 802, 386, 292, 548, 644, 56, 88, 280, 536, 104, 296, 200, 328, 648, 304, 560, 592, 352, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_565, vertices_293, vertices_709, vertices_121, vertices_593, vertices_481, vertices_654, vertices_806, vertices_282, vertices_538, vertices_458, vertices_818, vertices_312, vertices_728, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_517, vertices_49, vertices_81, vertices_529, vertices_97, vertices_289, vertices_193, vertices_577, vertices_385, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_802, vertices_386, vertices_292, vertices_548, vertices_644, vertices_56, vertices_88, vertices_280, vertices_536, vertices_104, vertices_296, vertices_200, vertices_328, vertices_648, vertices_304, vertices_560, vertices_592, vertices_352, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_565), (false, vertices_293), (false, vertices_709), (false, vertices_121), (false, vertices_593), (false, vertices_481), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_802), (true, vertices_280), (true, vertices_536), (true, vertices_296), (true, vertices_200), (true, vertices_328), (true, vertices_648), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 17 else
  if p.val = (false, vertices_565) then 20 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_121) then 23 else
  if p.val = (false, vertices_593) then 1 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_274) then 7 else
  if p.val = (true, vertices_530) then 8 else
  if p.val = (true, vertices_802) then 18 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_304) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 1 293 0 593 518 26 138 266 522 274 530 280 536 296 200 328 648 304 391 802 565 709 121 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 7 8 802
cert_row_4 1 0 1 2 6 8 654 134 2
cert_row_4 2 0 2 5 6 7 458 138 2
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 4 1 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 134 654 2
cert_coverFacet 1 806
cert_cover_5 1 0 0 1 4 7 262 806 2
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 458
cert_cover_5 4 2 0 2 5 6 138 458 2
cert_coverFacet 5 818
cert_cover_5 5 0 0 3 4 7 274 818 2
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 728
cert_cover_5 7 3 2 3 5 6 88 728 3
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0182

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0183.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0183

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 651, 275, 451, 117, 709, 337, 426, 778, 786, 316, 796, 556, 612, 744, 496, 19, 131, 259, 515, 21, 69, 517, 81, 273, 193, 321, 641, 138, 266, 522, 274, 530, 386, 770, 284, 44, 524, 52, 532, 100, 548, 580, 168, 296, 552, 648, 776, 112, 304, 336, 784, 224, 608, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_651, vertices_275, vertices_451, vertices_117, vertices_709, vertices_337, vertices_426, vertices_778, vertices_786, vertices_316, vertices_796, vertices_556, vertices_612, vertices_744, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_21, vertices_69, vertices_517, vertices_81, vertices_273, vertices_193, vertices_321, vertices_641, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_386, vertices_770, vertices_284, vertices_44, vertices_524, vertices_52, vertices_532, vertices_100, vertices_548, vertices_580, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_112, vertices_304, vertices_336, vertices_784, vertices_224, vertices_608, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_651), (false, vertices_275), (false, vertices_451), (false, vertices_117), (false, vertices_709), (false, vertices_337), (true, vertices_266), (true, vertices_770), (true, vertices_284), (true, vertices_44), (true, vertices_524), (true, vertices_548), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_304), (true, vertices_784), (true, vertices_224), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 24 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 17 else
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_117) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_337) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_284) then 23 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_608) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
cert_nodeAtPriority_6 275 337 266 770 44 524 548 168 296 552 776 304 784 224 608 416 535 651 451 117 709 284
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 7 284
cert_row_4 1 0 2 4 6 7 426 138 2
cert_row_4 2 2 4 5 6 8 744 168 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 426
cert_cover_5 0 1 0 2 4 6 138 426 2
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 316
cert_cover_5 3 0 1 2 3 4 284 316 3
cert_coverFacet 4 796
cert_cover_5 4 0 1 2 3 8 284 796 3
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 744
cert_cover_5 7 2 2 4 5 6 168 744 2
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0183

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0184.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0184

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 157, 781, 597, 409, 865, 174, 362, 394, 210, 402, 738, 556, 692, 808, 720, 13, 21, 517, 153, 265, 81, 273, 321, 577, 769, 42, 138, 266, 82, 146, 274, 98, 162, 194, 322, 386, 44, 140, 524, 148, 532, 164, 548, 296, 552, 392, 776, 208, 592, 400, 656, 352, 608, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_157, vertices_781, vertices_597, vertices_409, vertices_865, vertices_174, vertices_362, vertices_394, vertices_210, vertices_402, vertices_738, vertices_556, vertices_692, vertices_808, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_517, vertices_153, vertices_265, vertices_81, vertices_273, vertices_321, vertices_577, vertices_769, vertices_42, vertices_138, vertices_266, vertices_82, vertices_146, vertices_274, vertices_98, vertices_162, vertices_194, vertices_322, vertices_386, vertices_44, vertices_140, vertices_524, vertices_148, vertices_532, vertices_164, vertices_548, vertices_296, vertices_552, vertices_392, vertices_776, vertices_208, vertices_592, vertices_400, vertices_656, vertices_352, vertices_608, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_157), (false, vertices_781), (false, vertices_597), (false, vertices_409), (false, vertices_865), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_98), (true, vertices_162), (true, vertices_194), (true, vertices_386), (true, vertices_44), (true, vertices_164), (true, vertices_548), (true, vertices_296), (true, vertices_552), (true, vertices_208), (true, vertices_656), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 18 else
  if p.val = (false, vertices_157) then 23 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_597) then 21 else
  if p.val = (false, vertices_409) then 24 else
  if p.val = (false, vertices_865) then 27 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_672) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
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
cert_row_4 0 0 2 4 5 7 362 42 3
cert_row_4 1 0 1 2 4 6 174 42 1
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 1 3 4 6 8 692 148 2
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 1 0 1 2 4 42 174 1
cert_coverFacet 1 362
cert_cover_5 1 0 0 2 4 5 42 362 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 98 738 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 692
cert_cover_5 7 3 1 3 4 6 148 692 2
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coverFacet 9 720
cert_cover_2 9 5 3 6 8 208 720 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0184

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0185.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0185

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 653, 421, 837, 409, 329, 182, 662, 550, 122, 538, 866, 804, 344, 664, 496, 133, 261, 517, 73, 137, 265, 521, 321, 577, 385, 150, 38, 518, 26, 74, 522, 50, 530, 98, 546, 578, 164, 292, 548, 644, 772, 88, 152, 280, 536, 328, 648, 112, 176, 336, 400, 656, 352, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_653, vertices_421, vertices_837, vertices_409, vertices_329, vertices_182, vertices_662, vertices_550, vertices_122, vertices_538, vertices_866, vertices_804, vertices_344, vertices_664, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_521, vertices_321, vertices_577, vertices_385, vertices_150, vertices_38, vertices_518, vertices_26, vertices_74, vertices_522, vertices_50, vertices_530, vertices_98, vertices_546, vertices_578, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_536, vertices_328, vertices_648, vertices_112, vertices_176, vertices_336, vertices_400, vertices_656, vertices_352, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_653), (false, vertices_421), (false, vertices_837), (false, vertices_409), (false, vertices_329), (true, vertices_150), (true, vertices_38), (true, vertices_518), (true, vertices_26), (true, vertices_50), (true, vertices_530), (true, vertices_98), (true, vertices_546), (true, vertices_548), (true, vertices_88), (true, vertices_536), (true, vertices_112), (true, vertices_176), (true, vertices_336), (true, vertices_656), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 18 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_421) then 22 else
  if p.val = (false, vertices_837) then 23 else
  if p.val = (false, vertices_409) then 25 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (true, vertices_150) then 19 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_352) then 15 else
  if p.val = (true, vertices_800) then 16 else
  0
cert_priority
cert_nodeAtPriority_63 329 38 518 26 50 530 98 546 548 88 536 112 176 336 656 352 800 587 150 653 421 837 409
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 6 150
cert_row_4 1 0 2 3 4 5 122 26 3
cert_row_4 2 0 4 5 7 8 866 98 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 4 150 182 3
cert_coverFacet 1 662
cert_cover_5 1 0 0 1 3 8 150 662 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 122
cert_cover_5 3 1 0 2 3 4 26 122 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 866
cert_cover_5 5 2 0 4 5 7 98 866 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coverFacet 9 496
cert_cover_5 9 3 3 4 5 6 112 496 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0185

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0186.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0186

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 397, 789, 313, 537, 713, 230, 806, 122, 562, 722, 484, 600, 360, 456, 816, 133, 261, 517, 25, 137, 265, 521, 273, 529, 641, 38, 134, 518, 50, 82, 530, 98, 546, 194, 642, 228, 292, 388, 772, 56, 88, 536, 104, 296, 200, 328, 584, 392, 304, 560, 592, 784, 352, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_397, vertices_789, vertices_313, vertices_537, vertices_713, vertices_230, vertices_806, vertices_122, vertices_562, vertices_722, vertices_484, vertices_600, vertices_360, vertices_456, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_137, vertices_265, vertices_521, vertices_273, vertices_529, vertices_641, vertices_38, vertices_134, vertices_518, vertices_50, vertices_82, vertices_530, vertices_98, vertices_546, vertices_194, vertices_642, vertices_228, vertices_292, vertices_388, vertices_772, vertices_56, vertices_88, vertices_536, vertices_104, vertices_296, vertices_200, vertices_328, vertices_584, vertices_392, vertices_304, vertices_560, vertices_592, vertices_784, vertices_352, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_397), (false, vertices_789), (false, vertices_313), (false, vertices_537), (false, vertices_713), (true, vertices_38), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_98), (true, vertices_546), (true, vertices_194), (true, vertices_228), (true, vertices_292), (true, vertices_88), (true, vertices_104), (true, vertices_328), (true, vertices_560), (true, vertices_592), (true, vertices_352), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 18 else
  if p.val = (false, vertices_397) then 20 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_313) then 24 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_713) then 25 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_228) then 22 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_800) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_228), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 38 3
cert_row_2 1 1 4 5 6 228
cert_row_4 2 0 2 3 4 5 122 50 1
cert_row_4 3 0 3 5 6 8 722 82 3
cert_rows
cert_pivot_2 7 1 2 0
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 1 0 1 4 5 38 230 3
cert_coverFacet 1 806
cert_cover_5 1 0 0 1 4 7 38 806 3
cert_coverFacet 2 122
cert_cover_5 2 2 0 2 3 4 50 122 1
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 722
cert_cover_5 4 3 0 3 5 6 82 722 3
cert_coverFacet 5 484
cert_cover_5 5 1 1 4 5 7 228 484 3
cert_coverFacet 6 600
cert_cover_2 6 3 2 5 8 88 600 3
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coverFacet 9 816
cert_cover_2 9 4 3 7 8 304 816 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0186

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0187.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0187

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 395, 275, 707, 117, 581, 465, 682, 778, 786, 316, 796, 556, 740, 488, 368, 19, 131, 259, 515, 21, 69, 517, 81, 273, 193, 577, 385, 138, 266, 522, 274, 530, 642, 770, 284, 44, 524, 52, 532, 100, 548, 580, 168, 296, 552, 392, 776, 112, 304, 336, 784, 224, 352, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_395, vertices_275, vertices_707, vertices_117, vertices_581, vertices_465, vertices_682, vertices_778, vertices_786, vertices_316, vertices_796, vertices_556, vertices_740, vertices_488, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_21, vertices_69, vertices_517, vertices_81, vertices_273, vertices_193, vertices_577, vertices_385, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_642, vertices_770, vertices_284, vertices_44, vertices_524, vertices_52, vertices_532, vertices_100, vertices_548, vertices_580, vertices_168, vertices_296, vertices_552, vertices_392, vertices_776, vertices_112, vertices_304, vertices_336, vertices_784, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_395), (false, vertices_275), (false, vertices_707), (false, vertices_117), (false, vertices_581), (false, vertices_465), (true, vertices_522), (true, vertices_770), (true, vertices_284), (true, vertices_44), (true, vertices_524), (true, vertices_548), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_304), (true, vertices_784), (true, vertices_224), (true, vertices_352), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 17 else
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_707) then 19 else
  if p.val = (false, vertices_117) then 21 else
  if p.val = (false, vertices_581) then 1 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_284) then 22 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_284), by decide +kernel⟩
  | 23 => Sum.inl 2
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
cert_row_2 0 1 2 3 7 284
cert_row_4 1 0 2 4 6 8 682 138 2
cert_row_4 2 1 4 5 6 8 740 100 3
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 682
cert_cover_5 0 1 0 2 4 6 138 682 2
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 316
cert_cover_5 3 0 1 2 3 4 284 316 3
cert_coverFacet 4 796
cert_cover_5 4 0 1 2 3 8 284 796 3
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 740
cert_cover_5 6 2 1 4 5 6 100 740 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 168 488 2
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0187

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0188.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0188

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 453, 121, 537, 425, 721, 353, 398, 806, 710, 282, 538, 818, 628, 356, 312, 25, 41, 137, 521, 81, 529, 97, 289, 193, 321, 385, 641, 134, 262, 518, 26, 138, 266, 522, 274, 530, 802, 642, 100, 292, 548, 196, 324, 580, 388, 56, 280, 536, 296, 392, 112, 304, 560, 592, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_453, vertices_121, vertices_537, vertices_425, vertices_721, vertices_353, vertices_398, vertices_806, vertices_710, vertices_282, vertices_538, vertices_818, vertices_628, vertices_356, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_137, vertices_521, vertices_81, vertices_529, vertices_97, vertices_289, vertices_193, vertices_321, vertices_385, vertices_641, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_802, vertices_642, vertices_100, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_56, vertices_280, vertices_536, vertices_296, vertices_392, vertices_112, vertices_304, vertices_560, vertices_592, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_453), (false, vertices_121), (false, vertices_537), (false, vertices_425), (false, vertices_721), (false, vertices_353), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_266), (true, vertices_274), (true, vertices_530), (true, vertices_802), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_580), (true, vertices_280), (true, vertices_304), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 17 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_121) then 22 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_425) then 23 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (false, vertices_353) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_274) then 7 else
  if p.val = (true, vertices_530) then 8 else
  if p.val = (true, vertices_802) then 18 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_580) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_560) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_802), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_2 1 0 4 7 8 802
cert_row_4 2 0 1 5 6 8 710 134 2
cert_row_4 3 1 3 4 5 8 628 100 1
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 806
cert_cover_5 1 1 0 1 4 7 262 806 2
cert_coverFacet 2 710
cert_cover_5 2 2 0 1 5 6 134 710 2
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 818
cert_cover_5 5 1 0 3 4 7 274 818 2
cert_coverFacet 6 628
cert_cover_5 6 3 1 3 4 5 100 628 1
cert_coverFacet 7 356
cert_cover_2 7 4 1 5 7 100 356 3
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0188

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0189.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0189

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 107, 779, 789, 325, 425, 353, 58, 538, 690, 738, 412, 724, 484, 184, 792, 11, 67, 515, 69, 261, 517, 41, 265, 97, 289, 321, 769, 26, 42, 522, 50, 530, 98, 674, 578, 148, 276, 532, 196, 324, 580, 388, 56, 152, 280, 536, 168, 392, 776, 176, 656, 784, 224, 352, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_107, vertices_779, vertices_789, vertices_325, vertices_425, vertices_353, vertices_58, vertices_538, vertices_690, vertices_738, vertices_412, vertices_724, vertices_484, vertices_184, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_515, vertices_69, vertices_261, vertices_517, vertices_41, vertices_265, vertices_97, vertices_289, vertices_321, vertices_769, vertices_26, vertices_42, vertices_522, vertices_50, vertices_530, vertices_98, vertices_674, vertices_578, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_580, vertices_388, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_392, vertices_776, vertices_176, vertices_656, vertices_784, vertices_224, vertices_352, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_107), (false, vertices_779), (false, vertices_789), (false, vertices_325), (false, vertices_425), (false, vertices_353), (true, vertices_26), (true, vertices_50), (true, vertices_530), (true, vertices_674), (true, vertices_148), (true, vertices_196), (true, vertices_388), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_176), (true, vertices_656), (true, vertices_224), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 16 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 17 else
  if p.val = (false, vertices_107) then 20 else
  if p.val = (false, vertices_779) then 21 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_425) then 24 else
  if p.val = (false, vertices_353) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_674) then 22 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_674), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 6 8 674
cert_row_4 1 1 2 3 6 7 412 148 1
cert_row_4 2 1 3 5 6 8 724 148 2
cert_row_4 3 1 4 5 6 7 484 196 1
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 58
cert_cover_2 0 2 0 3 4 26 58 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 690
cert_cover_5 2 0 0 3 4 6 50 690 3
cert_coverFacet 3 738
cert_cover_5 3 0 0 4 5 6 98 738 3
cert_coverFacet 4 412
cert_cover_5 4 1 1 2 3 6 148 412 1
cert_coverFacet 5 724
cert_cover_5 5 2 1 3 5 6 148 724 2
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 196 484 1
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 792
cert_cover_2 8 3 2 7 8 280 792 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0189

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0190.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0190

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 523, 787, 205, 837, 649, 737, 682, 298, 626, 306, 412, 244, 340, 440, 848, 11, 259, 515, 13, 69, 261, 137, 521, 193, 577, 641, 769, 42, 266, 522, 50, 274, 530, 290, 546, 140, 268, 84, 148, 276, 196, 324, 408, 168, 296, 648, 112, 176, 304, 336, 592, 784, 224, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_523, vertices_787, vertices_205, vertices_837, vertices_649, vertices_737, vertices_682, vertices_298, vertices_626, vertices_306, vertices_412, vertices_244, vertices_340, vertices_440, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_259, vertices_515, vertices_13, vertices_69, vertices_261, vertices_137, vertices_521, vertices_193, vertices_577, vertices_641, vertices_769, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_140, vertices_268, vertices_84, vertices_148, vertices_276, vertices_196, vertices_324, vertices_408, vertices_168, vertices_296, vertices_648, vertices_112, vertices_176, vertices_304, vertices_336, vertices_592, vertices_784, vertices_224, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_523), (false, vertices_787), (false, vertices_205), (false, vertices_837), (false, vertices_649), (false, vertices_737), (true, vertices_42), (true, vertices_50), (true, vertices_290), (true, vertices_546), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_408), (true, vertices_168), (true, vertices_296), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_336), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 17 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_205) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_649) then 1 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_408) then 23 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_592) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
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
cert_row_2 0 2 3 6 7 408
cert_row_4 1 0 2 4 6 8 682 42 3
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 1 3 4 5 6 244 84 2
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 682
cert_cover_5 0 1 0 2 4 6 42 682 3
cert_coverFacet 1 298
cert_cover_2 1 2 0 4 7 42 298 3
cert_coverFacet 2 626
cert_cover_5 2 2 0 3 4 5 50 626 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 412
cert_cover_5 4 0 1 2 3 6 140 412 2
cert_coverFacet 5 244
cert_cover_5 5 3 1 3 4 5 84 244 2
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 440
cert_cover_5 7 0 2 3 4 6 408 440 2
cert_coverFacet 8 848
cert_cover_2 8 5 3 7 8 336 848 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0190

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0191.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0191

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 341, 805, 581, 713, 481, 94, 654, 534, 58, 170, 818, 588, 788, 440, 472, 69, 261, 517, 161, 289, 545, 193, 321, 577, 641, 14, 22, 518, 26, 42, 138, 50, 530, 162, 546, 642, 76, 524, 84, 276, 532, 580, 772, 56, 88, 408, 168, 200, 584, 648, 304, 336, 784, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_341, vertices_805, vertices_581, vertices_713, vertices_481, vertices_94, vertices_654, vertices_534, vertices_58, vertices_170, vertices_818, vertices_588, vertices_788, vertices_440, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_14, vertices_22, vertices_518, vertices_26, vertices_42, vertices_138, vertices_50, vertices_530, vertices_162, vertices_546, vertices_642, vertices_76, vertices_524, vertices_84, vertices_276, vertices_532, vertices_580, vertices_772, vertices_56, vertices_88, vertices_408, vertices_168, vertices_200, vertices_584, vertices_648, vertices_304, vertices_336, vertices_784, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_341), (false, vertices_805), (false, vertices_581), (false, vertices_713), (false, vertices_481), (true, vertices_14), (true, vertices_22), (true, vertices_518), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_50), (true, vertices_530), (true, vertices_76), (true, vertices_524), (true, vertices_532), (true, vertices_56), (true, vertices_88), (true, vertices_408), (true, vertices_168), (true, vertices_304), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 18 else
  if p.val = (false, vertices_341) then 20 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_713) then 23 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_138) then 6 else
  if p.val = (true, vertices_50) then 7 else
  if p.val = (true, vertices_530) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_88) then 13 else
  if p.val = (true, vertices_408) then 24 else
  if p.val = (true, vertices_168) then 14 else
  if p.val = (true, vertices_304) then 15 else
  if p.val = (true, vertices_784) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 5 94 14 3
cert_row_4 1 0 1 2 6 8 654 14 3
cert_row_2 2 2 3 6 7 408
cert_row_4 3 0 3 4 7 8 818 50 3
cert_rows
cert_pivot_2 5 1 2 0
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 14 94 3
cert_coverFacet 1 654
cert_cover_5 1 1 0 1 2 6 14 654 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 58
cert_cover_2 3 2 0 3 4 26 58 3
cert_coverFacet 4 170
cert_cover_2 4 2 0 4 6 42 170 3
cert_coverFacet 5 818
cert_cover_5 5 3 0 3 4 7 50 818 3
cert_coverFacet 6 588
cert_cover_2 6 2 1 5 8 76 588 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 440
cert_cover_5 8 2 2 3 4 6 56 440 3
cert_coverFacet 9 472
cert_cover_5 9 2 2 3 5 6 88 472 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0191

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0192.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0192

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 587, 355, 387, 181, 613, 417, 346, 394, 650, 796, 908, 564, 404, 632, 496, 67, 131, 259, 515, 37, 133, 517, 97, 161, 289, 577, 385, 74, 138, 266, 522, 322, 386, 642, 780, 52, 148, 276, 532, 548, 388, 644, 88, 280, 536, 584, 392, 648, 112, 176, 560, 336, 400, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_587, vertices_355, vertices_387, vertices_181, vertices_613, vertices_417, vertices_346, vertices_394, vertices_650, vertices_796, vertices_908, vertices_564, vertices_404, vertices_632, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_37, vertices_133, vertices_517, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_74, vertices_138, vertices_266, vertices_522, vertices_322, vertices_386, vertices_642, vertices_780, vertices_52, vertices_148, vertices_276, vertices_532, vertices_548, vertices_388, vertices_644, vertices_88, vertices_280, vertices_536, vertices_584, vertices_392, vertices_648, vertices_112, vertices_176, vertices_560, vertices_336, vertices_400, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_587), (false, vertices_355), (false, vertices_387), (false, vertices_181), (false, vertices_613), (false, vertices_417), (true, vertices_138), (true, vertices_266), (true, vertices_780), (true, vertices_276), (true, vertices_532), (true, vertices_388), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_392), (true, vertices_648), (true, vertices_112), (true, vertices_560), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 24 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 17 else
  if p.val = (false, vertices_587) then 18 else
  if p.val = (false, vertices_355) then 19 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_181) then 21 else
  if p.val = (false, vertices_613) then 22 else
  if p.val = (false, vertices_417) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_780) then 23 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
cert_nodeAtPriority_6 387 417 138 266 276 532 388 88 280 536 392 648 112 560 336 400 647 587 355 181 613 780
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 7 8 780
cert_row_4 1 0 2 3 5 7 346 74 2
cert_row_4 2 2 3 4 5 8 632 88 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 346
cert_cover_5 0 1 0 2 3 5 74 346 2
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 796
cert_cover_5 3 0 1 2 3 7 780 796 2
cert_coverFacet 4 908
cert_cover_5 4 0 1 2 6 7 780 908 2
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 632
cert_cover_5 7 2 2 3 4 5 88 632 2
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0192

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_4053 : Certifies 4053 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0163.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4054 : Certifies 4054 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0164.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4055 : Certifies 4055 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0165.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4056 : Certifies 4056 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0166.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4057 : Certifies 4057 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0167.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4058 : Certifies 4058 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0168.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4059 : Certifies 4059 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0169.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4060 : Certifies 4060 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0170.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4061 : Certifies 4061 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0171.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4062 : Certifies 4062 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0172.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4063 : Certifies 4063 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0173.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4064 : Certifies 4064 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0174.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4065 : Certifies 4065 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0175.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4066 : Certifies 4066 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0176.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4067 : Certifies 4067 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0177.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4068 : Certifies 4068 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0178.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4069 : Certifies 4069 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0179.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4070 : Certifies 4070 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0180.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4071 : Certifies 4071 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0181.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4072 : Certifies 4072 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0182.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4073 : Certifies 4073 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0183.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4074 : Certifies 4074 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0184.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4075 : Certifies 4075 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0185.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4076 : Certifies 4076 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0186.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4077 : Certifies 4077 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0187.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4078 : Certifies 4078 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0188.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4079 : Certifies 4079 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0189.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4080 : Certifies 4080 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0190.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4081 : Certifies 4081 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0191.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4082 : Certifies 4082 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0192.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B134 (j : Fin 30) :
    Certifies (4053 + j.val) := by
  fin_cases j
  · exact projection_4053
  · exact projection_4054
  · exact projection_4055
  · exact projection_4056
  · exact projection_4057
  · exact projection_4058
  · exact projection_4059
  · exact projection_4060
  · exact projection_4061
  · exact projection_4062
  · exact projection_4063
  · exact projection_4064
  · exact projection_4065
  · exact projection_4066
  · exact projection_4067
  · exact projection_4068
  · exact projection_4069
  · exact projection_4070
  · exact projection_4071
  · exact projection_4072
  · exact projection_4073
  · exact projection_4074
  · exact projection_4075
  · exact projection_4076
  · exact projection_4077
  · exact projection_4078
  · exact projection_4079
  · exact projection_4080
  · exact projection_4081
  · exact projection_4082

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
