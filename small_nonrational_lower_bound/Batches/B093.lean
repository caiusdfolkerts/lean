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
/- Source: ProjectionCertificates/R_m15e10q1_0211.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0211

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 285, 109, 565, 329, 785, 737, 410, 722, 786, 482, 668, 684, 360, 424, 13, 21, 37, 73, 265, 273, 529, 97, 545, 321, 577, 769, 146, 274, 530, 194, 322, 578, 386, 770, 28, 44, 652, 532, 548, 152, 280, 104, 168, 296, 328, 392, 656, 784, 224, 352, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_285, vertices_109, vertices_565, vertices_329, vertices_785, vertices_737, vertices_410, vertices_722, vertices_786, vertices_482, vertices_668, vertices_684, vertices_360, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_37, vertices_73, vertices_265, vertices_273, vertices_529, vertices_97, vertices_545, vertices_321, vertices_577, vertices_769, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_28, vertices_44, vertices_652, vertices_532, vertices_548, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_328, vertices_392, vertices_656, vertices_784, vertices_224, vertices_352, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_285), (false, vertices_109), (false, vertices_565), (false, vertices_329), (false, vertices_785), (false, vertices_737), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_386), (true, vertices_652), (true, vertices_152), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_656), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 19 22 16 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 15 else
  if p.val = (false, vertices_285) then 17 else
  if p.val = (false, vertices_109) then 20 else
  if p.val = (false, vertices_565) then 18 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_785) then 1 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_652) then 21 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 8 652
cert_row_4 1 0 2 3 6 7 410 146 1
cert_row_4 2 0 3 5 6 8 722 146 2
cert_row_4 3 0 4 5 6 7 482 194 1
cert_rows
cert_pivot_2 1 2 3 0
cert_heightProof 4
cert_coverFacet 0 410
cert_cover_5 0 1 0 2 3 6 146 410 1
cert_coverFacet 1 722
cert_cover_5 1 2 0 3 5 6 146 722 2
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 482
cert_cover_5 3 3 0 4 5 6 194 482 1
cert_coverFacet 4 668
cert_cover_5 4 0 1 2 3 6 28 668 3
cert_coverFacet 5 684
cert_cover_5 5 0 1 2 4 6 44 684 3
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0211

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0212.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0212

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 805, 233, 905, 625, 417, 206, 526, 566, 214, 594, 412, 780, 308, 496, 73, 137, 521, 97, 161, 289, 545, 577, 385, 769, 14, 22, 198, 518, 74, 522, 82, 530, 578, 140, 268, 524, 52, 148, 276, 292, 548, 772, 200, 392, 776, 112, 304, 560, 208, 592, 400, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_805, vertices_233, vertices_905, vertices_625, vertices_417, vertices_206, vertices_526, vertices_566, vertices_214, vertices_594, vertices_412, vertices_780, vertices_308, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_521, vertices_97, vertices_161, vertices_289, vertices_545, vertices_577, vertices_385, vertices_769, vertices_14, vertices_22, vertices_198, vertices_518, vertices_74, vertices_522, vertices_82, vertices_530, vertices_578, vertices_140, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_292, vertices_548, vertices_772, vertices_200, vertices_392, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_592, vertices_400, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_805), (false, vertices_233), (false, vertices_905), (false, vertices_625), (false, vertices_417), (true, vertices_14), (true, vertices_22), (true, vertices_198), (true, vertices_518), (true, vertices_82), (true, vertices_530), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_304), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 16 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_905) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_198) then 17 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 417 14 22 518 82 530 140 268 524 52 148 276 304 208 400 587 198 805 233 905 625
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
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0212

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0213.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0213

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 781, 681, 457, 241, 609, 214, 278, 454, 626, 786, 188, 556, 396, 820, 137, 265, 521, 97, 161, 545, 193, 321, 577, 769, 22, 198, 262, 82, 274, 530, 322, 578, 770, 44, 140, 268, 524, 52, 148, 276, 548, 388, 772, 168, 552, 392, 112, 176, 560, 208, 784, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_781, vertices_681, vertices_457, vertices_241, vertices_609, vertices_214, vertices_278, vertices_454, vertices_626, vertices_786, vertices_188, vertices_556, vertices_396, vertices_820] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_769, vertices_22, vertices_198, vertices_262, vertices_82, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_44, vertices_140, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_548, vertices_388, vertices_772, vertices_168, vertices_552, vertices_392, vertices_112, vertices_176, vertices_560, vertices_208, vertices_784, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_781), (false, vertices_681), (false, vertices_457), (false, vertices_241), (false, vertices_609), (true, vertices_22), (true, vertices_198), (true, vertices_262), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_44), (true, vertices_140), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_548), (true, vertices_388), (true, vertices_560), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (false, vertices_609) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_198) then 17 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_784) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 609 22 262 82 274 530 44 140 52 148 276 548 388 560 784 835 198 781 681 457 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 4 6 188 44 2
cert_row_2 1 0 1 5 6 198
cert_row_4 2 0 3 4 5 8 626 82 2
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 1 0 1 3 5 22 214 3
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 454
cert_cover_5 2 1 0 1 5 7 198 454 3
cert_coverFacet 3 626
cert_cover_5 3 2 0 3 4 5 82 626 2
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 188
cert_cover_5 5 0 1 2 3 4 44 188 2
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 396
cert_cover_2 7 2 1 6 7 140 396 3
cert_coverFacet 8 820
cert_cover_5 8 3 1 3 4 7 52 820 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0213

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0214.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0214

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 149, 789, 677, 409, 481, 609, 46, 526, 614, 794, 234, 458, 188, 540, 21, 133, 517, 145, 273, 97, 161, 545, 321, 577, 385, 769, 14, 38, 518, 42, 202, 266, 522, 98, 322, 578, 770, 28, 44, 524, 148, 532, 164, 548, 152, 280, 536, 168, 392, 784, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_149, vertices_789, vertices_677, vertices_409, vertices_481, vertices_609, vertices_46, vertices_526, vertices_614, vertices_794, vertices_234, vertices_458, vertices_188, vertices_540] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_145, vertices_273, vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_769, vertices_14, vertices_38, vertices_518, vertices_42, vertices_202, vertices_266, vertices_522, vertices_98, vertices_322, vertices_578, vertices_770, vertices_28, vertices_44, vertices_524, vertices_148, vertices_532, vertices_164, vertices_548, vertices_152, vertices_280, vertices_536, vertices_168, vertices_392, vertices_784, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_149), (false, vertices_789), (false, vertices_677), (false, vertices_409), (false, vertices_481), (false, vertices_609), (true, vertices_14), (true, vertices_38), (true, vertices_518), (true, vertices_42), (true, vertices_202), (true, vertices_266), (true, vertices_522), (true, vertices_98), (true, vertices_28), (true, vertices_44), (true, vertices_524), (true, vertices_536), (true, vertices_168)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 15 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (false, vertices_609) then 1 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_38) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_202) then 16 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_522) then 7 else
  if p.val = (true, vertices_98) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_44) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_168) then 13 else
  0
cert_priority
cert_nodeAtPriority_53 0 149 1 609 14 38 518 42 266 522 98 28 44 524 536 168 835 202 789 677 409 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 7 8 794 266 2
cert_row_4 1 0 1 4 5 8 614 38 3
cert_row_2 2 0 2 5 6 202
cert_row_4 3 1 2 3 4 6 188 28 3
cert_rows
cert_pivot_2 7 8 0 1
cert_heightProof 4
cert_coverFacet 0 46
cert_cover_2 0 1 0 2 4 14 46 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 614
cert_cover_5 2 1 0 1 4 5 38 614 3
cert_coverFacet 3 794
cert_cover_5 3 0 0 2 3 7 266 794 2
cert_coverFacet 4 234
cert_cover_5 4 2 0 2 4 5 42 234 3
cert_coverFacet 5 458
cert_cover_5 5 2 0 2 5 7 202 458 3
cert_coverFacet 6 188
cert_cover_5 6 3 1 2 3 4 28 188 3
cert_coverFacet 7 540
cert_cover_2 7 2 1 3 8 28 540 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0214

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0215.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0215

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [15, 583, 779, 93, 457, 737, 897, 286, 310, 550, 930, 244, 612, 440, 216, 7, 11, 515, 13, 69, 73, 265, 193, 577, 385, 641, 769, 14, 278, 38, 518, 266, 290, 546, 770, 28, 52, 84, 100, 548, 580, 88, 152, 280, 200, 392, 176, 304, 208, 224, 608, 416, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_15, vertices_583, vertices_779, vertices_93, vertices_457, vertices_737, vertices_897, vertices_286, vertices_310, vertices_550, vertices_930, vertices_244, vertices_612, vertices_440, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_13, vertices_69, vertices_73, vertices_265, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_278, vertices_38, vertices_518, vertices_266, vertices_290, vertices_546, vertices_770, vertices_28, vertices_52, vertices_84, vertices_100, vertices_548, vertices_580, vertices_88, vertices_152, vertices_280, vertices_200, vertices_392, vertices_176, vertices_304, vertices_208, vertices_224, vertices_608, vertices_416, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_15), (false, vertices_583), (false, vertices_779), (false, vertices_93), (false, vertices_457), (false, vertices_737), (false, vertices_897), (true, vertices_278), (true, vertices_38), (true, vertices_290), (true, vertices_546), (true, vertices_52), (true, vertices_100), (true, vertices_548), (true, vertices_152), (true, vertices_280), (true, vertices_176), (true, vertices_304), (true, vertices_208), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_15) then 0 else
  if p.val = (false, vertices_583) then 15 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_93) then 19 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_278) then 17 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_15), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_278), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 6 7 8 930 290 2
cert_row_2 1 0 1 3 7 278
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_4 3 2 3 4 6 7 440 152 2
cert_rows
cert_pivot_2 8 0 1 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 1 0 1 2 3 14 286 3
cert_coverFacet 1 310
cert_cover_5 1 1 0 1 3 4 278 310 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 930
cert_cover_5 3 0 0 4 6 7 290 930 2
cert_coverFacet 4 244
cert_cover_5 4 2 1 3 4 5 52 244 3
cert_coverFacet 5 612
cert_cover_2 5 4 1 5 8 100 612 3
cert_coverFacet 6 440
cert_cover_5 6 3 2 3 4 6 152 440 2
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0215

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0216.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0216

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 333, 653, 581, 425, 465, 598, 682, 818, 210, 402, 418, 316, 572, 340, 13, 69, 517, 137, 265, 193, 321, 577, 385, 641, 82, 146, 274, 530, 162, 290, 546, 194, 578, 386, 642, 60, 268, 524, 84, 276, 532, 324, 580, 168, 296, 552, 648, 304, 560, 208, 336, 400, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_333, vertices_653, vertices_581, vertices_425, vertices_465, vertices_598, vertices_682, vertices_818, vertices_210, vertices_402, vertices_418, vertices_316, vertices_572, vertices_340] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_137, vertices_265, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_82, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_194, vertices_578, vertices_386, vertices_642, vertices_60, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_324, vertices_580, vertices_168, vertices_296, vertices_552, vertices_648, vertices_304, vertices_560, vertices_208, vertices_336, vertices_400, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_333), (false, vertices_653), (false, vertices_581), (false, vertices_425), (false, vertices_465), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_60), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_552), (true, vertices_304), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 23 17 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_333) then 21 else
  if p.val = (false, vertices_653) then 22 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_425) then 24 else
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
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_560) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 581 1 82 3 146 2 274 530 162 290 546 386 84 276 532 552 304 560 707 465 60 333 653 425
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 82 1
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 2 4 6 8 682 162 1
cert_row_4 3 0 3 4 7 8 818 274 2
cert_rows
cert_pivot_2 5 1 2 0
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 82 598 1
cert_coverFacet 1 682
cert_cover_5 1 2 0 2 4 6 162 682 1
cert_coverFacet 2 818
cert_cover_5 2 3 0 3 4 7 274 818 2
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 316
cert_cover_5 6 1 1 2 3 7 60 316 3
cert_coverFacet 7 572
cert_cover_5 7 1 1 2 3 8 60 572 3
cert_coverFacet 8 340
cert_cover_2 8 3 1 5 7 84 340 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0216

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0217.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0217

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 789, 421, 681, 625, 305, 334, 782, 198, 234, 650, 452, 856, 616, 496, 133, 261, 517, 49, 273, 529, 161, 289, 545, 641, 270, 70, 134, 518, 74, 138, 522, 194, 642, 196, 324, 388, 772, 104, 168, 552, 328, 584, 648, 776, 112, 304, 336, 592, 784, 224, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_789, vertices_421, vertices_681, vertices_625, vertices_305, vertices_334, vertices_782, vertices_198, vertices_234, vertices_650, vertices_452, vertices_856, vertices_616, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_270, vertices_70, vertices_134, vertices_518, vertices_74, vertices_138, vertices_522, vertices_194, vertices_642, vertices_196, vertices_324, vertices_388, vertices_772, vertices_104, vertices_168, vertices_552, vertices_328, vertices_584, vertices_648, vertices_776, vertices_112, vertices_304, vertices_336, vertices_592, vertices_784, vertices_224, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_789), (false, vertices_421), (false, vertices_681), (false, vertices_625), (false, vertices_305), (true, vertices_270), (true, vertices_70), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_194), (true, vertices_196), (true, vertices_324), (true, vertices_104), (true, vertices_328), (true, vertices_584), (true, vertices_776), (true, vertices_336), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (true, vertices_270) then 17 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 305 70 74 138 522 194 196 324 104 328 584 776 336 224 448 647 270 789 421 681 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 7 270
cert_row_4 1 0 2 4 5 6 234 74 2
cert_row_4 2 2 3 5 7 8 856 328 1
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 270 334 3
cert_coverFacet 1 782
cert_cover_5 1 0 0 1 2 8 270 782 3
cert_coverFacet 2 198
cert_cover_2 2 1 0 5 6 70 198 3
cert_coverFacet 3 234
cert_cover_5 3 1 0 2 4 5 74 234 2
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 452
cert_cover_2 5 5 1 6 7 196 452 3
cert_coverFacet 6 856
cert_cover_5 6 2 2 3 5 7 328 856 1
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0217

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0218.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0218

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 653, 421, 617, 169, 817, 214, 534, 454, 370, 786, 660, 728, 488, 624, 133, 261, 517, 41, 137, 521, 161, 289, 545, 769, 22, 198, 262, 518, 82, 274, 530, 322, 770, 148, 532, 388, 644, 104, 168, 200, 584, 648, 112, 304, 560, 208, 592, 656, 784, 352, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_653, vertices_421, vertices_617, vertices_169, vertices_817, vertices_214, vertices_534, vertices_454, vertices_370, vertices_786, vertices_660, vertices_728, vertices_488, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_137, vertices_521, vertices_161, vertices_289, vertices_545, vertices_769, vertices_22, vertices_198, vertices_262, vertices_518, vertices_82, vertices_274, vertices_530, vertices_322, vertices_770, vertices_148, vertices_532, vertices_388, vertices_644, vertices_104, vertices_168, vertices_200, vertices_584, vertices_648, vertices_112, vertices_304, vertices_560, vertices_208, vertices_592, vertices_656, vertices_784, vertices_352, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_653), (false, vertices_421), (false, vertices_617), (false, vertices_169), (false, vertices_817), (true, vertices_22), (true, vertices_198), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_322), (true, vertices_148), (true, vertices_532), (true, vertices_200), (true, vertices_112), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_352), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_198) then 17 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 169 22 82 274 530 322 148 532 200 112 208 592 656 352 448 775 198 653 421 617 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_4 1 0 3 4 5 7 370 82 2
cert_row_4 2 2 3 5 6 8 728 200 1
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 1 0 3 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 454
cert_cover_5 2 0 0 1 5 7 198 454 3
cert_coverFacet 3 370
cert_cover_5 3 1 0 3 4 5 82 370 2
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 660
cert_cover_2 5 3 1 6 8 148 660 3
cert_coverFacet 6 728
cert_cover_5 6 2 2 3 5 6 200 728 1
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coverFacet 8 624
cert_cover_2 8 4 3 5 8 112 624 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0218

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0219.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0219

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 709, 361, 681, 585, 433, 182, 790, 198, 838, 402, 572, 676, 312, 856, 41, 73, 521, 161, 289, 193, 321, 577, 385, 641, 22, 70, 134, 774, 146, 274, 194, 322, 386, 52, 532, 164, 548, 196, 580, 644, 56, 280, 536, 296, 552, 328, 584, 176, 304, 400, 784, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_709, vertices_361, vertices_681, vertices_585, vertices_433, vertices_182, vertices_790, vertices_198, vertices_838, vertices_402, vertices_572, vertices_676, vertices_312, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_521, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_22, vertices_70, vertices_134, vertices_774, vertices_146, vertices_274, vertices_194, vertices_322, vertices_386, vertices_52, vertices_532, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_280, vertices_536, vertices_296, vertices_552, vertices_328, vertices_584, vertices_176, vertices_304, vertices_400, vertices_784, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_709), (false, vertices_361), (false, vertices_681), (false, vertices_585), (false, vertices_433), (true, vertices_22), (true, vertices_70), (true, vertices_134), (true, vertices_774), (true, vertices_146), (true, vertices_274), (true, vertices_52), (true, vertices_532), (true, vertices_164), (true, vertices_548), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_774) then 17 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 585 22 70 134 146 274 52 532 164 548 56 280 536 784 832 451 774 709 361 681 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 6 182 22 3
cert_row_2 1 0 1 7 8 774
cert_row_4 2 1 2 3 4 8 572 52 1
cert_row_4 3 2 3 5 7 8 856 280 2
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 4 22 182 3
cert_coverFacet 1 790
cert_cover_5 1 1 0 1 3 7 22 790 3
cert_coverFacet 2 198
cert_cover_2 2 1 0 5 6 70 198 3
cert_coverFacet 3 838
cert_cover_5 3 1 0 1 5 7 70 838 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 572
cert_cover_5 5 2 1 2 3 4 52 572 1
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 856
cert_cover_5 8 3 2 3 5 7 280 856 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0219

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0220.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0220

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 677, 361, 553, 713, 433, 182, 790, 198, 838, 402, 572, 708, 312, 856, 41, 73, 521, 161, 289, 545, 193, 321, 385, 641, 22, 70, 134, 774, 146, 274, 194, 322, 386, 52, 532, 164, 548, 196, 580, 644, 56, 280, 536, 296, 552, 328, 584, 176, 304, 400, 784, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_677, vertices_361, vertices_553, vertices_713, vertices_433, vertices_182, vertices_790, vertices_198, vertices_838, vertices_402, vertices_572, vertices_708, vertices_312, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_521, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_22, vertices_70, vertices_134, vertices_774, vertices_146, vertices_274, vertices_194, vertices_322, vertices_386, vertices_52, vertices_532, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_280, vertices_536, vertices_296, vertices_552, vertices_328, vertices_584, vertices_176, vertices_304, vertices_400, vertices_784, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_677), (false, vertices_361), (false, vertices_553), (false, vertices_713), (false, vertices_433), (true, vertices_22), (true, vertices_70), (true, vertices_134), (true, vertices_774), (true, vertices_146), (true, vertices_274), (true, vertices_52), (true, vertices_532), (true, vertices_196), (true, vertices_580), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_774) then 17 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 553 22 70 134 146 274 52 532 196 580 56 280 536 784 832 451 774 677 361 713 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 6 182 22 3
cert_row_2 1 0 1 7 8 774
cert_row_4 2 1 2 3 4 8 572 52 1
cert_row_4 3 2 3 5 7 8 856 280 2
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 4 22 182 3
cert_coverFacet 1 790
cert_cover_5 1 1 0 1 3 7 22 790 3
cert_coverFacet 2 198
cert_cover_2 2 1 0 5 6 70 198 3
cert_coverFacet 3 838
cert_cover_5 3 1 0 1 5 7 70 838 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 572
cert_cover_5 5 2 1 2 3 4 52 572 1
cert_coverFacet 6 708
cert_cover_2 6 5 1 6 8 196 708 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 856
cert_cover_5 8 3 2 3 5 7 280 856 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0220

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0221.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0221

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 453, 617, 425, 849, 225, 398, 654, 342, 534, 786, 244, 660, 696, 624, 41, 265, 521, 97, 161, 193, 321, 577, 385, 769, 142, 22, 262, 518, 266, 522, 274, 530, 770, 84, 148, 532, 196, 324, 388, 644, 168, 552, 392, 648, 112, 176, 560, 336, 592, 656, 784, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_453, vertices_617, vertices_425, vertices_849, vertices_225, vertices_398, vertices_654, vertices_342, vertices_534, vertices_786, vertices_244, vertices_660, vertices_696, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_265, vertices_521, vertices_97, vertices_161, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_142, vertices_22, vertices_262, vertices_518, vertices_266, vertices_522, vertices_274, vertices_530, vertices_770, vertices_84, vertices_148, vertices_532, vertices_196, vertices_324, vertices_388, vertices_644, vertices_168, vertices_552, vertices_392, vertices_648, vertices_112, vertices_176, vertices_560, vertices_336, vertices_592, vertices_656, vertices_784, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_453), (false, vertices_617), (false, vertices_425), (false, vertices_849), (false, vertices_225), (true, vertices_142), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_274), (true, vertices_530), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_644), (true, vertices_648), (true, vertices_112), (true, vertices_176), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (false, vertices_225) then 0 else
  if p.val = (true, vertices_142) then 17 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 225 22 262 518 274 530 84 148 532 644 648 112 176 560 656 779 142 453 617 425 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 22 3
cert_row_2 1 0 1 2 6 142
cert_row_4 2 1 3 4 5 6 244 84 2
cert_row_4 3 2 3 4 6 8 696 168 1
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 7 142 398 3
cert_coverFacet 1 654
cert_cover_5 1 1 0 1 2 8 142 654 3
cert_coverFacet 2 342
cert_cover_5 2 0 0 1 3 5 22 342 3
cert_coverFacet 3 534
cert_cover_2 3 1 0 3 8 22 534 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 244
cert_cover_5 5 2 1 3 4 5 84 244 2
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 696
cert_cover_5 7 3 2 3 4 6 168 696 1
cert_coverFacet 8 624
cert_cover_2 8 4 3 5 8 112 624 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0221

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0222.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0222

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 781, 409, 681, 721, 302, 118, 534, 774, 466, 482, 556, 596, 740, 424, 137, 265, 521, 145, 273, 529, 641, 769, 22, 38, 262, 518, 82, 274, 530, 98, 290, 450, 770, 44, 268, 524, 84, 532, 100, 548, 580, 772, 168, 296, 552, 392, 208, 592, 400, 224, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_781, vertices_409, vertices_681, vertices_721, vertices_302, vertices_118, vertices_534, vertices_774, vertices_466, vertices_482, vertices_556, vertices_596, vertices_740, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_641, vertices_769, vertices_22, vertices_38, vertices_262, vertices_518, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_450, vertices_770, vertices_44, vertices_268, vertices_524, vertices_84, vertices_532, vertices_100, vertices_548, vertices_580, vertices_772, vertices_168, vertices_296, vertices_552, vertices_392, vertices_208, vertices_592, vertices_400, vertices_224, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_781), (false, vertices_409), (false, vertices_681), (false, vertices_721), (true, vertices_22), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_82), (true, vertices_98), (true, vertices_290), (true, vertices_450), (true, vertices_44), (true, vertices_84), (true, vertices_532), (true, vertices_100), (true, vertices_548), (true, vertices_580), (true, vertices_296), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 17 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_450) then 18 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_580) then 12 else
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
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_450), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
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
cert_row_4 0 0 1 2 4 7 302 38 2
cert_row_2 1 0 5 6 7 450
cert_row_4 2 0 1 3 4 5 118 22 3
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 4 38 302 2
cert_coverFacet 1 118
cert_cover_5 1 2 0 1 3 4 22 118 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 466
cert_cover_5 4 1 0 3 5 6 82 466 3
cert_coverFacet 5 482
cert_cover_5 5 1 0 4 5 6 98 482 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 740
cert_cover_5 8 3 1 4 5 6 100 740 3
cert_coverFacet 9 424
cert_cover_2 9 4 2 6 7 168 424 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0222

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0223.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0223

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 789, 681, 433, 721, 110, 558, 342, 774, 354, 716, 596, 472, 360, 424, 145, 273, 529, 161, 289, 545, 641, 769, 46, 70, 262, 518, 98, 290, 546, 322, 770, 76, 524, 84, 276, 532, 580, 772, 104, 168, 296, 552, 200, 328, 392, 648, 208, 336, 592, 400, 352, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_789, vertices_681, vertices_433, vertices_721, vertices_110, vertices_558, vertices_342, vertices_774, vertices_354, vertices_716, vertices_596, vertices_472, vertices_360, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_46, vertices_70, vertices_262, vertices_518, vertices_98, vertices_290, vertices_546, vertices_322, vertices_770, vertices_76, vertices_524, vertices_84, vertices_276, vertices_532, vertices_580, vertices_772, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_392, vertices_648, vertices_208, vertices_336, vertices_592, vertices_400, vertices_352, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_789), (false, vertices_681), (false, vertices_433), (false, vertices_721), (true, vertices_46), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_98), (true, vertices_322), (true, vertices_76), (true, vertices_524), (true, vertices_84), (true, vertices_580), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_328), (true, vertices_392), (true, vertices_336), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (true, vertices_46) then 18 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_352) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 1 3 5 7 342 70 2
cert_row_4 2 1 2 5 6 8 716 76 3
cert_row_4 3 2 3 5 6 7 472 200 1
cert_rows
cert_pivot_2 4 0 1 2
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 5 46 110 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 8 46 558 3
cert_coverFacet 2 342
cert_cover_5 2 1 0 1 3 5 70 342 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 354
cert_cover_2 4 4 0 5 7 98 354 3
cert_coverFacet 5 716
cert_cover_5 5 2 1 2 5 6 76 716 3
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 200 472 1
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coverFacet 9 424
cert_cover_2 9 4 2 6 7 168 424 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0223

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0224.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0224

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 421, 793, 681, 457, 118, 614, 602, 306, 786, 716, 308, 468, 676, 344, 137, 265, 521, 161, 289, 545, 385, 769, 102, 50, 82, 274, 530, 290, 546, 578, 770, 52, 84, 276, 164, 292, 548, 196, 580, 388, 644, 88, 280, 536, 200, 328, 584, 648, 304, 336, 784, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_421, vertices_793, vertices_681, vertices_457, vertices_118, vertices_614, vertices_602, vertices_306, vertices_786, vertices_716, vertices_308, vertices_468, vertices_676, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_385, vertices_769, vertices_102, vertices_50, vertices_82, vertices_274, vertices_530, vertices_290, vertices_546, vertices_578, vertices_770, vertices_52, vertices_84, vertices_276, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_644, vertices_88, vertices_280, vertices_536, vertices_200, vertices_328, vertices_584, vertices_648, vertices_304, vertices_336, vertices_784, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_421), (false, vertices_793), (false, vertices_681), (false, vertices_457), (true, vertices_102), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_578), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_548), (true, vertices_196), (true, vertices_580), (true, vertices_644), (true, vertices_88), (true, vertices_584), (true, vertices_304), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_793) then 22 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (true, vertices_102) then 18 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_336) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
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
cert_row_2 0 0 1 4 5 102
cert_row_4 1 0 2 3 5 8 602 82 1
cert_row_4 2 1 2 5 6 8 716 196 1
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 4 0 2 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 0 0 1 3 4 102 118 2
cert_coverFacet 1 614
cert_cover_5 1 0 0 1 4 8 102 614 3
cert_coverFacet 2 602
cert_cover_5 2 1 0 2 3 5 82 602 1
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 716
cert_cover_5 5 2 1 2 5 6 196 716 1
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 468
cert_cover_5 7 3 1 3 5 6 84 468 3
cert_coverFacet 8 676
cert_cover_2 8 4 1 6 8 164 676 3
cert_coverFacet 9 344
cert_cover_2 9 3 2 5 7 88 344 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0224

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0225.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0225

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 709, 569, 241, 865, 286, 542, 198, 326, 646, 402, 482, 812, 836, 440, 49, 145, 529, 97, 545, 193, 577, 641, 30, 70, 134, 262, 518, 146, 274, 530, 194, 322, 386, 642, 268, 524, 196, 324, 580, 644, 772, 56, 280, 536, 296, 552, 176, 400, 224, 352, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_709, vertices_569, vertices_241, vertices_865, vertices_286, vertices_542, vertices_198, vertices_326, vertices_646, vertices_402, vertices_482, vertices_812, vertices_836, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_529, vertices_97, vertices_545, vertices_193, vertices_577, vertices_641, vertices_30, vertices_70, vertices_134, vertices_262, vertices_518, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_642, vertices_268, vertices_524, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_56, vertices_280, vertices_536, vertices_296, vertices_552, vertices_176, vertices_400, vertices_224, vertices_352, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_709), (false, vertices_569), (false, vertices_241), (false, vertices_865), (true, vertices_30), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_268), (true, vertices_524), (true, vertices_324), (true, vertices_772), (true, vertices_280), (true, vertices_296), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_569) then 22 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (false, vertices_865) then 26 else
  if p.val = (true, vertices_30) then 18 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
cert_nodeAtPriority_64 70 134 262 518 274 194 322 386 268 524 324 772 280 296 400 416 659 30 709 569 241 865
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 6 7 482 194 1
cert_row_2 1 0 1 2 3 30
cert_row_4 2 1 2 4 7 8 812 268 2
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 1 0 1 2 7 30 286 3
cert_coverFacet 1 542
cert_cover_5 1 1 0 1 2 8 30 542 3
cert_coverFacet 2 198
cert_cover_2 2 1 0 5 6 70 198 3
cert_coverFacet 3 326
cert_cover_2 3 1 0 5 7 70 326 3
cert_coverFacet 4 646
cert_cover_2 4 1 0 6 8 134 646 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 482
cert_cover_5 6 0 0 4 5 6 194 482 1
cert_coverFacet 7 812
cert_cover_5 7 2 1 2 4 7 268 812 2
cert_coverFacet 8 836
cert_cover_2 8 5 1 7 8 324 836 3
cert_coverFacet 9 440
cert_cover_5 9 3 2 3 4 6 56 440 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0225

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0226.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0226

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 677, 713, 849, 481, 94, 174, 790, 550, 282, 426, 588, 652, 596, 472, 161, 289, 545, 193, 321, 577, 641, 769, 14, 22, 38, 518, 26, 170, 266, 274, 290, 546, 770, 76, 140, 524, 84, 532, 164, 548, 580, 644, 88, 280, 200, 584, 392, 648, 336, 592, 784, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_677, vertices_713, vertices_849, vertices_481, vertices_94, vertices_174, vertices_790, vertices_550, vertices_282, vertices_426, vertices_588, vertices_652, vertices_596, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_38, vertices_518, vertices_26, vertices_170, vertices_266, vertices_274, vertices_290, vertices_546, vertices_770, vertices_76, vertices_140, vertices_524, vertices_84, vertices_532, vertices_164, vertices_548, vertices_580, vertices_644, vertices_88, vertices_280, vertices_200, vertices_584, vertices_392, vertices_648, vertices_336, vertices_592, vertices_784, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_677), (false, vertices_713), (false, vertices_849), (false, vertices_481), (true, vertices_14), (true, vertices_22), (true, vertices_38), (true, vertices_518), (true, vertices_26), (true, vertices_170), (true, vertices_266), (true, vertices_274), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_84), (true, vertices_532), (true, vertices_580), (true, vertices_88), (true, vertices_280), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_170) then 18 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_580) then 12 else
  if p.val = (true, vertices_88) then 13 else
  if p.val = (true, vertices_280) then 14 else
  if p.val = (true, vertices_392) then 15 else
  0
cert_priority
cert_nodeAtPriority_64 14 22 38 518 26 266 274 76 140 524 84 532 580 88 280 392 803 170 677 713 849 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 6 170
cert_row_4 1 0 1 3 7 8 790 22 3
cert_row_4 2 0 1 2 3 5 94 14 3
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 4 8 0 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 2 0 1 2 3 14 94 3
cert_coverFacet 1 174
cert_cover_5 1 0 0 1 2 4 14 174 3
cert_coverFacet 2 790
cert_cover_5 2 1 0 1 3 7 22 790 3
cert_coverFacet 3 550
cert_cover_2 3 1 0 4 8 38 550 3
cert_coverFacet 4 282
cert_cover_2 4 2 0 3 7 26 282 3
cert_coverFacet 5 426
cert_cover_5 5 0 0 2 4 7 170 426 3
cert_coverFacet 6 588
cert_cover_2 6 2 1 5 8 76 588 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 596
cert_cover_2 8 3 1 5 8 84 596 3
cert_coverFacet 9 472
cert_cover_5 9 3 2 3 5 6 88 472 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0226

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0227.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0227

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 595, 355, 213, 533, 389, 457, 810, 738, 412, 796, 696, 232, 360, 720, 67, 259, 515, 21, 133, 261, 517, 81, 529, 193, 321, 385, 98, 290, 546, 578, 770, 284, 148, 532, 388, 772, 152, 536, 104, 168, 296, 552, 200, 328, 392, 776, 208, 592, 656, 224, 352, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_595, vertices_355, vertices_213, vertices_533, vertices_389, vertices_457, vertices_810, vertices_738, vertices_412, vertices_796, vertices_696, vertices_232, vertices_360, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_21, vertices_133, vertices_261, vertices_517, vertices_81, vertices_529, vertices_193, vertices_321, vertices_385, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_284, vertices_148, vertices_532, vertices_388, vertices_772, vertices_152, vertices_536, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_392, vertices_776, vertices_208, vertices_592, vertices_656, vertices_224, vertices_352, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_595), (false, vertices_355), (false, vertices_213), (false, vertices_533), (false, vertices_389), (false, vertices_457), (true, vertices_546), (true, vertices_284), (true, vertices_152), (true, vertices_536), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_656), (true, vertices_224), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_595) then 16 else
  if p.val = (false, vertices_355) then 17 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_284) then 20 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_284), by decide +kernel⟩
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
cert_row_2 0 1 2 3 7 284
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 2 3 4 6 8 696 152 2
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 810
cert_cover_5 0 1 0 2 4 7 290 810 1
cert_coverFacet 1 738
cert_cover_5 1 2 0 4 5 6 98 738 3
cert_coverFacet 2 412
cert_cover_5 2 0 1 2 3 6 284 412 3
cert_coverFacet 3 796
cert_cover_5 3 0 1 2 3 8 284 796 3
cert_coverFacet 4 696
cert_cover_5 4 3 2 3 4 6 152 696 2
cert_coverFacet 5 232
cert_cover_2 5 4 2 5 6 104 232 3
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0227

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0228.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0228

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 597, 677, 453, 425, 833, 58, 538, 682, 306, 850, 220, 668, 376, 456, 69, 133, 517, 161, 289, 545, 321, 577, 385, 769, 26, 42, 522, 50, 274, 530, 290, 546, 770, 156, 84, 532, 196, 644, 56, 88, 536, 168, 296, 200, 328, 392, 648, 304, 336, 592, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_597, vertices_677, vertices_453, vertices_425, vertices_833, vertices_58, vertices_538, vertices_682, vertices_306, vertices_850, vertices_220, vertices_668, vertices_376, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_769, vertices_26, vertices_42, vertices_522, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_156, vertices_84, vertices_532, vertices_196, vertices_644, vertices_56, vertices_88, vertices_536, vertices_168, vertices_296, vertices_200, vertices_328, vertices_392, vertices_648, vertices_304, vertices_336, vertices_592, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_597), (false, vertices_677), (false, vertices_453), (false, vertices_425), (false, vertices_833), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_156), (true, vertices_56), (true, vertices_88), (true, vertices_536), (true, vertices_200), (true, vertices_328), (true, vertices_648), (true, vertices_304), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_597) then 21 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_453) then 23 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_156) then 19 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_336) then 14 else
  0
cert_priority
cert_nodeAtPriority_43 833 1 26 2 42 522 50 274 530 56 88 536 200 328 648 304 336 803 425 156 597 677 453
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 6 156
cert_row_4 1 0 2 4 6 8 682 42 3
cert_row_4 2 0 3 5 7 8 850 274 2
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 58
cert_cover_2 0 2 0 3 4 26 58 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 682
cert_cover_5 2 1 0 2 4 6 42 682 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 850
cert_cover_5 4 2 0 3 5 7 274 850 2
cert_coverFacet 5 220
cert_cover_5 5 0 1 2 3 5 156 220 3
cert_coverFacet 6 668
cert_cover_5 6 0 1 2 3 8 156 668 3
cert_coverFacet 7 376
cert_cover_5 7 3 2 3 4 5 56 376 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0228

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0229.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0229

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [199, 653, 85, 789, 425, 777, 465, 614, 646, 682, 370, 418, 450, 628, 824, 21, 69, 133, 517, 137, 265, 521, 81, 273, 193, 385, 769, 70, 134, 518, 98, 162, 290, 546, 194, 322, 386, 642, 84, 532, 612, 644, 168, 296, 552, 648, 776, 112, 304, 560, 336, 784, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_199, vertices_653, vertices_85, vertices_789, vertices_425, vertices_777, vertices_465, vertices_614, vertices_646, vertices_682, vertices_370, vertices_418, vertices_450, vertices_628, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_133, vertices_517, vertices_137, vertices_265, vertices_521, vertices_81, vertices_273, vertices_193, vertices_385, vertices_769, vertices_70, vertices_134, vertices_518, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_386, vertices_642, vertices_84, vertices_532, vertices_612, vertices_644, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_112, vertices_304, vertices_560, vertices_336, vertices_784, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_199), (false, vertices_653), (false, vertices_85), (false, vertices_789), (false, vertices_425), (false, vertices_777), (false, vertices_465), (true, vertices_518), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_386), (true, vertices_642), (true, vertices_612), (true, vertices_552), (true, vertices_112), (true, vertices_304), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 19 16 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_199) then 15 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_85) then 0 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_642) then 9 else
  if p.val = (true, vertices_612) then 21 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_560) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
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
cert_row_2 0 1 4 5 8 612
cert_row_4 1 0 2 4 6 8 682 162 1
cert_row_4 2 0 3 4 5 7 370 98 1
cert_row_4 3 2 3 4 7 8 824 296 1
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 0 0 1 4 5 70 614 2
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 682
cert_cover_5 2 1 0 2 4 6 162 682 1
cert_coverFacet 3 370
cert_cover_5 3 2 0 3 4 5 98 370 1
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 628
cert_cover_5 6 0 1 3 4 5 84 628 2
cert_coverFacet 7 824
cert_cover_5 7 3 2 3 4 7 296 824 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0229

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0231.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0231

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 301, 397, 661, 613, 169, 241, 806, 362, 338, 914, 610, 900, 472, 232, 269, 37, 133, 517, 41, 137, 81, 145, 529, 97, 161, 577, 82, 274, 530, 98, 290, 546, 322, 578, 770, 292, 548, 388, 644, 772, 104, 168, 296, 200, 328, 392, 208, 336, 400, 656, 224, 608, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_301, vertices_397, vertices_661, vertices_613, vertices_169, vertices_241, vertices_806, vertices_362, vertices_338, vertices_914, vertices_610, vertices_900, vertices_472, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_269, vertices_37, vertices_133, vertices_517, vertices_41, vertices_137, vertices_81, vertices_145, vertices_529, vertices_97, vertices_161, vertices_577, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_104, vertices_168, vertices_296, vertices_200, vertices_328, vertices_392, vertices_208, vertices_336, vertices_400, vertices_656, vertices_224, vertices_608, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_301), (false, vertices_397), (false, vertices_661), (false, vertices_613), (false, vertices_169), (false, vertices_241), (true, vertices_274), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_770), (true, vertices_772), (true, vertices_104), (true, vertices_200), (true, vertices_328), (true, vertices_336), (true, vertices_400), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 19 16 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_301) then 17 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_661) then 20 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
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
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_4 1 0 2 4 5 7 362 98 1
cert_row_4 2 0 3 6 7 8 914 274 2
cert_row_4 3 2 3 5 6 7 472 200 1
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 362
cert_cover_5 1 1 0 2 4 5 98 362 1
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 914
cert_cover_5 3 2 0 3 6 7 274 914 2
cert_coverFacet 4 610
cert_cover_2 4 4 0 5 8 98 610 3
cert_coverFacet 5 900
cert_cover_2 5 6 1 7 8 388 900 3
cert_coverFacet 6 472
cert_cover_5 6 3 2 3 5 6 200 472 1
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0231

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0232.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0232

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 651, 403, 355, 309, 569, 657, 454, 202, 716, 692, 404, 804, 836, 872, 11, 99, 131, 259, 41, 521, 49, 145, 273, 529, 289, 641, 74, 138, 194, 322, 386, 52, 148, 276, 292, 548, 196, 324, 580, 388, 644, 772, 104, 552, 200, 584, 648, 560, 400, 656, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_651, vertices_403, vertices_355, vertices_309, vertices_569, vertices_657, vertices_454, vertices_202, vertices_716, vertices_692, vertices_404, vertices_804, vertices_836, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_99, vertices_131, vertices_259, vertices_41, vertices_521, vertices_49, vertices_145, vertices_273, vertices_529, vertices_289, vertices_641, vertices_74, vertices_138, vertices_194, vertices_322, vertices_386, vertices_52, vertices_148, vertices_276, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_104, vertices_552, vertices_200, vertices_584, vertices_648, vertices_560, vertices_400, vertices_656, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_651), (false, vertices_403), (false, vertices_355), (false, vertices_309), (false, vertices_569), (false, vertices_657), (true, vertices_194), (true, vertices_148), (true, vertices_548), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_200), (true, vertices_584), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 14 16 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 20 else
  if p.val = (false, vertices_651) then 17 else
  if p.val = (false, vertices_403) then 21 else
  if p.val = (false, vertices_355) then 22 else
  if p.val = (false, vertices_309) then 15 else
  if p.val = (false, vertices_569) then 18 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
cert_nodeAtPriority_48 1 657 0 194 2 148 548 196 324 580 388 644 772 200 584 800 832 309 651 569 107 403 355
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 194 1
cert_row_4 1 1 3 4 6 8 692 52 3
cert_row_4 2 1 2 5 6 8 716 196 1
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 0 0 1 5 6 194 454 1
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 716
cert_cover_5 2 2 1 2 5 6 196 716 1
cert_coverFacet 3 692
cert_cover_5 3 1 1 3 4 6 52 692 3
cert_coverFacet 4 404
cert_cover_2 4 3 1 6 7 148 404 3
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coverFacet 6 836
cert_cover_2 6 5 1 7 8 324 836 3
cert_coverFacet 7 872
cert_cover_5 7 3 2 4 5 7 104 872 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0232

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0233.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0233

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 45, 269, 613, 121, 793, 721, 174, 398, 550, 914, 738, 344, 488, 464, 13, 37, 261, 517, 25, 41, 265, 81, 529, 97, 577, 769, 142, 38, 262, 518, 162, 546, 386, 642, 770, 44, 268, 548, 88, 280, 104, 168, 328, 392, 208, 336, 400, 656, 784, 224, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_45, vertices_269, vertices_613, vertices_121, vertices_793, vertices_721, vertices_174, vertices_398, vertices_550, vertices_914, vertices_738, vertices_344, vertices_488, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_261, vertices_517, vertices_25, vertices_41, vertices_265, vertices_81, vertices_529, vertices_97, vertices_577, vertices_769, vertices_142, vertices_38, vertices_262, vertices_518, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_548, vertices_88, vertices_280, vertices_104, vertices_168, vertices_328, vertices_392, vertices_208, vertices_336, vertices_400, vertices_656, vertices_784, vertices_224, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_45), (false, vertices_269), (false, vertices_613), (false, vertices_121), (false, vertices_793), (false, vertices_721), (true, vertices_142), (true, vertices_38), (true, vertices_162), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_168), (true, vertices_328), (true, vertices_392), (true, vertices_336), (true, vertices_400), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_45) then 0 else
  if p.val = (false, vertices_269) then 1 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_142) then 16 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_142), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
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
cert_row_2 0 0 1 2 6 142
cert_row_4 1 0 3 6 7 8 914 386 1
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 0 0 1 2 4 142 174 3
cert_coverFacet 1 398
cert_cover_5 1 0 0 1 2 7 142 398 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 914
cert_cover_5 3 1 0 3 6 7 386 914 1
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 162 738 2
cert_coverFacet 5 344
cert_cover_2 5 3 2 5 7 88 344 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 104 488 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0233

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0234.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0234

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 355, 163, 613, 601, 681, 329, 806, 902, 674, 668, 372, 596, 404, 472, 35, 131, 259, 73, 137, 265, 521, 97, 161, 545, 321, 577, 774, 162, 290, 546, 386, 642, 84, 148, 276, 532, 100, 292, 548, 580, 388, 644, 88, 152, 536, 328, 392, 648, 336, 592, 400, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_355, vertices_163, vertices_613, vertices_601, vertices_681, vertices_329, vertices_806, vertices_902, vertices_674, vertices_668, vertices_372, vertices_596, vertices_404, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_73, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_774, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_84, vertices_148, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_580, vertices_388, vertices_644, vertices_88, vertices_152, vertices_536, vertices_328, vertices_392, vertices_648, vertices_336, vertices_592, vertices_400, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_355), (false, vertices_163), (false, vertices_613), (false, vertices_601), (false, vertices_681), (false, vertices_329), (true, vertices_774), (true, vertices_546), (true, vertices_642), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_388), (true, vertices_644), (true, vertices_152), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_355) then 19 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_613) then 15 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (true, vertices_774) then 16 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
cert_nodeAtPriority_25 1 163 0 329 546 642 84 148 276 532 292 388 644 152 336 400 613 774 395 355 601 681
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 1 2 3 6 8 668 148 1
cert_row_4 2 1 3 4 5 7 372 84 2
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 774 806 2
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 774 902 2
cert_coverFacet 2 674
cert_cover_2 2 4 0 6 8 162 674 3
cert_coverFacet 3 668
cert_cover_5 3 1 1 2 3 6 148 668 1
cert_coverFacet 4 372
cert_cover_5 4 2 1 3 4 5 84 372 2
cert_coverFacet 5 596
cert_cover_2 5 3 1 5 8 84 596 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 88 472 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0234

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0235.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0235

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 781, 421, 409, 681, 54, 342, 838, 218, 178, 738, 308, 856, 712, 432, 37, 261, 517, 137, 265, 521, 161, 545, 385, 22, 38, 326, 518, 50, 82, 146, 162, 546, 194, 578, 52, 276, 292, 772, 88, 152, 280, 200, 584, 648, 776, 176, 304, 336, 400, 416, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_781, vertices_421, vertices_409, vertices_681, vertices_54, vertices_342, vertices_838, vertices_218, vertices_178, vertices_738, vertices_308, vertices_856, vertices_712, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_161, vertices_545, vertices_385, vertices_22, vertices_38, vertices_326, vertices_518, vertices_50, vertices_82, vertices_146, vertices_162, vertices_546, vertices_194, vertices_578, vertices_52, vertices_276, vertices_292, vertices_772, vertices_88, vertices_152, vertices_280, vertices_200, vertices_584, vertices_648, vertices_776, vertices_176, vertices_304, vertices_336, vertices_400, vertices_416, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_781), (false, vertices_421), (false, vertices_409), (false, vertices_681), (true, vertices_22), (true, vertices_326), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_162), (true, vertices_194), (true, vertices_578), (true, vertices_52), (true, vertices_276), (true, vertices_88), (true, vertices_200), (true, vertices_584), (true, vertices_176), (true, vertices_304), (true, vertices_336), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 18 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_421) then 22 else
  if p.val = (false, vertices_409) then 24 else
  if p.val = (false, vertices_681) then 25 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_326) then 19 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_704) then 15 else
  if p.val = (true, vertices_832) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_326), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 7 326
cert_row_4 1 0 4 5 6 8 738 162 2
cert_row_4 2 0 2 3 5 6 218 82 1
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 54
cert_cover_2 0 1 0 3 4 22 54 3
cert_coverFacet 1 342
cert_cover_5 1 0 0 1 3 5 22 342 3
cert_coverFacet 2 838
cert_cover_5 2 0 0 1 5 8 326 838 3
cert_coverFacet 3 218
cert_cover_5 3 2 0 2 3 5 82 218 1
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 738
cert_cover_5 5 1 0 4 5 6 162 738 2
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 856
cert_cover_5 7 3 2 3 5 7 88 856 3
cert_coverFacet 8 712
cert_cover_2 8 5 2 6 8 200 712 3
cert_coverFacet 9 432
cert_cover_2 9 4 3 6 7 176 432 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0235

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0236.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0236

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 613, 409, 689, 481, 833, 286, 46, 550, 838, 538, 682, 236, 460, 664, 145, 273, 529, 97, 161, 545, 321, 577, 385, 769, 14, 38, 262, 518, 26, 42, 522, 274, 530, 546, 770, 44, 204, 268, 100, 548, 324, 580, 152, 280, 536, 168, 392, 648, 656, 224, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_613, vertices_409, vertices_689, vertices_481, vertices_833, vertices_286, vertices_46, vertices_550, vertices_838, vertices_538, vertices_682, vertices_236, vertices_460, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_769, vertices_14, vertices_38, vertices_262, vertices_518, vertices_26, vertices_42, vertices_522, vertices_274, vertices_530, vertices_546, vertices_770, vertices_44, vertices_204, vertices_268, vertices_100, vertices_548, vertices_324, vertices_580, vertices_152, vertices_280, vertices_536, vertices_168, vertices_392, vertices_648, vertices_656, vertices_224, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_613), (false, vertices_409), (false, vertices_689), (false, vertices_481), (false, vertices_833), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_546), (true, vertices_44), (true, vertices_204), (true, vertices_268), (true, vertices_324), (true, vertices_536), (true, vertices_168), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_42) then 6 else
  if p.val = (true, vertices_522) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_204) then 19 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_648) then 14 else
  0
cert_priority
cert_nodeAtPriority_9 0 833 1 14 38 262 518 26 42 522 546 44 268 324 536 168 648 787 613 204 409 689 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 7 286 14 3
cert_row_4 1 0 1 5 7 8 838 262 2
cert_row_2 2 1 2 5 6 204
cert_row_4 3 0 2 4 6 8 682 42 3
cert_rows
cert_pivot_2 3 7 1 0
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 14 286 3
cert_coverFacet 1 46
cert_cover_2 1 1 0 2 4 14 46 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 838
cert_cover_5 3 1 0 1 5 7 262 838 2
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 682
cert_cover_5 5 3 0 2 4 6 42 682 3
cert_coverFacet 6 236
cert_cover_5 6 2 1 2 4 5 44 236 3
cert_coverFacet 7 460
cert_cover_5 7 2 1 2 5 7 204 460 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0236

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0237.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0237

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 535, 613, 421, 233, 721, 398, 806, 346, 154, 786, 216, 360, 424, 880, 23, 37, 133, 517, 145, 529, 97, 161, 193, 577, 134, 262, 518, 26, 138, 266, 146, 274, 530, 770, 292, 548, 388, 88, 152, 104, 168, 296, 200, 328, 392, 208, 336, 592, 784, 352, 608, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_535, vertices_613, vertices_421, vertices_233, vertices_721, vertices_398, vertices_806, vertices_346, vertices_154, vertices_786, vertices_216, vertices_360, vertices_424, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_37, vertices_133, vertices_517, vertices_145, vertices_529, vertices_97, vertices_161, vertices_193, vertices_577, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_770, vertices_292, vertices_548, vertices_388, vertices_88, vertices_152, vertices_104, vertices_168, vertices_296, vertices_200, vertices_328, vertices_392, vertices_208, vertices_336, vertices_592, vertices_784, vertices_352, vertices_608, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_535), (false, vertices_613), (false, vertices_421), (false, vertices_233), (false, vertices_721), (true, vertices_262), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_274), (true, vertices_770), (true, vertices_88), (true, vertices_152), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_336), (true, vertices_784), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 16 else
  if p.val = (false, vertices_535) then 17 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
cert_nodeAtPriority_62 262 26 138 266 274 770 88 152 296 328 392 336 784 352 800 151 535 613 421 233 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_4 1 0 1 4 7 8 806 262 2
cert_row_4 2 0 2 3 5 7 346 26 3
cert_row_4 3 3 4 5 7 8 880 336 1
cert_rows
cert_pivot_2 6 1 0 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 806
cert_cover_5 1 1 0 1 4 7 262 806 2
cert_coverFacet 2 346
cert_cover_5 2 2 0 2 3 5 26 346 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 216
cert_cover_2 5 3 2 5 6 88 216 3
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coverFacet 8 880
cert_cover_5 8 3 3 4 5 7 336 880 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0237

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0238.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0238

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 285, 541, 617, 425, 369, 662, 682, 210, 226, 610, 908, 212, 340, 484, 29, 41, 265, 521, 81, 273, 529, 97, 289, 577, 82, 146, 530, 98, 162, 546, 194, 578, 642, 268, 524, 84, 148, 276, 532, 196, 324, 388, 644, 168, 552, 392, 648, 208, 336, 224, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_285, vertices_541, vertices_617, vertices_425, vertices_369, vertices_662, vertices_682, vertices_210, vertices_226, vertices_610, vertices_908, vertices_212, vertices_340, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_41, vertices_265, vertices_521, vertices_81, vertices_273, vertices_529, vertices_97, vertices_289, vertices_577, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_388, vertices_644, vertices_168, vertices_552, vertices_392, vertices_648, vertices_208, vertices_336, vertices_224, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_285), (false, vertices_541), (false, vertices_617), (false, vertices_425), (false, vertices_369), (true, vertices_146), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_642), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_644), (true, vertices_648), (true, vertices_208), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 16 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 146 1 98 2 162 546 194 642 84 148 196 324 388 644 648 208 224 595 285 541 617 425 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_4 1 0 2 4 6 8 682 162 1
cert_row_4 2 1 2 6 7 8 908 268 2
cert_row_4 3 1 4 5 6 7 484 196 1
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 682
cert_cover_5 1 1 0 2 4 6 162 682 1
cert_coverFacet 2 210
cert_cover_2 2 3 0 5 6 82 210 3
cert_coverFacet 3 226
cert_cover_2 3 4 0 5 6 98 226 3
cert_coverFacet 4 610
cert_cover_2 4 4 0 5 8 98 610 3
cert_coverFacet 5 908
cert_cover_5 5 2 1 2 6 7 268 908 2
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coverFacet 8 484
cert_cover_5 8 3 1 4 5 6 196 484 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0238

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0239.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0239

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 541, 153, 713, 241, 817, 334, 590, 790, 354, 802, 156, 396, 436, 488, 25, 137, 521, 49, 145, 529, 97, 545, 193, 577, 78, 262, 518, 98, 290, 546, 322, 578, 770, 28, 140, 268, 524, 148, 276, 532, 388, 152, 200, 328, 584, 392, 176, 304, 784, 224, 352, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_541, vertices_153, vertices_713, vertices_241, vertices_817, vertices_334, vertices_590, vertices_790, vertices_354, vertices_802, vertices_156, vertices_396, vertices_436, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_521, vertices_49, vertices_145, vertices_529, vertices_97, vertices_545, vertices_193, vertices_577, vertices_78, vertices_262, vertices_518, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_388, vertices_152, vertices_200, vertices_328, vertices_584, vertices_392, vertices_176, vertices_304, vertices_784, vertices_224, vertices_352, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_541), (false, vertices_153), (false, vertices_713), (false, vertices_241), (false, vertices_817), (true, vertices_78), (true, vertices_262), (true, vertices_518), (true, vertices_290), (true, vertices_322), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_388), (true, vertices_328), (true, vertices_392), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_153) then 0 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_40 153 262 518 290 322 770 140 268 148 276 388 328 392 352 416 611 78 541 713 241 817
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 262 2
cert_row_2 1 0 1 2 5 78
cert_row_4 2 1 3 4 6 7 436 148 2
cert_row_4 3 2 4 5 6 7 488 200 1
cert_rows
cert_pivot_2 8 0 1 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 1 0 1 2 7 78 334 3
cert_coverFacet 1 590
cert_cover_5 1 1 0 1 2 8 78 590 3
cert_coverFacet 2 790
cert_cover_5 2 0 0 1 3 7 262 790 2
cert_coverFacet 3 354
cert_cover_2 3 4 0 5 7 98 354 3
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 436
cert_cover_5 7 2 1 3 4 6 148 436 2
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 200 488 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0239

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0240.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0240

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 541, 153, 809, 625, 433, 206, 334, 242, 354, 418, 156, 780, 724, 868, 25, 137, 265, 521, 49, 145, 529, 289, 545, 385, 78, 138, 266, 98, 162, 290, 194, 322, 386, 28, 140, 268, 524, 148, 532, 196, 324, 580, 772, 152, 776, 112, 176, 208, 592, 352, 608, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_541, vertices_153, vertices_809, vertices_625, vertices_433, vertices_206, vertices_334, vertices_242, vertices_354, vertices_418, vertices_156, vertices_780, vertices_724, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_529, vertices_289, vertices_545, vertices_385, vertices_78, vertices_138, vertices_266, vertices_98, vertices_162, vertices_290, vertices_194, vertices_322, vertices_386, vertices_28, vertices_140, vertices_268, vertices_524, vertices_148, vertices_532, vertices_196, vertices_324, vertices_580, vertices_772, vertices_152, vertices_776, vertices_112, vertices_176, vertices_208, vertices_592, vertices_352, vertices_608, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_541), (false, vertices_153), (false, vertices_809), (false, vertices_625), (false, vertices_433), (true, vertices_78), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_194), (true, vertices_322), (true, vertices_140), (true, vertices_268), (true, vertices_148), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_208), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_153) then 0 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
cert_nodeAtPriority_40 153 98 162 290 194 322 140 268 148 196 324 580 772 208 352 395 78 541 809 625 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 3 4 5 6 242 98 1
cert_row_4 2 1 3 5 6 8 724 148 2
cert_row_4 3 1 4 5 7 8 868 324 1
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 6 78 206 3
cert_coverFacet 1 334
cert_cover_5 1 0 0 1 2 7 78 334 3
cert_coverFacet 2 242
cert_cover_5 2 1 0 3 4 5 98 242 1
cert_coverFacet 3 354
cert_cover_2 3 4 0 5 7 98 354 3
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 724
cert_cover_5 7 2 1 3 5 6 148 724 2
cert_coverFacet 8 868
cert_cover_5 8 3 1 4 5 7 324 868 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0240

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0241.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0241

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 285, 781, 181, 709, 817, 590, 810, 330, 434, 450, 706, 92, 212, 472, 269, 21, 133, 517, 49, 273, 161, 545, 641, 769, 74, 266, 522, 162, 290, 546, 194, 322, 578, 386, 642, 28, 76, 524, 84, 148, 196, 580, 88, 280, 328, 776, 176, 304, 208, 400, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_285, vertices_781, vertices_181, vertices_709, vertices_817, vertices_590, vertices_810, vertices_330, vertices_434, vertices_450, vertices_706, vertices_92, vertices_212, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_269, vertices_21, vertices_133, vertices_517, vertices_49, vertices_273, vertices_161, vertices_545, vertices_641, vertices_769, vertices_74, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_28, vertices_76, vertices_524, vertices_84, vertices_148, vertices_196, vertices_580, vertices_88, vertices_280, vertices_328, vertices_776, vertices_176, vertices_304, vertices_208, vertices_400, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_285), (false, vertices_781), (false, vertices_181), (false, vertices_709), (false, vertices_817), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_88), (true, vertices_328), (true, vertices_208), (true, vertices_400), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_181) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 74 2 266 1 522 290 194 322 578 386 76 84 88 328 208 400 448 675 285 781 181 709 817
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 74 1
cert_row_4 1 0 2 4 7 8 810 266 2
cert_row_4 2 0 3 4 6 7 434 162 1
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 74 590 1
cert_coverFacet 1 810
cert_cover_5 1 1 0 2 4 7 266 810 2
cert_coverFacet 2 330
cert_cover_2 2 2 0 5 7 74 330 3
cert_coverFacet 3 434
cert_cover_5 3 2 0 3 4 6 162 434 1
cert_coverFacet 4 450
cert_cover_2 4 5 0 6 7 194 450 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 92
cert_cover_2 6 2 1 3 5 28 92 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coverFacet 8 472
cert_cover_5 8 3 2 3 5 6 88 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0241

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2823 : Certifies 2823 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0211.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2824 : Certifies 2824 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0212.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2825 : Certifies 2825 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0213.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2826 : Certifies 2826 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0214.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2827 : Certifies 2827 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0215.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2828 : Certifies 2828 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0216.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2829 : Certifies 2829 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0217.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2830 : Certifies 2830 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0218.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2831 : Certifies 2831 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0219.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2832 : Certifies 2832 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0220.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2833 : Certifies 2833 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0221.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2834 : Certifies 2834 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0222.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2835 : Certifies 2835 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0223.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2836 : Certifies 2836 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0224.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2837 : Certifies 2837 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0225.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2838 : Certifies 2838 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0226.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2839 : Certifies 2839 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0227.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2840 : Certifies 2840 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0228.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2841 : Certifies 2841 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0229.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2842 : Certifies 2842 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0231.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2843 : Certifies 2843 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0232.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2844 : Certifies 2844 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0233.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2845 : Certifies 2845 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0234.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2846 : Certifies 2846 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0235.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2847 : Certifies 2847 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0236.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2848 : Certifies 2848 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0237.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2849 : Certifies 2849 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0238.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2850 : Certifies 2850 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0239.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2851 : Certifies 2851 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0240.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2852 : Certifies 2852 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0241.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B093 (j : Fin 30) :
    Certifies (2823 + j.val) := by
  fin_cases j
  · exact projection_2823
  · exact projection_2824
  · exact projection_2825
  · exact projection_2826
  · exact projection_2827
  · exact projection_2828
  · exact projection_2829
  · exact projection_2830
  · exact projection_2831
  · exact projection_2832
  · exact projection_2833
  · exact projection_2834
  · exact projection_2835
  · exact projection_2836
  · exact projection_2837
  · exact projection_2838
  · exact projection_2839
  · exact projection_2840
  · exact projection_2841
  · exact projection_2842
  · exact projection_2843
  · exact projection_2844
  · exact projection_2845
  · exact projection_2846
  · exact projection_2847
  · exact projection_2848
  · exact projection_2849
  · exact projection_2850
  · exact projection_2851
  · exact projection_2852

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
