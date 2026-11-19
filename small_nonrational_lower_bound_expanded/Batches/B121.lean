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
/- Source: ProjectionCertificates/R_m15e10q1_1100.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1100

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 29, 333, 901, 409, 689, 62, 110, 326, 774, 626, 962, 184, 744, 456, 13, 21, 261, 517, 25, 265, 145, 529, 385, 641, 46, 22, 70, 262, 518, 50, 530, 98, 322, 578, 770, 28, 76, 324, 772, 56, 152, 104, 168, 200, 328, 392, 176, 560, 608, 672, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_29, vertices_333, vertices_901, vertices_409, vertices_689, vertices_62, vertices_110, vertices_326, vertices_774, vertices_626, vertices_962, vertices_184, vertices_744, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_261, vertices_517, vertices_25, vertices_265, vertices_145, vertices_529, vertices_385, vertices_641, vertices_46, vertices_22, vertices_70, vertices_262, vertices_518, vertices_50, vertices_530, vertices_98, vertices_322, vertices_578, vertices_770, vertices_28, vertices_76, vertices_324, vertices_772, vertices_56, vertices_152, vertices_104, vertices_168, vertices_200, vertices_328, vertices_392, vertices_176, vertices_560, vertices_608, vertices_672, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_29), (false, vertices_333), (false, vertices_901), (false, vertices_409), (false, vertices_689), (true, vertices_46), (true, vertices_70), (true, vertices_262), (true, vertices_50), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_56), (true, vertices_104), (true, vertices_168), (true, vertices_200), (true, vertices_608), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 16 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_901) then 20 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (true, vertices_46) then 17 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_448) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 29 70 262 50 98 322 578 770 56 104 168 200 608 448 704 535 46 333 901 409 689
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 3 4 5 8 626 50 3
cert_row_4 2 0 5 6 7 8 962 322 2
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 46 62 3
cert_coverFacet 1 110
cert_cover_5 1 0 0 1 2 5 46 110 3
cert_coverFacet 2 326
cert_cover_2 2 1 0 5 7 70 326 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 626
cert_cover_5 4 1 0 3 4 5 50 626 3
cert_coverFacet 5 962
cert_cover_5 5 2 0 5 6 7 322 962 2
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 104 744 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1100

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_1101.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1101

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 157, 269, 565, 425, 241, 801, 334, 590, 626, 482, 802, 540, 472, 600, 13, 21, 261, 517, 137, 265, 49, 145, 161, 289, 545, 769, 78, 262, 518, 98, 290, 546, 322, 578, 770, 28, 268, 524, 532, 88, 152, 536, 328, 584, 392, 112, 560, 208, 592, 224, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_157, vertices_269, vertices_565, vertices_425, vertices_241, vertices_801, vertices_334, vertices_590, vertices_626, vertices_482, vertices_802, vertices_540, vertices_472, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_261, vertices_517, vertices_137, vertices_265, vertices_49, vertices_145, vertices_161, vertices_289, vertices_545, vertices_769, vertices_78, vertices_262, vertices_518, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_268, vertices_524, vertices_532, vertices_88, vertices_152, vertices_536, vertices_328, vertices_584, vertices_392, vertices_112, vertices_560, vertices_208, vertices_592, vertices_224, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_157), (false, vertices_269), (false, vertices_565), (false, vertices_425), (false, vertices_241), (false, vertices_801), (true, vertices_78), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_578), (true, vertices_524), (true, vertices_88), (true, vertices_536), (true, vertices_328), (true, vertices_584), (true, vertices_592), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_801) then 1 else
  if p.val = (true, vertices_78) then 16 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 269 1 801 98 290 546 322 578 524 88 536 328 584 592 448 775 78 157 565 425 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 3 4 5 8 626 98 1
cert_row_4 2 0 4 5 6 7 482 98 3
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 7 78 334 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 626
cert_cover_5 2 1 0 3 4 5 98 626 1
cert_coverFacet 3 482
cert_cover_5 3 2 0 4 5 6 98 482 3
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 472
cert_cover_5 6 3 2 3 5 6 88 472 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1101

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_1102.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1102

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 267, 899, 421, 121, 297, 737, 62, 302, 534, 774, 538, 244, 916, 728, 11, 259, 515, 41, 73, 265, 97, 161, 289, 577, 385, 641, 46, 22, 262, 518, 26, 266, 522, 530, 770, 52, 148, 532, 164, 292, 388, 772, 56, 88, 536, 296, 584, 112, 208, 656, 224, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_267, vertices_899, vertices_421, vertices_121, vertices_297, vertices_737, vertices_62, vertices_302, vertices_534, vertices_774, vertices_538, vertices_244, vertices_916, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_259, vertices_515, vertices_41, vertices_73, vertices_265, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_641, vertices_46, vertices_22, vertices_262, vertices_518, vertices_26, vertices_266, vertices_522, vertices_530, vertices_770, vertices_52, vertices_148, vertices_532, vertices_164, vertices_292, vertices_388, vertices_772, vertices_56, vertices_88, vertices_536, vertices_296, vertices_584, vertices_112, vertices_208, vertices_656, vertices_224, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_267), (false, vertices_899), (false, vertices_421), (false, vertices_121), (false, vertices_297), (false, vertices_737), (true, vertices_46), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_530), (true, vertices_52), (true, vertices_148), (true, vertices_532), (true, vertices_772), (true, vertices_536), (true, vertices_208), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_121) then 21 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_46) then 17 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_656) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_2 0 0 1 2 4 46
cert_row_4 1 1 3 4 5 6 244 52 3
cert_row_4 2 1 3 6 7 8 916 148 3
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 46 62 3
cert_coverFacet 1 302
cert_cover_5 1 0 0 1 2 7 46 302 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 244
cert_cover_5 5 1 1 3 4 5 52 244 3
cert_coverFacet 6 916
cert_cover_5 6 2 1 3 6 7 148 916 3
cert_coverFacet 7 728
cert_cover_5 7 3 2 3 5 6 88 728 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1102

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_1103.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1103

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 565, 361, 553, 713, 433, 657, 214, 598, 422, 774, 842, 812, 180, 720, 41, 73, 521, 49, 145, 529, 289, 545, 193, 321, 385, 641, 86, 134, 262, 518, 194, 322, 578, 386, 770, 52, 148, 532, 164, 292, 548, 772, 296, 552, 328, 584, 776, 176, 208, 592, 656, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_565, vertices_361, vertices_553, vertices_713, vertices_433, vertices_657, vertices_214, vertices_598, vertices_422, vertices_774, vertices_842, vertices_812, vertices_180, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_521, vertices_49, vertices_145, vertices_529, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_86, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_52, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_772, vertices_296, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_208, vertices_592, vertices_656, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_565), (false, vertices_361), (false, vertices_553), (false, vertices_713), (false, vertices_433), (false, vertices_657), (true, vertices_86), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_578), (true, vertices_770), (true, vertices_148), (true, vertices_164), (true, vertices_292), (true, vertices_772), (true, vertices_776), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_565) then 18 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_657) then 1 else
  if p.val = (true, vertices_86) then 16 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_592) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
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
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 1 4 6 7 422 134 2
cert_row_4 2 0 2 5 7 8 842 322 1
cert_row_4 3 1 2 4 7 8 812 292 1
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 6 86 214 3
cert_coverFacet 1 598
cert_cover_5 1 0 0 1 3 8 86 598 3
cert_coverFacet 2 422
cert_cover_5 2 1 0 1 4 6 134 422 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 842
cert_cover_5 4 2 0 2 5 7 322 842 1
cert_coverFacet 5 812
cert_cover_5 5 3 1 2 4 7 292 812 1
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1103

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_1104.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1104

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 781, 357, 549, 569, 153, 433, 838, 218, 602, 778, 482, 244, 564, 596, 37, 261, 517, 25, 137, 265, 521, 49, 145, 289, 545, 385, 90, 138, 266, 522, 194, 322, 578, 386, 770, 52, 84, 532, 100, 548, 324, 580, 772, 152, 536, 776, 176, 560, 208, 592, 224, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_781, vertices_357, vertices_549, vertices_569, vertices_153, vertices_433, vertices_838, vertices_218, vertices_602, vertices_778, vertices_482, vertices_244, vertices_564, vertices_596] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_25, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_289, vertices_545, vertices_385, vertices_90, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_52, vertices_84, vertices_532, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_152, vertices_536, vertices_776, vertices_176, vertices_560, vertices_208, vertices_592, vertices_224, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_781), (false, vertices_357), (false, vertices_549), (false, vertices_569), (false, vertices_153), (false, vertices_433), (true, vertices_90), (true, vertices_522), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_52), (true, vertices_84), (true, vertices_532), (true, vertices_580), (true, vertices_208), (true, vertices_592), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_153) then 1 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (true, vertices_90) then 16 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_224) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 549 1 153 522 194 322 578 770 52 84 532 580 208 592 224 395 90 781 357 569 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 4 5 6 7 482 194 1
cert_row_4 3 1 3 4 5 6 244 52 3
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
cert_coverFacet 5 244
cert_cover_5 5 3 1 3 4 5 52 244 3
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1104

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_1105.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1105

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 563, 147, 589, 405, 325, 849, 682, 370, 402, 418, 236, 652, 484, 632, 19, 131, 515, 69, 133, 261, 517, 145, 273, 529, 321, 577, 50, 146, 274, 162, 290, 546, 386, 642, 76, 140, 524, 228, 324, 388, 644, 104, 168, 552, 584, 648, 112, 560, 336, 592, 400, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_563, vertices_147, vertices_589, vertices_405, vertices_325, vertices_849, vertices_682, vertices_370, vertices_402, vertices_418, vertices_236, vertices_652, vertices_484, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_515, vertices_69, vertices_133, vertices_261, vertices_517, vertices_145, vertices_273, vertices_529, vertices_321, vertices_577, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_76, vertices_140, vertices_524, vertices_228, vertices_324, vertices_388, vertices_644, vertices_104, vertices_168, vertices_552, vertices_584, vertices_648, vertices_112, vertices_560, vertices_336, vertices_592, vertices_400, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_563), (false, vertices_147), (false, vertices_589), (false, vertices_405), (false, vertices_325), (false, vertices_849), (true, vertices_274), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_140), (true, vertices_228), (true, vertices_104), (true, vertices_168), (true, vertices_552), (true, vertices_648), (true, vertices_112), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_325) then 1 else
  if p.val = (false, vertices_849) then 23 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_228) then 20 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_228), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
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
cert_row_4 2 0 3 4 5 7 370 50 3
cert_row_4 3 2 3 4 5 8 632 104 1
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 682
cert_cover_5 0 1 0 2 4 6 162 682 1
cert_coverFacet 1 370
cert_cover_5 1 2 0 3 4 5 50 370 3
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1105

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_1106.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1106

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 205, 405, 613, 773, 105, 425, 790, 666, 282, 362, 714, 610, 724, 408, 69, 133, 261, 517, 41, 73, 137, 97, 289, 545, 385, 769, 26, 74, 650, 266, 274, 530, 98, 290, 546, 578, 770, 148, 276, 532, 196, 580, 772, 152, 280, 104, 296, 200, 392, 400, 656, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_205, vertices_405, vertices_613, vertices_773, vertices_105, vertices_425, vertices_790, vertices_666, vertices_282, vertices_362, vertices_714, vertices_610, vertices_724, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_517, vertices_41, vertices_73, vertices_137, vertices_97, vertices_289, vertices_545, vertices_385, vertices_769, vertices_26, vertices_74, vertices_650, vertices_266, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_148, vertices_276, vertices_532, vertices_196, vertices_580, vertices_772, vertices_152, vertices_280, vertices_104, vertices_296, vertices_200, vertices_392, vertices_400, vertices_656, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_205), (false, vertices_405), (false, vertices_613), (false, vertices_773), (false, vertices_105), (false, vertices_425), (true, vertices_26), (true, vertices_74), (true, vertices_650), (true, vertices_266), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_578), (true, vertices_532), (true, vertices_152), (true, vertices_280), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_205) then 18 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_105) then 1 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_650) then 16 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 773 1 105 26 74 266 274 530 98 578 532 152 280 656 704 803 650 205 405 613 425
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 7 362 74 2
cert_row_2 1 0 2 6 8 650
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 1 3 5 6 8 724 148 2
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 666
cert_cover_5 1 1 0 2 3 6 26 666 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 362
cert_cover_5 3 0 0 2 4 5 74 362 2
cert_coverFacet 4 714
cert_cover_5 4 1 0 2 5 6 74 714 3
cert_coverFacet 5 610
cert_cover_2 5 4 0 5 8 98 610 3
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 148 724 2
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1106

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_1107.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1107

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 781, 185, 553, 625, 913, 270, 526, 598, 454, 234, 618, 340, 788, 496, 41, 137, 265, 521, 49, 145, 529, 545, 385, 769, 14, 70, 262, 518, 106, 138, 266, 522, 194, 578, 386, 268, 524, 84, 276, 532, 324, 772, 168, 552, 112, 176, 336, 592, 400, 784, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_781, vertices_185, vertices_553, vertices_625, vertices_913, vertices_270, vertices_526, vertices_598, vertices_454, vertices_234, vertices_618, vertices_340, vertices_788, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_529, vertices_545, vertices_385, vertices_769, vertices_14, vertices_70, vertices_262, vertices_518, vertices_106, vertices_138, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_324, vertices_772, vertices_168, vertices_552, vertices_112, vertices_176, vertices_336, vertices_592, vertices_400, vertices_784, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_781), (false, vertices_185), (false, vertices_553), (false, vertices_625), (false, vertices_913), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_106), (true, vertices_522), (true, vertices_194), (true, vertices_578), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_324), (true, vertices_336), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_913) then 24 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_106) then 17 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_40 553 14 70 262 518 522 194 578 84 276 532 324 336 224 448 395 106 781 185 625 913
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 1 3 5 8 598 70 2
cert_row_4 2 0 1 5 6 7 454 70 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 2 8 0 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 598
cert_cover_5 2 1 0 1 3 5 70 598 2
cert_coverFacet 3 454
cert_cover_5 3 2 0 1 5 6 70 454 3
cert_coverFacet 4 234
cert_cover_5 4 0 0 2 4 6 106 234 3
cert_coverFacet 5 618
cert_cover_5 5 0 0 2 4 8 106 618 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1107

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_1108.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1108

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 421, 185, 537, 617, 465, 353, 542, 214, 454, 774, 866, 156, 684, 804, 25, 41, 521, 81, 145, 529, 97, 161, 289, 321, 577, 385, 22, 198, 262, 518, 82, 530, 322, 578, 770, 28, 140, 524, 148, 164, 292, 548, 388, 772, 152, 536, 168, 552, 208, 352, 608, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_421, vertices_185, vertices_537, vertices_617, vertices_465, vertices_353, vertices_542, vertices_214, vertices_454, vertices_774, vertices_866, vertices_156, vertices_684, vertices_804] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_521, vertices_81, vertices_145, vertices_529, vertices_97, vertices_161, vertices_289, vertices_321, vertices_577, vertices_385, vertices_22, vertices_198, vertices_262, vertices_518, vertices_82, vertices_530, vertices_322, vertices_578, vertices_770, vertices_28, vertices_140, vertices_524, vertices_148, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_152, vertices_536, vertices_168, vertices_552, vertices_208, vertices_352, vertices_608, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_421), (false, vertices_185), (false, vertices_537), (false, vertices_617), (false, vertices_465), (false, vertices_353), (true, vertices_22), (true, vertices_198), (true, vertices_262), (true, vertices_518), (true, vertices_322), (true, vertices_770), (true, vertices_28), (true, vertices_140), (true, vertices_524), (true, vertices_148), (true, vertices_548), (true, vertices_772), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_421) then 18 else
  if p.val = (false, vertices_185) then 20 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (false, vertices_353) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_198) then 16 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_198), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
cert_row_4 0 0 1 2 3 8 542 22 2
cert_row_4 1 0 4 5 7 8 866 322 1
cert_row_2 2 0 1 5 6 198
cert_row_4 3 1 2 4 6 8 684 140 2
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 22 542 2
cert_coverFacet 1 214
cert_cover_5 1 2 0 1 3 5 22 214 3
cert_coverFacet 2 454
cert_cover_5 2 2 0 1 5 7 198 454 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 866
cert_cover_5 4 1 0 4 5 7 322 866 1
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 684
cert_cover_5 6 3 1 2 4 6 140 684 2
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1108

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_1109.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1109

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [103, 519, 651, 179, 597, 113, 913, 398, 526, 422, 364, 588, 968, 880, 432, 7, 35, 131, 515, 69, 517, 49, 81, 145, 529, 97, 641, 14, 38, 390, 518, 138, 522, 162, 76, 268, 524, 100, 292, 580, 328, 584, 392, 648, 112, 176, 304, 592, 400, 784, 352, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_103, vertices_519, vertices_651, vertices_179, vertices_597, vertices_113, vertices_913, vertices_398, vertices_526, vertices_422, vertices_364, vertices_588, vertices_968, vertices_880, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_35, vertices_131, vertices_515, vertices_69, vertices_517, vertices_49, vertices_81, vertices_145, vertices_529, vertices_97, vertices_641, vertices_14, vertices_38, vertices_390, vertices_518, vertices_138, vertices_522, vertices_162, vertices_76, vertices_268, vertices_524, vertices_100, vertices_292, vertices_580, vertices_328, vertices_584, vertices_392, vertices_648, vertices_112, vertices_176, vertices_304, vertices_592, vertices_400, vertices_784, vertices_352, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_103), (false, vertices_519), (false, vertices_651), (false, vertices_179), (false, vertices_597), (false, vertices_113), (false, vertices_913), (true, vertices_14), (true, vertices_390), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_292), (true, vertices_328), (true, vertices_584), (true, vertices_392), (true, vertices_304), (true, vertices_352), (true, vertices_416), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 14 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_103) then 15 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_651) then 19 else
  if p.val = (false, vertices_179) then 20 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_113) then 1 else
  if p.val = (false, vertices_913) then 23 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_390) then 17 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_103), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_4 1 1 2 4 5 7 364 76 2
cert_row_4 2 2 5 6 7 8 968 328 2
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 422
cert_cover_5 2 0 0 1 4 6 38 422 3
cert_coverFacet 3 364
cert_cover_5 3 1 1 2 4 5 76 364 2
cert_coverFacet 4 588
cert_cover_2 4 2 1 5 8 76 588 3
cert_coverFacet 5 968
cert_cover_5 5 2 2 5 6 7 328 968 2
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1109

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_1110.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1110

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [39, 519, 611, 781, 421, 409, 681, 542, 342, 358, 722, 284, 664, 496, 736, 7, 35, 515, 37, 261, 517, 137, 265, 521, 161, 545, 385, 22, 38, 326, 518, 82, 530, 98, 578, 28, 268, 524, 276, 292, 152, 280, 536, 648, 208, 336, 400, 656, 224, 352, 608, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_39, vertices_519, vertices_611, vertices_781, vertices_421, vertices_409, vertices_681, vertices_542, vertices_342, vertices_358, vertices_722, vertices_284, vertices_664, vertices_496, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_35, vertices_515, vertices_37, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_161, vertices_545, vertices_385, vertices_22, vertices_38, vertices_326, vertices_518, vertices_82, vertices_530, vertices_98, vertices_578, vertices_28, vertices_268, vertices_524, vertices_276, vertices_292, vertices_152, vertices_280, vertices_536, vertices_648, vertices_208, vertices_336, vertices_400, vertices_656, vertices_224, vertices_352, vertices_608, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_39), (false, vertices_519), (false, vertices_611), (false, vertices_781), (false, vertices_421), (false, vertices_409), (false, vertices_681), (true, vertices_22), (true, vertices_326), (true, vertices_82), (true, vertices_530), (true, vertices_28), (true, vertices_276), (true, vertices_536), (true, vertices_208), (true, vertices_336), (true, vertices_656), (true, vertices_224), (true, vertices_352), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_39) then 0 else
  if p.val = (false, vertices_519) then 1 else
  if p.val = (false, vertices_611) then 15 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_681) then 22 else
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
cert_nodeAtPriority_25 0 39 1 519 22 82 530 28 276 536 208 336 656 224 352 704 611 326 781 421 409 681
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1110

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_1111.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1111

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 333, 141, 165, 805, 185, 617, 902, 218, 458, 626, 658, 396, 692, 120, 13, 37, 133, 261, 41, 73, 137, 161, 545, 321, 577, 769, 202, 82, 146, 530, 322, 578, 386, 642, 770, 140, 268, 164, 548, 388, 644, 772, 56, 88, 152, 104, 328, 392, 112, 176, 560, 656, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_333, vertices_141, vertices_165, vertices_805, vertices_185, vertices_617, vertices_902, vertices_218, vertices_458, vertices_626, vertices_658, vertices_396, vertices_692, vertices_120] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_133, vertices_261, vertices_41, vertices_73, vertices_137, vertices_161, vertices_545, vertices_321, vertices_577, vertices_769, vertices_202, vertices_82, vertices_146, vertices_530, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_140, vertices_268, vertices_164, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_104, vertices_328, vertices_392, vertices_112, vertices_176, vertices_560, vertices_656, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_333), (false, vertices_141), (false, vertices_165), (false, vertices_805), (false, vertices_185), (false, vertices_617), (true, vertices_202), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_388), (true, vertices_644), (true, vertices_88), (true, vertices_392), (true, vertices_112), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 15 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_165) then 1 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_617) then 22 else
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
cert_nodeAtPriority_25 0 141 1 165 82 146 530 386 642 388 644 88 392 112 560 656 835 202 333 805 185 617
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1111

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_1112.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1112

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 229, 793, 625, 177, 961, 206, 334, 186, 282, 450, 572, 172, 780, 868, 49, 145, 273, 529, 97, 161, 193, 577, 385, 769, 78, 26, 138, 266, 146, 274, 194, 322, 386, 44, 140, 268, 524, 100, 164, 548, 196, 324, 772, 56, 280, 536, 168, 776, 176, 560, 608, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_229, vertices_793, vertices_625, vertices_177, vertices_961, vertices_206, vertices_334, vertices_186, vertices_282, vertices_450, vertices_572, vertices_172, vertices_780, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_193, vertices_577, vertices_385, vertices_769, vertices_78, vertices_26, vertices_138, vertices_266, vertices_146, vertices_274, vertices_194, vertices_322, vertices_386, vertices_44, vertices_140, vertices_268, vertices_524, vertices_100, vertices_164, vertices_548, vertices_196, vertices_324, vertices_772, vertices_56, vertices_280, vertices_536, vertices_168, vertices_776, vertices_176, vertices_560, vertices_608, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_229), (false, vertices_793), (false, vertices_625), (false, vertices_177), (false, vertices_961), (true, vertices_78), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_194), (true, vertices_322), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_548), (true, vertices_324), (true, vertices_772), (true, vertices_56), (true, vertices_168)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 25 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (false, vertices_961) then 26 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_56) then 13 else
  if p.val = (true, vertices_168) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 6 186 26 3
cert_row_2 1 0 1 2 5 78
cert_row_4 2 1 2 3 4 8 572 44 2
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 6 0 2 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 6 78 206 3
cert_coverFacet 1 334
cert_cover_5 1 1 0 1 2 7 78 334 3
cert_coverFacet 2 186
cert_cover_5 2 0 0 2 3 4 26 186 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 450
cert_cover_2 4 5 0 6 7 194 450 3
cert_coverFacet 5 572
cert_cover_5 5 2 1 2 3 4 44 572 2
cert_coverFacet 6 172
cert_cover_2 6 2 1 4 6 44 172 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 868
cert_cover_5 8 3 1 4 5 7 100 868 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1112

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_1113.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1113

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 205, 589, 565, 421, 809, 598, 794, 202, 586, 242, 402, 116, 228, 944, 77, 37, 133, 517, 137, 265, 521, 289, 545, 385, 74, 138, 266, 522, 82, 146, 274, 530, 194, 578, 386, 52, 84, 532, 100, 164, 196, 580, 200, 584, 776, 112, 176, 560, 400, 784, 224, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_205, vertices_589, vertices_565, vertices_421, vertices_809, vertices_598, vertices_794, vertices_202, vertices_586, vertices_242, vertices_402, vertices_116, vertices_228, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_77, vertices_37, vertices_133, vertices_517, vertices_137, vertices_265, vertices_521, vertices_289, vertices_545, vertices_385, vertices_74, vertices_138, vertices_266, vertices_522, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_578, vertices_386, vertices_52, vertices_84, vertices_532, vertices_100, vertices_164, vertices_196, vertices_580, vertices_200, vertices_584, vertices_776, vertices_112, vertices_176, vertices_560, vertices_400, vertices_784, vertices_224, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_205), (false, vertices_589), (false, vertices_565), (false, vertices_421), (false, vertices_809), (true, vertices_74), (true, vertices_522), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_578), (true, vertices_84), (true, vertices_100), (true, vertices_112), (true, vertices_176), (true, vertices_400), (true, vertices_784), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 21 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_205) then 18 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_565) then 22 else
  if p.val = (false, vertices_421) then 23 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 74 2 522 1 82 146 274 530 194 578 84 100 112 176 400 784 224 395 205 589 809 565 421
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 82 1
cert_row_4 1 0 2 3 7 8 794 266 2
cert_row_4 2 0 3 4 5 6 242 82 2
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 82 598 1
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 266 794 2
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 586
cert_cover_2 3 2 0 5 8 74 586 3
cert_coverFacet 4 242
cert_cover_5 4 2 0 3 4 5 82 242 2
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 116
cert_cover_2 6 3 1 4 5 52 116 3
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coverFacet 8 944
cert_cover_5 8 3 3 4 6 7 176 944 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1113

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_1114.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1114

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 595, 147, 547, 213, 809, 713, 422, 818, 402, 236, 364, 340, 404, 856, 19, 35, 131, 515, 41, 137, 521, 81, 145, 545, 193, 577, 146, 274, 530, 162, 290, 546, 386, 108, 84, 148, 276, 164, 292, 196, 324, 388, 168, 296, 200, 328, 584, 776, 336, 592, 400, 784, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_595, vertices_147, vertices_547, vertices_213, vertices_809, vertices_713, vertices_422, vertices_818, vertices_402, vertices_236, vertices_364, vertices_340, vertices_404, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_515, vertices_41, vertices_137, vertices_521, vertices_81, vertices_145, vertices_545, vertices_193, vertices_577, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_108, vertices_84, vertices_148, vertices_276, vertices_164, vertices_292, vertices_196, vertices_324, vertices_388, vertices_168, vertices_296, vertices_200, vertices_328, vertices_584, vertices_776, vertices_336, vertices_592, vertices_400, vertices_784, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_595), (false, vertices_147), (false, vertices_547), (false, vertices_213), (false, vertices_809), (false, vertices_713), (true, vertices_274), (true, vertices_290), (true, vertices_386), (true, vertices_108), (true, vertices_276), (true, vertices_164), (true, vertices_292), (true, vertices_324), (true, vertices_388), (true, vertices_328), (true, vertices_336), (true, vertices_400), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 15 else
  if p.val = (false, vertices_595) then 16 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_547) then 1 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_108) then 19 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_784) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 7 422 162 1
cert_row_2 1 1 2 4 5 108
cert_row_4 2 0 3 4 7 8 818 274 2
cert_row_4 3 2 3 5 7 8 856 328 1
cert_rows
cert_pivot_2 6 1 0 2
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 162 422 1
cert_coverFacet 1 818
cert_cover_5 1 2 0 3 4 7 274 818 2
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 236
cert_cover_5 3 1 1 2 4 6 108 236 3
cert_coverFacet 4 364
cert_cover_5 4 1 1 2 4 7 108 364 3
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 856
cert_cover_5 7 3 2 3 5 7 328 856 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1114

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_1115.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1115

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [59, 285, 333, 617, 817, 961, 30, 78, 214, 554, 714, 178, 930, 436, 452, 269, 25, 41, 73, 49, 273, 545, 321, 577, 769, 14, 22, 70, 26, 42, 74, 522, 50, 146, 162, 546, 194, 642, 28, 76, 148, 276, 196, 324, 388, 552, 584, 176, 304, 416, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_59, vertices_285, vertices_333, vertices_617, vertices_817, vertices_961, vertices_30, vertices_78, vertices_214, vertices_554, vertices_714, vertices_178, vertices_930, vertices_436, vertices_452] (by decide +kernel)
  polygons := literalFinset [vertices_269, vertices_25, vertices_41, vertices_73, vertices_49, vertices_273, vertices_545, vertices_321, vertices_577, vertices_769, vertices_14, vertices_22, vertices_70, vertices_26, vertices_42, vertices_74, vertices_522, vertices_50, vertices_146, vertices_162, vertices_546, vertices_194, vertices_642, vertices_28, vertices_76, vertices_148, vertices_276, vertices_196, vertices_324, vertices_388, vertices_552, vertices_584, vertices_176, vertices_304, vertices_416, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_59), (false, vertices_285), (false, vertices_333), (false, vertices_617), (false, vertices_817), (false, vertices_961), (true, vertices_14), (true, vertices_22), (true, vertices_70), (true, vertices_74), (true, vertices_522), (true, vertices_146), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_642), (true, vertices_148), (true, vertices_196), (true, vertices_388), (true, vertices_176), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 25 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_59) then 16 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (false, vertices_961) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_194) then 8 else
  if p.val = (true, vertices_642) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 74 3
cert_row_4 1 0 1 3 5 6 214 22 3
cert_row_4 2 0 4 6 7 8 930 162 3
cert_row_4 3 1 3 4 6 7 436 148 2
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 78
cert_cover_2 1 1 0 2 5 14 78 3
cert_coverFacet 2 214
cert_cover_5 2 1 0 1 3 5 22 214 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 714
cert_cover_5 4 0 0 2 5 6 74 714 3
cert_coverFacet 5 178
cert_cover_2 5 3 0 4 6 50 178 3
cert_coverFacet 6 930
cert_cover_5 6 2 0 4 6 7 162 930 3
cert_coverFacet 7 436
cert_cover_5 7 3 1 3 4 6 148 436 2
cert_coverFacet 8 452
cert_cover_2 8 5 1 6 7 196 452 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1115

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_1116.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1116

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [59, 403, 611, 771, 901, 113, 721, 558, 282, 778, 364, 780, 468, 740, 376, 19, 35, 259, 515, 49, 81, 145, 97, 577, 385, 641, 769, 26, 42, 266, 522, 274, 546, 770, 44, 268, 524, 100, 548, 196, 324, 388, 644, 772, 56, 280, 360, 776, 112, 208, 336, 400, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_59, vertices_403, vertices_611, vertices_771, vertices_901, vertices_113, vertices_721, vertices_558, vertices_282, vertices_778, vertices_364, vertices_780, vertices_468, vertices_740, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_515, vertices_49, vertices_81, vertices_145, vertices_97, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_546, vertices_770, vertices_44, vertices_268, vertices_524, vertices_100, vertices_548, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_56, vertices_280, vertices_360, vertices_776, vertices_112, vertices_208, vertices_336, vertices_400, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_59), (false, vertices_403), (false, vertices_611), (false, vertices_771), (false, vertices_901), (false, vertices_113), (false, vertices_721), (true, vertices_266), (true, vertices_522), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_100), (true, vertices_548), (true, vertices_196), (true, vertices_324), (true, vertices_280), (true, vertices_360), (true, vertices_776), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_59) then 15 else
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_113) then 1 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_360) then 21 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_336) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_360), by decide +kernel⟩
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
cert_row_4 0 0 1 2 4 8 558 42 1
cert_row_2 1 2 4 5 7 360
cert_row_4 2 1 3 5 6 7 468 196 1
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 42 558 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 364
cert_cover_5 3 1 1 2 4 5 44 364 3
cert_coverFacet 4 780
cert_cover_2 4 2 1 7 8 268 780 3
cert_coverFacet 5 468
cert_cover_5 5 2 1 3 5 6 196 468 1
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 100 740 3
cert_coverFacet 7 376
cert_cover_5 7 1 2 3 4 5 56 376 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1116

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_1117.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1117

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [47, 205, 805, 581, 169, 849, 481, 30, 598, 550, 666, 682, 92, 472, 944, 13, 37, 69, 517, 41, 137, 161, 289, 193, 321, 577, 769, 14, 22, 38, 518, 26, 42, 650, 530, 546, 28, 76, 84, 548, 580, 88, 152, 168, 200, 336, 592, 400, 656, 784, 416, 672, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_47, vertices_205, vertices_805, vertices_581, vertices_169, vertices_849, vertices_481, vertices_30, vertices_598, vertices_550, vertices_666, vertices_682, vertices_92, vertices_472, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_517, vertices_41, vertices_137, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_769, vertices_14, vertices_22, vertices_38, vertices_518, vertices_26, vertices_42, vertices_650, vertices_530, vertices_546, vertices_28, vertices_76, vertices_84, vertices_548, vertices_580, vertices_88, vertices_152, vertices_168, vertices_200, vertices_336, vertices_592, vertices_400, vertices_656, vertices_784, vertices_416, vertices_672, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_47), (false, vertices_205), (false, vertices_805), (false, vertices_581), (false, vertices_169), (false, vertices_849), (false, vertices_481), (true, vertices_22), (true, vertices_518), (true, vertices_26), (true, vertices_650), (true, vertices_530), (true, vertices_546), (true, vertices_28), (true, vertices_84), (true, vertices_88), (true, vertices_152), (true, vertices_400), (true, vertices_656), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_47) then 15 else
  if p.val = (false, vertices_205) then 18 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_169) then 1 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_650) then 16 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_47), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_650), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 22 3
cert_row_2 1 0 2 6 8 650
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 3 4 6 7 8 944 400 1
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 598
cert_cover_5 1 0 0 1 3 5 22 598 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 666
cert_cover_5 3 1 0 2 3 6 26 666 3
cert_coverFacet 4 682
cert_cover_5 4 1 0 2 4 6 42 682 3
cert_coverFacet 5 92
cert_cover_2 5 2 1 3 5 28 92 3
cert_coverFacet 6 472
cert_cover_5 6 2 2 3 5 6 88 472 3
cert_coverFacet 7 944
cert_cover_5 7 3 3 4 6 7 400 944 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1117

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_1118.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1118

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 29, 45, 405, 677, 569, 961, 30, 110, 214, 538, 842, 466, 228, 744, 13, 21, 37, 133, 25, 41, 273, 529, 545, 385, 641, 769, 14, 22, 70, 26, 74, 522, 210, 274, 530, 322, 770, 28, 44, 148, 100, 164, 196, 536, 104, 552, 584, 400, 224, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_29, vertices_45, vertices_405, vertices_677, vertices_569, vertices_961, vertices_30, vertices_110, vertices_214, vertices_538, vertices_842, vertices_466, vertices_228, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_37, vertices_133, vertices_25, vertices_41, vertices_273, vertices_529, vertices_545, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_70, vertices_26, vertices_74, vertices_522, vertices_210, vertices_274, vertices_530, vertices_322, vertices_770, vertices_28, vertices_44, vertices_148, vertices_100, vertices_164, vertices_196, vertices_536, vertices_104, vertices_552, vertices_584, vertices_400, vertices_224, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_29), (false, vertices_45), (false, vertices_405), (false, vertices_677), (false, vertices_569), (false, vertices_961), (true, vertices_14), (true, vertices_22), (true, vertices_70), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_210), (true, vertices_322), (true, vertices_100), (true, vertices_196), (true, vertices_104), (true, vertices_584), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_45) then 1 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_22) then 3 else
  if p.val = (true, vertices_70) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_74) then 6 else
  if p.val = (true, vertices_522) then 7 else
  if p.val = (true, vertices_210) then 16 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_224) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_29), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 6 210
cert_row_4 1 0 1 2 4 5 110 14 3
cert_row_4 2 0 2 5 7 8 842 74 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 110
cert_cover_5 1 1 0 1 2 4 14 110 3
cert_coverFacet 2 214
cert_cover_5 2 0 0 1 3 5 22 214 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 842
cert_cover_5 4 2 0 2 5 7 74 842 3
cert_coverFacet 5 466
cert_cover_5 5 0 0 3 5 7 210 466 3
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 104 744 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1118

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_1119.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1119

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 709, 233, 809, 625, 897, 286, 142, 598, 646, 818, 898, 188, 244, 312, 41, 137, 265, 97, 545, 193, 577, 385, 641, 769, 14, 22, 134, 518, 138, 266, 274, 530, 386, 642, 770, 28, 140, 180, 84, 196, 580, 644, 56, 280, 168, 296, 112, 304, 560, 592, 224, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_709, vertices_233, vertices_809, vertices_625, vertices_897, vertices_286, vertices_142, vertices_598, vertices_646, vertices_818, vertices_898, vertices_188, vertices_244, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_265, vertices_97, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_134, vertices_518, vertices_138, vertices_266, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_28, vertices_140, vertices_180, vertices_84, vertices_196, vertices_580, vertices_644, vertices_56, vertices_280, vertices_168, vertices_296, vertices_112, vertices_304, vertices_560, vertices_592, vertices_224, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_709), (false, vertices_233), (false, vertices_809), (false, vertices_625), (false, vertices_897), (true, vertices_14), (true, vertices_22), (true, vertices_134), (true, vertices_518), (true, vertices_274), (true, vertices_530), (true, vertices_642), (true, vertices_770), (true, vertices_28), (true, vertices_140), (true, vertices_180), (true, vertices_84), (true, vertices_56), (true, vertices_280), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_180) then 19 else
  if p.val = (true, vertices_84) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_304) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 897 2 14 1 22 3 134 518 274 530 642 770 28 140 84 56 280 304 395 709 180 233 809 625
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
cert_coverFacet 4 818
cert_cover_5 4 3 0 3 4 7 274 818 2
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 188
cert_cover_5 6 0 1 2 3 4 28 188 3
cert_coverFacet 7 244
cert_cover_5 7 0 1 3 4 5 180 244 3
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1119

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_1120.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1120

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 659, 597, 617, 425, 241, 286, 558, 534, 394, 466, 300, 340, 484, 612, 643, 41, 137, 521, 81, 145, 529, 97, 161, 577, 14, 22, 518, 138, 266, 522, 146, 274, 530, 386, 44, 268, 84, 276, 532, 100, 292, 548, 324, 580, 296, 552, 392, 208, 336, 224, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_659, vertices_597, vertices_617, vertices_425, vertices_241, vertices_286, vertices_558, vertices_534, vertices_394, vertices_466, vertices_300, vertices_340, vertices_484, vertices_612] (by decide +kernel)
  polygons := literalFinset [vertices_643, vertices_41, vertices_137, vertices_521, vertices_81, vertices_145, vertices_529, vertices_97, vertices_161, vertices_577, vertices_14, vertices_22, vertices_518, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_44, vertices_268, vertices_84, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_296, vertices_552, vertices_392, vertices_208, vertices_336, vertices_224, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_659), (false, vertices_597), (false, vertices_617), (false, vertices_425), (false, vertices_241), (true, vertices_14), (true, vertices_22), (true, vertices_518), (true, vertices_266), (true, vertices_274), (true, vertices_386), (true, vertices_44), (true, vertices_268), (true, vertices_276), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_324), (true, vertices_336), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_324) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 14 3
cert_row_4 1 0 1 2 3 7 286 14 3
cert_row_4 2 0 3 5 6 7 466 146 2
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 8 2 0 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 1 0 1 2 3 14 286 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 4 14 558 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 466
cert_cover_5 4 2 0 3 5 6 146 466 2
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 100 484 3
cert_coverFacet 8 612
cert_cover_2 8 4 1 5 8 100 612 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1120

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_1122.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1122

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 229, 409, 625, 177, 961, 142, 526, 182, 566, 154, 282, 842, 620, 460, 49, 145, 273, 529, 97, 161, 193, 577, 385, 769, 14, 54, 134, 518, 26, 138, 266, 522, 146, 274, 530, 770, 76, 140, 524, 100, 164, 548, 196, 152, 280, 328, 584, 392, 176, 560, 608, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_229, vertices_409, vertices_625, vertices_177, vertices_961, vertices_142, vertices_526, vertices_182, vertices_566, vertices_154, vertices_282, vertices_842, vertices_620, vertices_460] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_54, vertices_134, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_770, vertices_76, vertices_140, vertices_524, vertices_100, vertices_164, vertices_548, vertices_196, vertices_152, vertices_280, vertices_328, vertices_584, vertices_392, vertices_176, vertices_560, vertices_608, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_229), (false, vertices_409), (false, vertices_625), (false, vertices_177), (false, vertices_961), (true, vertices_14), (true, vertices_54), (true, vertices_134), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_548), (true, vertices_328), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 25 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (false, vertices_961) then 26 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_54) then 17 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_522) then 7 else
  if p.val = (true, vertices_146) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_548) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_584) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 0 2 5 7 8 842 266 2
cert_row_4 2 1 2 4 5 8 620 76 2
cert_row_4 3 1 2 5 6 7 460 76 3
cert_rows
cert_pivot_2 3 0 4 1
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 182
cert_cover_5 2 0 0 1 3 6 54 182 3
cert_coverFacet 3 566
cert_cover_5 3 0 0 1 3 8 54 566 3
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 282
cert_cover_2 5 2 0 3 7 26 282 3
cert_coverFacet 6 842
cert_cover_5 6 1 0 2 5 7 266 842 2
cert_coverFacet 7 620
cert_cover_5 7 2 1 2 4 5 76 620 2
cert_coverFacet 8 460
cert_cover_5 8 3 1 2 5 6 76 460 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1122

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_1123.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1123

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 211, 419, 597, 809, 961, 158, 542, 170, 554, 428, 844, 340, 404, 464, 19, 35, 131, 81, 529, 289, 545, 193, 577, 385, 769, 30, 42, 138, 522, 146, 530, 162, 546, 140, 268, 524, 84, 148, 276, 532, 324, 580, 388, 168, 296, 552, 776, 208, 336, 400, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_211, vertices_419, vertices_597, vertices_809, vertices_961, vertices_158, vertices_542, vertices_170, vertices_554, vertices_428, vertices_844, vertices_340, vertices_404, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_81, vertices_529, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_30, vertices_42, vertices_138, vertices_522, vertices_146, vertices_530, vertices_162, vertices_546, vertices_140, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_324, vertices_580, vertices_388, vertices_168, vertices_296, vertices_552, vertices_776, vertices_208, vertices_336, vertices_400, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_211), (false, vertices_419), (false, vertices_597), (false, vertices_809), (false, vertices_961), (true, vertices_30), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_324), (true, vertices_388), (true, vertices_168), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 20 22 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 17 else
  if p.val = (false, vertices_211) then 18 else
  if p.val = (false, vertices_419) then 19 else
  if p.val = (false, vertices_597) then 14 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_30) then 15 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_30), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 1 2 4 6 7 428 140 2
cert_row_4 2 1 2 5 7 8 844 268 2
cert_rows_3
cert_pivot_3 4 0 1
cert_heightProof 3
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 6 30 158 3
cert_coverFacet 1 542
cert_cover_5 1 0 0 1 2 8 30 542 3
cert_coverFacet 2 170
cert_cover_2 2 2 0 4 6 42 170 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 428
cert_cover_5 4 1 1 2 4 6 140 428 2
cert_coverFacet 5 844
cert_cover_5 5 2 1 2 5 7 268 844 2
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 3 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1123

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_1124.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1124

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 527, 339, 707, 677, 453, 282, 538, 626, 572, 172, 396, 376, 424, 992, 15, 67, 259, 515, 133, 261, 517, 193, 321, 641, 26, 266, 522, 82, 274, 530, 578, 44, 140, 268, 524, 164, 548, 388, 56, 280, 536, 168, 296, 392, 112, 560, 336, 352, 608, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_527, vertices_339, vertices_707, vertices_677, vertices_453, vertices_282, vertices_538, vertices_626, vertices_572, vertices_172, vertices_396, vertices_376, vertices_424, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_15, vertices_67, vertices_259, vertices_515, vertices_133, vertices_261, vertices_517, vertices_193, vertices_321, vertices_641, vertices_26, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_578, vertices_44, vertices_140, vertices_268, vertices_524, vertices_164, vertices_548, vertices_388, vertices_56, vertices_280, vertices_536, vertices_168, vertices_296, vertices_392, vertices_112, vertices_560, vertices_336, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_527), (false, vertices_339), (false, vertices_707), (false, vertices_677), (false, vertices_453), (true, vertices_26), (true, vertices_530), (true, vertices_44), (true, vertices_140), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_112), (true, vertices_560), (true, vertices_352), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 21 15 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 16 else
  if p.val = (false, vertices_527) then 17 else
  if p.val = (false, vertices_339) then 19 else
  if p.val = (false, vertices_707) then 20 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_453) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_56) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 8 626 82 2
cert_row_4 1 1 2 3 4 8 572 44 2
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 282
cert_cover_2 0 2 0 3 7 26 282 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 626
cert_cover_5 2 0 0 3 4 5 82 626 2
cert_coverFacet 3 572
cert_cover_5 3 1 1 2 3 4 44 572 2
cert_coverFacet 4 172
cert_cover_2 4 2 1 4 6 44 172 3
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 376
cert_cover_5 6 2 2 3 4 5 56 376 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coverFacet 8 992
cert_cover_5 8 3 4 5 6 7 352 992 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1124

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_1125.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1125

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [143, 527, 403, 835, 613, 453, 154, 538, 818, 572, 236, 312, 408, 424, 992, 15, 131, 259, 515, 69, 133, 517, 321, 577, 385, 26, 138, 522, 146, 274, 530, 770, 44, 140, 524, 100, 548, 196, 56, 152, 280, 536, 168, 296, 392, 304, 560, 400, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_143, vertices_527, vertices_403, vertices_835, vertices_613, vertices_453, vertices_154, vertices_538, vertices_818, vertices_572, vertices_236, vertices_312, vertices_408, vertices_424, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_15, vertices_131, vertices_259, vertices_515, vertices_69, vertices_133, vertices_517, vertices_321, vertices_577, vertices_385, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_770, vertices_44, vertices_140, vertices_524, vertices_100, vertices_548, vertices_196, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_392, vertices_304, vertices_560, vertices_400, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_143), (false, vertices_527), (false, vertices_403), (false, vertices_835), (false, vertices_613), (false, vertices_453), (true, vertices_26), (true, vertices_530), (true, vertices_44), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_304), (true, vertices_560), (true, vertices_224), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 21 15 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_143) then 16 else
  if p.val = (false, vertices_527) then 17 else
  if p.val = (false, vertices_403) then 19 else
  if p.val = (false, vertices_835) then 20 else
  if p.val = (false, vertices_613) then 22 else
  if p.val = (false, vertices_453) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_56) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_143), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 7 8 818 274 2
cert_row_4 1 1 2 3 4 8 572 44 2
cert_row_4 2 1 2 4 5 6 236 44 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 3 1 4
cert_heightProof 4
cert_coverFacet 0 154
cert_cover_2 0 2 0 3 6 26 154 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 818
cert_cover_5 2 0 0 3 4 7 274 818 2
cert_coverFacet 3 572
cert_cover_5 3 1 1 2 3 4 44 572 2
cert_coverFacet 4 236
cert_cover_5 4 2 1 2 4 5 44 236 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coverFacet 8 992
cert_cover_5 8 3 4 5 6 7 224 992 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1125

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_1126.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1126

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 527, 357, 709, 313, 617, 390, 646, 570, 154, 394, 722, 468, 408, 880, 15, 69, 261, 517, 41, 265, 521, 97, 289, 577, 134, 262, 518, 26, 138, 266, 522, 146, 530, 386, 642, 196, 324, 388, 644, 56, 152, 280, 552, 392, 304, 560, 208, 336, 592, 400, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_527, vertices_357, vertices_709, vertices_313, vertices_617, vertices_390, vertices_646, vertices_570, vertices_154, vertices_394, vertices_722, vertices_468, vertices_408, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_15, vertices_69, vertices_261, vertices_517, vertices_41, vertices_265, vertices_521, vertices_97, vertices_289, vertices_577, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_642, vertices_196, vertices_324, vertices_388, vertices_644, vertices_56, vertices_152, vertices_280, vertices_552, vertices_392, vertices_304, vertices_560, vertices_208, vertices_336, vertices_592, vertices_400, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_527), (false, vertices_357), (false, vertices_709), (false, vertices_313), (false, vertices_617), (true, vertices_134), (true, vertices_26), (true, vertices_138), (true, vertices_146), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_388), (true, vertices_152), (true, vertices_392), (true, vertices_560), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 16 else
  if p.val = (false, vertices_527) then 17 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 26 3
cert_row_4 1 0 3 5 6 8 722 146 2
cert_row_4 2 1 3 5 6 7 468 196 1
cert_row_4 3 3 4 5 7 8 880 304 2
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 390
cert_cover_2 0 1 0 6 7 134 390 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 570
cert_cover_5 2 0 0 2 3 4 26 570 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 722
cert_cover_5 5 1 0 3 5 6 146 722 2
cert_coverFacet 6 468
cert_cover_5 6 2 1 3 5 6 196 468 1
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 880
cert_cover_5 8 3 3 4 5 7 304 880 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1126

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_1127.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1127

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 775, 181, 341, 841, 721, 174, 310, 362, 650, 778, 744, 432, 464, 480, 519, 21, 133, 261, 81, 145, 321, 577, 641, 769, 38, 134, 262, 42, 138, 266, 522, 290, 642, 770, 52, 276, 164, 104, 168, 328, 584, 648, 776, 176, 304, 208, 336, 400, 224, 352, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_775, vertices_181, vertices_341, vertices_841, vertices_721, vertices_174, vertices_310, vertices_362, vertices_650, vertices_778, vertices_744, vertices_432, vertices_464, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_519, vertices_21, vertices_133, vertices_261, vertices_81, vertices_145, vertices_321, vertices_577, vertices_641, vertices_769, vertices_38, vertices_134, vertices_262, vertices_42, vertices_138, vertices_266, vertices_522, vertices_290, vertices_642, vertices_770, vertices_52, vertices_276, vertices_164, vertices_104, vertices_168, vertices_328, vertices_584, vertices_648, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_400, vertices_224, vertices_352, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_775), (false, vertices_181), (false, vertices_341), (false, vertices_841), (false, vertices_721), (true, vertices_38), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_104), (true, vertices_168), (true, vertices_648), (true, vertices_304), (true, vertices_400), (true, vertices_224), (true, vertices_352), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_341) then 20 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_62 38 42 138 266 522 290 104 168 648 304 400 224 352 416 448 647 775 181 341 841 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 38 2
cert_row_4 1 0 1 2 4 6 174 38 2
cert_row_4 2 0 2 4 5 7 362 42 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 1 0 1 2 4 38 174 2
cert_coverFacet 1 310
cert_cover_5 1 0 0 1 3 4 38 310 2
cert_coverFacet 2 362
cert_cover_5 2 2 0 2 4 5 42 362 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 744
cert_cover_5 5 3 2 4 5 6 104 744 3
cert_coverFacet 6 432
cert_cover_2 6 4 3 6 7 176 432 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coverFacet 8 480
cert_cover_2 8 5 4 6 7 224 480 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1127

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_1128.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1128

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 589, 565, 421, 325, 737, 334, 314, 218, 402, 60, 540, 300, 728, 944, 37, 69, 261, 517, 161, 545, 193, 321, 577, 385, 26, 74, 266, 146, 274, 194, 322, 386, 28, 44, 76, 268, 524, 52, 532, 292, 324, 56, 216, 536, 296, 584, 304, 560, 400, 656, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_589, vertices_565, vertices_421, vertices_325, vertices_737, vertices_334, vertices_314, vertices_218, vertices_402, vertices_60, vertices_540, vertices_300, vertices_728, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_261, vertices_517, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_26, vertices_74, vertices_266, vertices_146, vertices_274, vertices_194, vertices_322, vertices_386, vertices_28, vertices_44, vertices_76, vertices_268, vertices_524, vertices_52, vertices_532, vertices_292, vertices_324, vertices_56, vertices_216, vertices_536, vertices_296, vertices_584, vertices_304, vertices_560, vertices_400, vertices_656, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_589), (false, vertices_565), (false, vertices_421), (false, vertices_325), (false, vertices_737), (true, vertices_26), (true, vertices_74), (true, vertices_266), (true, vertices_146), (true, vertices_274), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_56), (true, vertices_216), (true, vertices_536), (true, vertices_296), (true, vertices_304), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_216) then 22 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
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
cert_row_4 0 0 1 2 5 7 334 74 1
cert_row_2 1 2 3 5 6 216
cert_row_4 2 0 2 3 4 7 314 26 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 1 5 0 3
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 74 334 1
cert_coverFacet 1 314
cert_cover_5 1 2 0 2 3 4 26 314 3
cert_coverFacet 2 218
cert_cover_5 2 1 0 2 3 5 26 218 3
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 60
cert_cover_2 4 2 1 3 4 28 60 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 728
cert_cover_5 7 1 2 3 5 8 216 728 3
cert_coverFacet 8 944
cert_cover_5 8 3 3 4 6 7 304 944 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1128

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_1129.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1129

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [211, 595, 541, 173, 613, 153, 481, 838, 794, 434, 450, 364, 780, 184, 312, 83, 13, 37, 517, 25, 137, 145, 529, 97, 161, 193, 577, 146, 274, 530, 194, 322, 578, 386, 770, 44, 268, 524, 100, 324, 580, 772, 56, 152, 280, 536, 168, 296, 776, 176, 304, 352, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_595, vertices_541, vertices_173, vertices_613, vertices_153, vertices_481, vertices_838, vertices_794, vertices_434, vertices_450, vertices_364, vertices_780, vertices_184, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_83, vertices_13, vertices_37, vertices_517, vertices_25, vertices_137, vertices_145, vertices_529, vertices_97, vertices_161, vertices_193, vertices_577, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_44, vertices_268, vertices_524, vertices_100, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_776, vertices_176, vertices_304, vertices_352, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_595), (false, vertices_541), (false, vertices_173), (false, vertices_613), (false, vertices_153), (false, vertices_481), (true, vertices_274), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_268), (true, vertices_324), (true, vertices_772), (true, vertices_56), (true, vertices_280), (true, vertices_296), (true, vertices_776), (true, vertices_176), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 15 else
  if p.val = (false, vertices_595) then 16 else
  if p.val = (false, vertices_541) then 18 else
  if p.val = (false, vertices_173) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_153) then 0 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_153), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_4 0 0 3 4 6 7 434 146 2
cert_row_4 1 0 2 3 7 8 794 274 1
cert_row_4 2 0 1 5 7 8 838 322 1
cert_row_4 3 1 2 4 5 7 364 44 3
cert_rows
cert_pivot_2 6 3 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 2 0 1 5 7 322 838 1
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 274 794 1
cert_coverFacet 2 434
cert_cover_5 2 0 0 3 4 6 146 434 2
cert_coverFacet 3 450
cert_cover_2 3 5 0 6 7 194 450 3
cert_coverFacet 4 364
cert_cover_5 4 3 1 2 4 5 44 364 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1129

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_1130.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1130

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 789, 233, 625, 465, 801, 286, 590, 806, 618, 170, 394, 220, 596, 408, 81, 273, 529, 97, 161, 289, 545, 193, 385, 769, 14, 262, 518, 42, 586, 138, 266, 162, 290, 546, 386, 28, 76, 84, 276, 532, 580, 772, 152, 280, 104, 168, 200, 392, 208, 592, 400, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_789, vertices_233, vertices_625, vertices_465, vertices_801, vertices_286, vertices_590, vertices_806, vertices_618, vertices_170, vertices_394, vertices_220, vertices_596, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_385, vertices_769, vertices_14, vertices_262, vertices_518, vertices_42, vertices_586, vertices_138, vertices_266, vertices_162, vertices_290, vertices_546, vertices_386, vertices_28, vertices_76, vertices_84, vertices_276, vertices_532, vertices_580, vertices_772, vertices_152, vertices_280, vertices_104, vertices_168, vertices_200, vertices_392, vertices_208, vertices_592, vertices_400, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_789), (false, vertices_233), (false, vertices_625), (false, vertices_465), (false, vertices_801), (true, vertices_14), (true, vertices_262), (true, vertices_518), (true, vertices_42), (true, vertices_586), (true, vertices_138), (true, vertices_266), (true, vertices_546), (true, vertices_28), (true, vertices_76), (true, vertices_84), (true, vertices_580), (true, vertices_152), (true, vertices_280), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_586) then 17 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
cert_nodeAtPriority_40 801 14 262 518 42 138 266 546 28 76 84 580 152 280 392 419 586 789 233 625 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 262 2
cert_row_2 1 0 2 5 8 586
cert_row_4 2 0 1 2 3 7 286 14 3
cert_row_4 3 1 2 3 5 6 220 28 3
cert_rows
cert_pivot_2 4 8 0 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 2 0 1 2 3 14 286 3
cert_coverFacet 1 590
cert_cover_5 1 1 0 1 2 5 14 590 3
cert_coverFacet 2 806
cert_cover_5 2 0 0 1 4 7 262 806 2
cert_coverFacet 3 618
cert_cover_5 3 1 0 2 4 5 42 618 3
cert_coverFacet 4 170
cert_cover_2 4 2 0 4 6 42 170 3
cert_coverFacet 5 394
cert_cover_2 5 2 0 6 7 138 394 3
cert_coverFacet 6 220
cert_cover_5 6 3 1 2 3 5 28 220 3
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1130

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3663 : Certifies 3663 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1100.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3664 : Certifies 3664 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1101.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3665 : Certifies 3665 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1102.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3666 : Certifies 3666 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1103.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3667 : Certifies 3667 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1104.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3668 : Certifies 3668 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1105.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3669 : Certifies 3669 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1106.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3670 : Certifies 3670 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1107.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3671 : Certifies 3671 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1108.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3672 : Certifies 3672 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1109.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3673 : Certifies 3673 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1110.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3674 : Certifies 3674 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1111.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3675 : Certifies 3675 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1112.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3676 : Certifies 3676 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1113.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3677 : Certifies 3677 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1114.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3678 : Certifies 3678 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1115.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3679 : Certifies 3679 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1116.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3680 : Certifies 3680 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1117.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3681 : Certifies 3681 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1118.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3682 : Certifies 3682 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1119.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3683 : Certifies 3683 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1120.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3684 : Certifies 3684 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1122.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3685 : Certifies 3685 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1123.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3686 : Certifies 3686 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1124.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3687 : Certifies 3687 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1125.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3688 : Certifies 3688 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1126.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3689 : Certifies 3689 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1127.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3690 : Certifies 3690 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1128.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3691 : Certifies 3691 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1129.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3692 : Certifies 3692 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1130.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B121 (j : Fin 30) :
    Certifies (3663 + j.val) := by
  fin_cases j
  · exact projection_3663
  · exact projection_3664
  · exact projection_3665
  · exact projection_3666
  · exact projection_3667
  · exact projection_3668
  · exact projection_3669
  · exact projection_3670
  · exact projection_3671
  · exact projection_3672
  · exact projection_3673
  · exact projection_3674
  · exact projection_3675
  · exact projection_3676
  · exact projection_3677
  · exact projection_3678
  · exact projection_3679
  · exact projection_3680
  · exact projection_3681
  · exact projection_3682
  · exact projection_3683
  · exact projection_3684
  · exact projection_3685
  · exact projection_3686
  · exact projection_3687
  · exact projection_3688
  · exact projection_3689
  · exact projection_3690
  · exact projection_3691
  · exact projection_3692

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
