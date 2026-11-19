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
/- Source: ProjectionCertificates/R_m15e10q1_0333.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0333

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 557, 181, 789, 361, 777, 417, 598, 150, 710, 338, 482, 676, 856, 744, 21, 37, 517, 41, 265, 521, 145, 273, 161, 289, 385, 769, 22, 582, 134, 82, 146, 274, 194, 322, 386, 148, 532, 164, 548, 644, 104, 552, 328, 584, 776, 336, 592, 784, 224, 352, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_557, vertices_181, vertices_789, vertices_361, vertices_777, vertices_417, vertices_598, vertices_150, vertices_710, vertices_338, vertices_482, vertices_676, vertices_856, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_517, vertices_41, vertices_265, vertices_521, vertices_145, vertices_273, vertices_161, vertices_289, vertices_385, vertices_769, vertices_22, vertices_582, vertices_134, vertices_82, vertices_146, vertices_274, vertices_194, vertices_322, vertices_386, vertices_148, vertices_532, vertices_164, vertices_548, vertices_644, vertices_104, vertices_552, vertices_328, vertices_584, vertices_776, vertices_336, vertices_592, vertices_784, vertices_224, vertices_352, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_557), (false, vertices_181), (false, vertices_789), (false, vertices_361), (false, vertices_777), (false, vertices_417), (true, vertices_22), (true, vertices_582), (true, vertices_134), (true, vertices_82), (true, vertices_194), (true, vertices_322), (true, vertices_644), (true, vertices_584), (true, vertices_336), (true, vertices_592), (true, vertices_224), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 15 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_417) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_582) then 16 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 777 1 417 22 134 82 194 322 644 584 336 592 224 672 704 403 582 557 181 789 361
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 8 582
cert_row_4 1 0 4 5 6 7 482 194 1
cert_row_4 2 2 3 5 7 8 856 328 1
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 1 0 3 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 22 598 3
cert_coverFacet 1 150
cert_cover_2 1 1 0 3 6 22 150 3
cert_coverFacet 2 710
cert_cover_5 2 0 0 1 5 6 582 710 3
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 482
cert_cover_5 4 1 0 4 5 6 194 482 1
cert_coverFacet 5 676
cert_cover_2 5 4 1 6 8 164 676 3
cert_coverFacet 6 856
cert_cover_5 6 2 2 3 5 7 328 856 1
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 104 744 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0333

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0334.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0334

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 675, 195, 323, 565, 457, 433, 710, 842, 316, 796, 236, 588, 676, 424, 67, 131, 259, 515, 49, 273, 529, 161, 545, 193, 321, 385, 194, 322, 578, 642, 770, 284, 44, 76, 524, 52, 532, 164, 548, 196, 580, 644, 168, 296, 200, 328, 584, 392, 776, 304, 784, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_675, vertices_195, vertices_323, vertices_565, vertices_457, vertices_433, vertices_710, vertices_842, vertices_316, vertices_796, vertices_236, vertices_588, vertices_676, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_49, vertices_273, vertices_529, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_284, vertices_44, vertices_76, vertices_524, vertices_52, vertices_532, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_168, vertices_296, vertices_200, vertices_328, vertices_584, vertices_392, vertices_776, vertices_304, vertices_784, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_675), (false, vertices_195), (false, vertices_323), (false, vertices_565), (false, vertices_457), (false, vertices_433), (true, vertices_578), (true, vertices_284), (true, vertices_44), (true, vertices_76), (true, vertices_524), (true, vertices_164), (true, vertices_196), (true, vertices_580), (true, vertices_644), (true, vertices_168), (true, vertices_296), (true, vertices_584), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_323) then 1 else
  if p.val = (false, vertices_565) then 18 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_284) then 19 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_776) then 13 else
  0
cert_priority
cert_nodeAtPriority_44 195 323 578 44 76 524 164 196 580 644 168 296 584 776 787 675 565 284 457 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 7 284
cert_row_4 1 0 2 5 7 8 842 322 1
cert_row_4 2 0 1 5 6 8 710 194 1
cert_row_4 3 1 2 4 5 6 236 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 2 0 1 5 6 194 710 1
cert_coverFacet 1 842
cert_cover_5 1 1 0 2 5 7 322 842 1
cert_coverFacet 2 316
cert_cover_5 2 0 1 2 3 4 284 316 3
cert_coverFacet 3 796
cert_cover_5 3 0 1 2 3 8 284 796 3
cert_coverFacet 4 236
cert_cover_5 4 3 1 2 4 5 44 236 3
cert_coverFacet 5 588
cert_cover_2 5 2 1 5 8 76 588 3
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0334

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0335.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0335

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 661, 453, 601, 209, 865, 422, 646, 186, 666, 618, 802, 376, 432, 464, 133, 261, 517, 81, 145, 529, 193, 321, 577, 769, 134, 262, 518, 154, 42, 522, 162, 290, 546, 642, 770, 388, 644, 56, 88, 536, 104, 584, 176, 304, 208, 336, 400, 656, 352, 608, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_661, vertices_453, vertices_601, vertices_209, vertices_865, vertices_422, vertices_646, vertices_186, vertices_666, vertices_618, vertices_802, vertices_376, vertices_432, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_769, vertices_134, vertices_262, vertices_518, vertices_154, vertices_42, vertices_522, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_388, vertices_644, vertices_56, vertices_88, vertices_536, vertices_104, vertices_584, vertices_176, vertices_304, vertices_208, vertices_336, vertices_400, vertices_656, vertices_352, vertices_608, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_661), (false, vertices_453), (false, vertices_601), (false, vertices_209), (false, vertices_865), (true, vertices_134), (true, vertices_154), (true, vertices_42), (true, vertices_522), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_56), (true, vertices_104), (true, vertices_176), (true, vertices_304), (true, vertices_336), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_601) then 22 else
  if p.val = (false, vertices_209) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_154) then 17 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_34 209 134 42 522 162 290 546 642 56 104 176 304 336 400 416 775 154 661 453 601 865
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 7 422 134 2
cert_row_2 1 0 2 3 6 154
cert_row_4 2 0 2 4 5 8 618 42 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 134 422 2
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 186
cert_cover_5 2 1 0 2 3 4 154 186 3
cert_coverFacet 3 666
cert_cover_5 3 1 0 2 3 8 154 666 3
cert_coverFacet 4 618
cert_cover_5 4 2 0 2 4 5 42 618 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 56 376 3
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0335

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0336.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0336

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 611, 419, 285, 149, 805, 401, 242, 706, 668, 844, 376, 728, 432, 864, 35, 131, 515, 21, 133, 261, 517, 145, 273, 289, 545, 385, 98, 162, 194, 578, 642, 28, 268, 524, 148, 644, 772, 88, 664, 280, 328, 584, 112, 176, 304, 208, 400, 352, 608, 416, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_611, vertices_419, vertices_285, vertices_149, vertices_805, vertices_401, vertices_242, vertices_706, vertices_668, vertices_844, vertices_376, vertices_728, vertices_432, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_21, vertices_133, vertices_261, vertices_517, vertices_145, vertices_273, vertices_289, vertices_545, vertices_385, vertices_98, vertices_162, vertices_194, vertices_578, vertices_642, vertices_28, vertices_268, vertices_524, vertices_148, vertices_644, vertices_772, vertices_88, vertices_664, vertices_280, vertices_328, vertices_584, vertices_112, vertices_176, vertices_304, vertices_208, vertices_400, vertices_352, vertices_608, vertices_416, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_611), (false, vertices_419), (false, vertices_285), (false, vertices_149), (false, vertices_805), (false, vertices_401), (true, vertices_194), (true, vertices_524), (true, vertices_88), (true, vertices_664), (true, vertices_328), (true, vertices_584), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_208), (true, vertices_352), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_419) then 17 else
  if p.val = (false, vertices_285) then 19 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_664) then 22 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_704) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 6 242 98 1
cert_row_2 1 2 3 6 8 664
cert_row_4 2 1 2 5 7 8 844 268 2
cert_row_4 3 2 3 4 5 7 376 88 2
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 242
cert_cover_5 0 0 0 3 4 5 98 242 1
cert_coverFacet 1 706
cert_cover_2 1 5 0 6 8 194 706 3
cert_coverFacet 2 668
cert_cover_5 2 1 1 2 3 6 28 668 3
cert_coverFacet 3 844
cert_cover_5 3 2 1 2 5 7 268 844 2
cert_coverFacet 4 376
cert_cover_5 4 3 2 3 4 5 88 376 2
cert_coverFacet 5 728
cert_cover_5 5 1 2 3 5 6 88 728 3
cert_coverFacet 6 432
cert_cover_2 6 4 3 6 7 176 432 3
cert_coverFacet 7 864
cert_cover_2 7 5 4 7 8 352 864 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0336

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0337.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0337

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 179, 611, 781, 309, 149, 801, 482, 706, 348, 668, 728, 872, 432, 464, 35, 131, 515, 21, 133, 261, 517, 49, 145, 289, 545, 769, 98, 162, 194, 578, 642, 28, 268, 524, 148, 276, 644, 88, 664, 328, 584, 776, 176, 304, 208, 336, 400, 352, 608, 416, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_179, vertices_611, vertices_781, vertices_309, vertices_149, vertices_801, vertices_482, vertices_706, vertices_348, vertices_668, vertices_728, vertices_872, vertices_432, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_21, vertices_133, vertices_261, vertices_517, vertices_49, vertices_145, vertices_289, vertices_545, vertices_769, vertices_98, vertices_162, vertices_194, vertices_578, vertices_642, vertices_28, vertices_268, vertices_524, vertices_148, vertices_276, vertices_644, vertices_88, vertices_664, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_400, vertices_352, vertices_608, vertices_416, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_179), (false, vertices_611), (false, vertices_781), (false, vertices_309), (false, vertices_149), (false, vertices_801), (true, vertices_194), (true, vertices_28), (true, vertices_88), (true, vertices_664), (true, vertices_328), (true, vertices_584), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_352), (true, vertices_416), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_179) then 16 else
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_309) then 20 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_801) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_664) then 22 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_448) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 6 7 482 98 3
cert_row_2 1 2 3 6 8 664
cert_row_4 2 1 2 3 5 7 348 28 3
cert_row_4 3 2 4 5 7 8 872 328 1
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 482
cert_cover_5 0 0 0 4 5 6 98 482 3
cert_coverFacet 1 706
cert_cover_2 1 5 0 6 8 194 706 3
cert_coverFacet 2 348
cert_cover_5 2 2 1 2 3 5 28 348 3
cert_coverFacet 3 668
cert_cover_5 3 1 1 2 3 6 28 668 3
cert_coverFacet 4 728
cert_cover_5 4 1 2 3 5 6 88 728 3
cert_coverFacet 5 872
cert_cover_5 5 3 2 4 5 7 328 872 1
cert_coverFacet 6 432
cert_cover_2 6 4 3 6 7 176 432 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0337

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0338.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0338

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 789, 357, 581, 537, 713, 465, 282, 682, 298, 242, 370, 812, 740, 792, 69, 261, 517, 25, 137, 521, 145, 273, 529, 193, 321, 577, 26, 42, 138, 266, 114, 146, 274, 162, 290, 100, 292, 548, 580, 772, 280, 536, 296, 552, 648, 776, 208, 336, 784, 224, 352, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_789, vertices_357, vertices_581, vertices_537, vertices_713, vertices_465, vertices_282, vertices_682, vertices_298, vertices_242, vertices_370, vertices_812, vertices_740, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_25, vertices_137, vertices_521, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_26, vertices_42, vertices_138, vertices_266, vertices_114, vertices_146, vertices_274, vertices_162, vertices_290, vertices_100, vertices_292, vertices_548, vertices_580, vertices_772, vertices_280, vertices_536, vertices_296, vertices_552, vertices_648, vertices_776, vertices_208, vertices_336, vertices_784, vertices_224, vertices_352, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_789), (false, vertices_357), (false, vertices_581), (false, vertices_537), (false, vertices_713), (false, vertices_465), (true, vertices_42), (true, vertices_266), (true, vertices_114), (true, vertices_274), (true, vertices_162), (true, vertices_290), (true, vertices_548), (true, vertices_280), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 15 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_114) then 16 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 581 1 537 42 266 274 162 290 548 280 296 552 776 224 672 155 114 789 357 713 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 5 114
cert_row_4 1 0 2 4 6 8 682 42 3
cert_row_4 2 1 2 4 7 8 812 292 1
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 282
cert_cover_2 0 2 0 3 7 26 282 3
cert_coverFacet 1 682
cert_cover_5 1 1 0 2 4 6 42 682 3
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 242
cert_cover_5 3 0 0 3 4 6 114 242 3
cert_coverFacet 4 370
cert_cover_5 4 0 0 3 4 7 114 370 3
cert_coverFacet 5 812
cert_cover_5 5 2 1 2 4 7 292 812 1
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 100 740 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0338

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0339.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0339

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 565, 793, 113, 465, 737, 542, 270, 678, 390, 778, 60, 236, 460, 376, 49, 81, 273, 529, 97, 545, 193, 385, 641, 769, 14, 134, 262, 518, 266, 522, 386, 642, 770, 28, 44, 204, 268, 52, 532, 164, 548, 388, 56, 280, 536, 104, 328, 776, 112, 336, 224, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_565, vertices_793, vertices_113, vertices_465, vertices_737, vertices_542, vertices_270, vertices_678, vertices_390, vertices_778, vertices_60, vertices_236, vertices_460, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_273, vertices_529, vertices_97, vertices_545, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_134, vertices_262, vertices_518, vertices_266, vertices_522, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_204, vertices_268, vertices_52, vertices_532, vertices_164, vertices_548, vertices_388, vertices_56, vertices_280, vertices_536, vertices_104, vertices_328, vertices_776, vertices_112, vertices_336, vertices_224, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_565), (false, vertices_793), (false, vertices_113), (false, vertices_465), (false, vertices_737), (true, vertices_14), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_522), (true, vertices_28), (true, vertices_44), (true, vertices_204), (true, vertices_268), (true, vertices_164), (true, vertices_388), (true, vertices_56), (true, vertices_104), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_565) then 18 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_113) then 0 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_204) then 19 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_104) then 13 else
  if p.val = (true, vertices_328) then 14 else
  0
cert_priority
cert_nodeAtPriority_9 0 113 1 14 134 262 518 266 522 28 44 268 164 388 56 104 328 899 565 204 793 465 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 5 7 376 56 3
cert_row_2 1 1 2 5 6 204
cert_row_4 2 0 1 2 3 8 542 14 3
cert_row_4 3 0 1 4 6 8 678 134 2
cert_rows
cert_pivot_2 7 5 2 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 2 0 1 2 3 14 542 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 678
cert_cover_5 2 3 0 1 4 6 134 678 2
cert_coverFacet 3 390
cert_cover_2 3 1 0 6 7 134 390 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 236
cert_cover_5 6 1 1 2 4 5 44 236 3
cert_coverFacet 7 460
cert_cover_5 7 1 1 2 5 7 204 460 3
cert_coverFacet 8 376
cert_cover_5 8 0 2 3 4 5 56 376 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0339

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0340.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0340

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 395, 227, 579, 681, 777, 625, 598, 454, 820, 468, 248, 312, 408, 808, 67, 131, 259, 515, 137, 265, 521, 97, 161, 545, 577, 769, 70, 262, 518, 194, 578, 386, 84, 276, 532, 452, 772, 56, 152, 280, 168, 296, 552, 392, 776, 112, 304, 560, 208, 592, 400, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_395, vertices_227, vertices_579, vertices_681, vertices_777, vertices_625, vertices_598, vertices_454, vertices_820, vertices_468, vertices_248, vertices_312, vertices_408, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_577, vertices_769, vertices_70, vertices_262, vertices_518, vertices_194, vertices_578, vertices_386, vertices_84, vertices_276, vertices_532, vertices_452, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_392, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_592, vertices_400, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_395), (false, vertices_227), (false, vertices_579), (false, vertices_681), (false, vertices_777), (false, vertices_625), (true, vertices_70), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_452), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_304), (true, vertices_208), (true, vertices_400), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_227) then 17 else
  if p.val = (false, vertices_579) then 0 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_452) then 19 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
cert_nodeAtPriority_47 579 777 70 84 276 532 56 152 280 296 304 208 400 800 775 395 227 452 681 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 70 2
cert_row_4 1 1 3 4 7 8 820 276 2
cert_row_2 2 1 5 6 7 452
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 70 598 2
cert_coverFacet 1 454
cert_cover_5 1 2 0 1 5 6 70 454 3
cert_coverFacet 2 820
cert_cover_5 2 1 1 3 4 7 276 820 2
cert_coverFacet 3 468
cert_cover_5 3 2 1 3 5 6 84 468 3
cert_coverFacet 4 248
cert_cover_5 4 3 2 3 4 5 56 248 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0340

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0341.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0341

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 157, 789, 229, 581, 537, 681, 838, 234, 298, 458, 802, 468, 824, 408, 21, 69, 133, 517, 25, 137, 521, 529, 97, 161, 545, 577, 42, 202, 266, 98, 290, 546, 322, 578, 770, 148, 276, 196, 324, 580, 772, 152, 280, 536, 168, 296, 552, 392, 400, 784, 224, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_157, vertices_789, vertices_229, vertices_581, vertices_537, vertices_681, vertices_838, vertices_234, vertices_298, vertices_458, vertices_802, vertices_468, vertices_824, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_133, vertices_517, vertices_25, vertices_137, vertices_521, vertices_529, vertices_97, vertices_161, vertices_545, vertices_577, vertices_42, vertices_202, vertices_266, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_148, vertices_276, vertices_196, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_392, vertices_400, vertices_784, vertices_224, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_157), (false, vertices_789), (false, vertices_229), (false, vertices_581), (false, vertices_537), (false, vertices_681), (true, vertices_42), (true, vertices_202), (true, vertices_266), (true, vertices_290), (true, vertices_322), (true, vertices_770), (true, vertices_324), (true, vertices_280), (true, vertices_296), (true, vertices_392), (true, vertices_400), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 15 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_229) then 20 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_202) then 16 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 581 1 537 42 266 290 322 770 324 280 296 392 400 800 448 611 202 157 789 229 681
cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 7 8 824 280 2
cert_row_2 1 0 2 5 6 202
cert_row_4 2 0 1 5 7 8 838 322 1
cert_row_4 3 1 3 5 6 7 468 148 2
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 2 0 1 5 7 322 838 1
cert_coverFacet 1 234
cert_cover_5 1 1 0 2 4 5 42 234 3
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 458
cert_cover_5 3 1 0 2 5 7 202 458 3
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 468
cert_cover_5 5 3 1 3 5 6 148 468 2
cert_coverFacet 6 824
cert_cover_5 6 0 2 3 4 7 280 824 2
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0341

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0342.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0342

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 653, 569, 345, 393, 241, 673, 398, 710, 774, 370, 818, 610, 796, 736, 25, 137, 265, 521, 49, 81, 161, 545, 193, 321, 385, 641, 134, 262, 518, 306, 98, 546, 194, 322, 578, 386, 770, 140, 268, 524, 644, 772, 280, 536, 392, 112, 560, 336, 784, 224, 608, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_653, vertices_569, vertices_345, vertices_393, vertices_241, vertices_673, vertices_398, vertices_710, vertices_774, vertices_370, vertices_818, vertices_610, vertices_796, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_521, vertices_49, vertices_81, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_134, vertices_262, vertices_518, vertices_306, vertices_98, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_140, vertices_268, vertices_524, vertices_644, vertices_772, vertices_280, vertices_536, vertices_392, vertices_112, vertices_560, vertices_336, vertices_784, vertices_224, vertices_608, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_653), (false, vertices_569), (false, vertices_345), (false, vertices_393), (false, vertices_241), (false, vertices_673), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_306), (true, vertices_98), (true, vertices_546), (true, vertices_578), (true, vertices_770), (true, vertices_268), (true, vertices_772), (true, vertices_784), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_569) then 20 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_673) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_306) then 16 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_306), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
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
cert_row_2 0 0 3 4 7 306
cert_row_4 1 0 1 5 6 8 710 134 2
cert_row_4 2 0 1 2 6 7 398 134 2
cert_row_4 3 1 2 3 7 8 796 268 2
cert_rows
cert_pivot_2 4 5 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 2 0 1 2 6 134 398 2
cert_coverFacet 1 710
cert_cover_5 1 1 0 1 5 6 134 710 2
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 370
cert_cover_5 3 0 0 3 4 5 306 370 3
cert_coverFacet 4 818
cert_cover_5 4 0 0 3 4 8 306 818 3
cert_coverFacet 5 610
cert_cover_2 5 4 0 5 8 98 610 3
cert_coverFacet 6 796
cert_cover_5 6 3 1 2 3 7 268 796 2
cert_coverFacet 7 736
cert_cover_2 7 5 4 6 8 224 736 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0342

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0343.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0343

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 781, 421, 645, 313, 153, 241, 838, 218, 346, 778, 738, 372, 612, 676, 133, 261, 517, 25, 137, 265, 521, 49, 145, 161, 289, 641, 90, 138, 266, 522, 194, 322, 578, 642, 770, 100, 164, 292, 548, 324, 580, 644, 772, 152, 280, 776, 112, 304, 208, 336, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_781, vertices_421, vertices_645, vertices_313, vertices_153, vertices_241, vertices_838, vertices_218, vertices_346, vertices_778, vertices_738, vertices_372, vertices_612, vertices_676] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_161, vertices_289, vertices_641, vertices_90, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_100, vertices_164, vertices_292, vertices_548, vertices_324, vertices_580, vertices_644, vertices_772, vertices_152, vertices_280, vertices_776, vertices_112, vertices_304, vertices_208, vertices_336, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_781), (false, vertices_421), (false, vertices_645), (false, vertices_313), (false, vertices_153), (false, vertices_241), (true, vertices_90), (true, vertices_266), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_100), (true, vertices_548), (true, vertices_324), (true, vertices_580), (true, vertices_336), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_153) then 1 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_90) then 16 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 645 1 153 266 194 322 578 770 100 548 324 580 336 608 672 651 90 781 421 313 241
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
cert_coverFacet 5 372
cert_cover_5 5 3 1 3 4 5 100 372 1
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 676
cert_cover_2 7 4 1 6 8 164 676 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0343

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0344.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0344

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 595, 675, 291, 421, 337, 961, 302, 558, 538, 604, 204, 396, 740, 472, 19, 35, 259, 515, 81, 273, 161, 289, 321, 577, 385, 641, 46, 26, 266, 522, 530, 290, 546, 76, 140, 268, 524, 164, 292, 548, 196, 580, 388, 88, 280, 536, 200, 392, 336, 592, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_595, vertices_675, vertices_291, vertices_421, vertices_337, vertices_961, vertices_302, vertices_558, vertices_538, vertices_604, vertices_204, vertices_396, vertices_740, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_515, vertices_81, vertices_273, vertices_161, vertices_289, vertices_321, vertices_577, vertices_385, vertices_641, vertices_46, vertices_26, vertices_266, vertices_522, vertices_530, vertices_290, vertices_546, vertices_76, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_88, vertices_280, vertices_536, vertices_200, vertices_392, vertices_336, vertices_592, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_595), (false, vertices_675), (false, vertices_291), (false, vertices_421), (false, vertices_337), (false, vertices_961), (true, vertices_46), (true, vertices_522), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_548), (true, vertices_196), (true, vertices_580), (true, vertices_88), (true, vertices_536), (true, vertices_200), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 21 22 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 18 else
  if p.val = (false, vertices_595) then 19 else
  if p.val = (false, vertices_675) then 20 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_421) then 15 else
  if p.val = (false, vertices_337) then 1 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_46) then 16 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_392) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_2 0 0 1 2 4 46
cert_row_4 1 1 4 5 6 8 740 164 2
cert_row_4 2 1 2 3 5 8 604 76 2
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 7 46 302 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 8 46 558 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 604
cert_cover_5 3 2 1 2 3 5 76 604 2
cert_coverFacet 4 204
cert_cover_2 4 2 1 5 6 76 204 3
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 740
cert_cover_5 6 1 1 4 5 6 164 740 2
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 88 472 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0344

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0345.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0345

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 837, 217, 793, 593, 481, 782, 358, 550, 186, 570, 418, 740, 688, 720, 25, 137, 265, 81, 529, 193, 321, 577, 385, 769, 38, 262, 518, 58, 138, 266, 522, 162, 290, 546, 386, 100, 548, 324, 580, 772, 152, 536, 776, 176, 560, 208, 592, 656, 224, 352, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_837, vertices_217, vertices_793, vertices_593, vertices_481, vertices_782, vertices_358, vertices_550, vertices_186, vertices_570, vertices_418, vertices_740, vertices_688, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_81, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_38, vertices_262, vertices_518, vertices_58, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_152, vertices_536, vertices_776, vertices_176, vertices_560, vertices_208, vertices_592, vertices_656, vertices_224, vertices_352, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_837), (false, vertices_217), (false, vertices_793), (false, vertices_593), (false, vertices_481), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_58), (true, vertices_522), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_100), (true, vertices_548), (true, vertices_176), (true, vertices_560), (true, vertices_656), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_793) then 22 else
  if p.val = (false, vertices_593) then 0 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_58) then 17 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 593 38 262 518 522 162 290 546 100 548 176 560 656 672 704 395 58 837 217 793 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 4 58
cert_row_4 1 0 1 2 7 8 782 262 2
cert_row_4 2 0 1 4 5 7 358 38 3
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 262 782 2
cert_coverFacet 1 358
cert_cover_5 1 2 0 1 4 5 38 358 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 186
cert_cover_5 3 0 0 2 3 6 58 186 3
cert_coverFacet 4 570
cert_cover_5 4 0 0 2 3 8 58 570 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 100 740 3
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coverFacet 8 720
cert_cover_2 8 5 3 6 8 208 720 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0345

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0346.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0346

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 651, 179, 307, 357, 677, 602, 154, 786, 852, 612, 472, 744, 432, 480, 51, 131, 259, 515, 37, 261, 517, 161, 289, 641, 26, 138, 522, 146, 274, 530, 770, 100, 548, 324, 580, 772, 88, 152, 200, 584, 648, 176, 304, 336, 592, 400, 784, 224, 352, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_651, vertices_179, vertices_307, vertices_357, vertices_677, vertices_602, vertices_154, vertices_786, vertices_852, vertices_612, vertices_472, vertices_744, vertices_432, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_51, vertices_131, vertices_259, vertices_515, vertices_37, vertices_261, vertices_517, vertices_161, vertices_289, vertices_641, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_770, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_88, vertices_152, vertices_200, vertices_584, vertices_648, vertices_176, vertices_304, vertices_336, vertices_592, vertices_400, vertices_784, vertices_224, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_651), (false, vertices_179), (false, vertices_307), (false, vertices_357), (false, vertices_677), (true, vertices_26), (true, vertices_530), (true, vertices_580), (true, vertices_88), (true, vertices_152), (true, vertices_200), (true, vertices_584), (true, vertices_336), (true, vertices_592), (true, vertices_400), (true, vertices_784), (true, vertices_224), (true, vertices_608), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 15 23 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_651) then 20 else
  if p.val = (false, vertices_179) then 21 else
  if p.val = (false, vertices_307) then 22 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_580) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
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
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_4 1 1 3 5 7 8 852 324 1
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 2 4 5 6 8 744 200 1
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 602
cert_cover_5 0 0 0 2 3 5 26 602 3
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 852
cert_cover_5 3 1 1 3 5 7 324 852 1
cert_coverFacet 4 612
cert_cover_2 4 4 1 5 8 100 612 3
cert_coverFacet 5 472
cert_cover_5 5 2 2 3 5 6 88 472 3
cert_coverFacet 6 744
cert_cover_5 6 3 2 4 5 6 200 744 1
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coverFacet 8 480
cert_cover_2 8 5 4 6 7 224 480 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0346

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0347.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0347

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 611, 291, 707, 109, 309, 213, 806, 906, 92, 284, 556, 780, 472, 744, 35, 579, 131, 259, 21, 37, 69, 145, 273, 97, 289, 193, 290, 546, 386, 642, 770, 28, 44, 76, 268, 524, 84, 276, 292, 548, 772, 88, 280, 104, 552, 200, 392, 648, 776, 208, 400, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_611, vertices_291, vertices_707, vertices_109, vertices_309, vertices_213, vertices_806, vertices_906, vertices_92, vertices_284, vertices_556, vertices_780, vertices_472, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_579, vertices_131, vertices_259, vertices_21, vertices_37, vertices_69, vertices_145, vertices_273, vertices_97, vertices_289, vertices_193, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_292, vertices_548, vertices_772, vertices_88, vertices_280, vertices_104, vertices_552, vertices_200, vertices_392, vertices_648, vertices_776, vertices_208, vertices_400, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_611), (false, vertices_291), (false, vertices_707), (false, vertices_109), (false, vertices_309), (false, vertices_213), (true, vertices_770), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_548), (true, vertices_772), (true, vertices_88), (true, vertices_280), (true, vertices_552), (true, vertices_200), (true, vertices_392), (true, vertices_648), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 22 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 15 else
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_109) then 19 else
  if p.val = (false, vertices_309) then 20 else
  if p.val = (false, vertices_213) then 21 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_776) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
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
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_4 1 0 2 6 7 8 906 386 1
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 1 0 3 2
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 386 906 1
cert_coverFacet 2 92
cert_cover_2 2 2 1 3 5 28 92 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 556
cert_cover_2 4 2 1 4 8 44 556 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 472
cert_cover_5 6 2 2 3 5 6 88 472 3
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 104 744 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0347

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0348.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0348

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 781, 357, 165, 645, 345, 617, 662, 602, 466, 482, 610, 436, 788, 792, 37, 133, 261, 517, 73, 265, 521, 97, 161, 545, 321, 641, 82, 146, 530, 98, 162, 546, 450, 578, 642, 148, 276, 532, 164, 292, 644, 772, 88, 280, 536, 584, 776, 336, 400, 784, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_781, vertices_357, vertices_165, vertices_645, vertices_345, vertices_617, vertices_662, vertices_602, vertices_466, vertices_482, vertices_610, vertices_436, vertices_788, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_321, vertices_641, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_450, vertices_578, vertices_642, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_644, vertices_772, vertices_88, vertices_280, vertices_536, vertices_584, vertices_776, vertices_336, vertices_400, vertices_784, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_781), (false, vertices_357), (false, vertices_165), (false, vertices_645), (false, vertices_345), (false, vertices_617), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_98), (true, vertices_450), (true, vertices_578), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_536), (true, vertices_400), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_645) then 1 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_450) then 16 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
cert_nodeAtPriority_25 0 165 1 645 82 146 530 98 578 148 276 532 536 400 784 416 675 450 781 357 345 617
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 82 1
cert_row_2 1 0 5 6 7 450
cert_row_4 2 0 1 3 6 8 662 146 1
cert_row_4 3 1 3 4 6 7 436 148 2
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 2 0 1 3 6 146 662 1
cert_coverFacet 1 602
cert_cover_5 1 0 0 2 3 5 82 602 1
cert_coverFacet 2 466
cert_cover_5 2 1 0 3 5 6 82 466 3
cert_coverFacet 3 482
cert_cover_5 3 1 0 4 5 6 98 482 3
cert_coverFacet 4 610
cert_cover_2 4 4 0 5 8 98 610 3
cert_coverFacet 5 436
cert_cover_5 5 3 1 3 4 6 148 436 2
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0348

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0349.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0349

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 333, 565, 85, 293, 721, 481, 806, 666, 234, 362, 778, 220, 540, 780, 21, 37, 69, 261, 81, 529, 161, 289, 545, 193, 321, 641, 106, 138, 266, 522, 162, 290, 546, 642, 770, 28, 76, 268, 524, 84, 532, 292, 548, 772, 152, 536, 200, 328, 776, 208, 656, 224, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_333, vertices_565, vertices_85, vertices_293, vertices_721, vertices_481, vertices_806, vertices_666, vertices_234, vertices_362, vertices_778, vertices_220, vertices_540, vertices_780] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_69, vertices_261, vertices_81, vertices_529, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_106, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_28, vertices_76, vertices_268, vertices_524, vertices_84, vertices_532, vertices_292, vertices_548, vertices_772, vertices_152, vertices_536, vertices_200, vertices_328, vertices_776, vertices_208, vertices_656, vertices_224, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_333), (false, vertices_565), (false, vertices_85), (false, vertices_293), (false, vertices_721), (false, vertices_481), (true, vertices_106), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_770), (true, vertices_28), (true, vertices_524), (true, vertices_772), (true, vertices_152), (true, vertices_536), (true, vertices_200), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_85) then 0 else
  if p.val = (false, vertices_293) then 1 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_106) then 16 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_776) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_106), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_2 1 0 2 4 5 106
cert_row_4 2 0 2 3 6 8 666 138 2
cert_row_4 3 1 2 3 5 6 220 28 3
cert_rows
cert_pivot_2 7 4 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 666
cert_cover_5 1 2 0 2 3 6 138 666 2
cert_coverFacet 2 234
cert_cover_5 2 1 0 2 4 6 106 234 3
cert_coverFacet 3 362
cert_cover_5 3 1 0 2 4 7 106 362 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 220
cert_cover_5 5 3 1 2 3 5 28 220 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0349

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0350.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0350

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 519, 587, 339, 565, 433, 593, 206, 526, 454, 428, 556, 744, 688, 976, 7, 67, 259, 515, 37, 517, 49, 81, 273, 529, 289, 577, 14, 198, 262, 518, 74, 522, 322, 44, 140, 524, 292, 548, 388, 168, 552, 200, 584, 176, 560, 336, 592, 400, 656, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_519, vertices_587, vertices_339, vertices_565, vertices_433, vertices_593, vertices_206, vertices_526, vertices_454, vertices_428, vertices_556, vertices_744, vertices_688, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_67, vertices_259, vertices_515, vertices_37, vertices_517, vertices_49, vertices_81, vertices_273, vertices_529, vertices_289, vertices_577, vertices_14, vertices_198, vertices_262, vertices_518, vertices_74, vertices_522, vertices_322, vertices_44, vertices_140, vertices_524, vertices_292, vertices_548, vertices_388, vertices_168, vertices_552, vertices_200, vertices_584, vertices_176, vertices_560, vertices_336, vertices_592, vertices_400, vertices_656, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_519), (false, vertices_587), (false, vertices_339), (false, vertices_565), (false, vertices_433), (false, vertices_593), (true, vertices_14), (true, vertices_198), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_388), (true, vertices_168), (true, vertices_552), (true, vertices_200), (true, vertices_656), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 14 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 15 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_587) then 19 else
  if p.val = (false, vertices_339) then 20 else
  if p.val = (false, vertices_565) then 16 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_593) then 1 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_198) then 17 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_448) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_198), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_2 0 0 1 5 6 198
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 2 4 5 6 8 744 168 2
cert_row_4 3 3 5 6 7 8 976 336 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 454
cert_cover_5 2 0 0 1 5 7 198 454 3
cert_coverFacet 3 428
cert_cover_5 3 1 1 2 4 6 44 428 3
cert_coverFacet 4 556
cert_cover_2 4 2 1 4 8 44 556 3
cert_coverFacet 5 744
cert_cover_5 5 2 2 4 5 6 168 744 2
cert_coverFacet 6 688
cert_cover_2 6 4 3 6 8 176 688 3
cert_coverFacet 7 976
cert_cover_5 7 3 3 5 6 7 336 976 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0350

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0351.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0351

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 173, 565, 149, 913, 481, 609, 46, 526, 614, 794, 234, 458, 412, 540, 21, 37, 133, 145, 529, 97, 161, 545, 321, 577, 385, 769, 14, 38, 518, 42, 202, 266, 522, 98, 322, 578, 770, 28, 44, 140, 524, 148, 532, 548, 280, 536, 168, 392, 400, 784, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_173, vertices_565, vertices_149, vertices_913, vertices_481, vertices_609, vertices_46, vertices_526, vertices_614, vertices_794, vertices_234, vertices_458, vertices_412, vertices_540] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_133, vertices_145, vertices_529, vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_769, vertices_14, vertices_38, vertices_518, vertices_42, vertices_202, vertices_266, vertices_522, vertices_98, vertices_322, vertices_578, vertices_770, vertices_28, vertices_44, vertices_140, vertices_524, vertices_148, vertices_532, vertices_548, vertices_280, vertices_536, vertices_168, vertices_392, vertices_400, vertices_784, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_173), (false, vertices_565), (false, vertices_149), (false, vertices_913), (false, vertices_481), (false, vertices_609), (true, vertices_14), (true, vertices_38), (true, vertices_518), (true, vertices_42), (true, vertices_202), (true, vertices_266), (true, vertices_522), (true, vertices_98), (true, vertices_28), (true, vertices_524), (true, vertices_280), (true, vertices_536), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 15 else
  if p.val = (false, vertices_173) then 18 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_913) then 22 else
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
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_392) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_609), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 8 614 38 3
cert_row_2 1 0 2 5 6 202
cert_row_4 2 0 2 3 7 8 794 266 2
cert_row_4 3 1 2 3 6 7 412 28 3
cert_rows
cert_pivot_2 4 5 0 1
cert_heightProof 4
cert_coverFacet 0 46
cert_cover_2 0 1 0 2 4 14 46 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 614
cert_cover_5 2 0 0 1 4 5 38 614 3
cert_coverFacet 3 794
cert_cover_5 3 2 0 2 3 7 266 794 2
cert_coverFacet 4 234
cert_cover_5 4 1 0 2 4 5 42 234 3
cert_coverFacet 5 458
cert_cover_5 5 1 0 2 5 7 202 458 3
cert_coverFacet 6 412
cert_cover_5 6 3 1 2 3 6 28 412 3
cert_coverFacet 7 540
cert_cover_2 7 2 1 3 8 28 540 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0351

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0352.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0352

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [15, 583, 395, 803, 93, 713, 897, 286, 310, 550, 244, 612, 440, 216, 992, 7, 11, 259, 515, 13, 69, 73, 137, 577, 385, 641, 769, 14, 278, 38, 518, 266, 290, 546, 28, 52, 84, 100, 548, 580, 88, 152, 280, 200, 392, 176, 304, 208, 224, 608, 416, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_15, vertices_583, vertices_395, vertices_803, vertices_93, vertices_713, vertices_897, vertices_286, vertices_310, vertices_550, vertices_244, vertices_612, vertices_440, vertices_216, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_515, vertices_13, vertices_69, vertices_73, vertices_137, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_278, vertices_38, vertices_518, vertices_266, vertices_290, vertices_546, vertices_28, vertices_52, vertices_84, vertices_100, vertices_548, vertices_580, vertices_88, vertices_152, vertices_280, vertices_200, vertices_392, vertices_176, vertices_304, vertices_208, vertices_224, vertices_608, vertices_416, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_15), (false, vertices_583), (false, vertices_395), (false, vertices_803), (false, vertices_93), (false, vertices_713), (false, vertices_897), (true, vertices_278), (true, vertices_38), (true, vertices_52), (true, vertices_100), (true, vertices_548), (true, vertices_152), (true, vertices_280), (true, vertices_176), (true, vertices_304), (true, vertices_208), (true, vertices_224), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 14 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_15) then 0 else
  if p.val = (false, vertices_583) then 15 else
  if p.val = (false, vertices_395) then 19 else
  if p.val = (false, vertices_803) then 20 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_278) then 17 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_52) then 3 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_15), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_278), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_2 0 0 1 3 7 278
cert_row_4 1 1 3 4 5 6 244 52 3
cert_row_4 2 2 3 4 6 7 440 152 2
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 14 286 3
cert_coverFacet 1 310
cert_cover_5 1 0 0 1 3 4 278 310 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 244
cert_cover_5 3 1 1 3 4 5 52 244 3
cert_coverFacet 4 612
cert_cover_2 4 4 1 5 8 100 612 3
cert_coverFacet 5 440
cert_cover_5 5 2 2 3 4 6 152 440 2
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0352

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0353.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0353

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 803, 451, 341, 533, 773, 217, 558, 426, 650, 92, 668, 108, 868, 488, 131, 259, 515, 21, 261, 517, 81, 145, 529, 193, 321, 769, 42, 138, 522, 290, 546, 386, 642, 28, 44, 76, 524, 84, 532, 100, 548, 324, 772, 88, 152, 104, 424, 200, 648, 656, 352, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_803, vertices_451, vertices_341, vertices_533, vertices_773, vertices_217, vertices_558, vertices_426, vertices_650, vertices_92, vertices_668, vertices_108, vertices_868, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_21, vertices_261, vertices_517, vertices_81, vertices_145, vertices_529, vertices_193, vertices_321, vertices_769, vertices_42, vertices_138, vertices_522, vertices_290, vertices_546, vertices_386, vertices_642, vertices_28, vertices_44, vertices_76, vertices_524, vertices_84, vertices_532, vertices_100, vertices_548, vertices_324, vertices_772, vertices_88, vertices_152, vertices_104, vertices_424, vertices_200, vertices_648, vertices_656, vertices_352, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_803), (false, vertices_451), (false, vertices_341), (false, vertices_533), (false, vertices_773), (false, vertices_217), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_524), (true, vertices_100), (true, vertices_548), (true, vertices_104), (true, vertices_424), (true, vertices_648), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_451) then 17 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_773) then 1 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_424) then 22 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_424), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 42 1
cert_row_4 1 1 2 3 6 8 668 28 3
cert_row_2 2 2 4 6 7 424
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 0 3 2 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 42 558 1
cert_coverFacet 1 426
cert_cover_5 1 2 0 2 4 6 42 426 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 92
cert_cover_2 3 2 1 3 5 28 92 3
cert_coverFacet 4 668
cert_cover_5 4 1 1 2 3 6 28 668 3
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 868
cert_cover_5 6 3 1 4 5 7 100 868 3
cert_coverFacet 7 488
cert_cover_5 7 2 2 4 5 6 104 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0353

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0354.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0354

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 333, 805, 709, 217, 393, 566, 58, 154, 810, 394, 722, 372, 596, 376, 69, 261, 517, 73, 137, 265, 193, 385, 641, 769, 26, 42, 138, 266, 50, 146, 530, 546, 386, 642, 770, 52, 84, 532, 292, 548, 324, 580, 56, 88, 152, 296, 328, 392, 368, 208, 592, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_333, vertices_805, vertices_709, vertices_217, vertices_393, vertices_566, vertices_58, vertices_154, vertices_810, vertices_394, vertices_722, vertices_372, vertices_596, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_193, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_138, vertices_266, vertices_50, vertices_146, vertices_530, vertices_546, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_532, vertices_292, vertices_548, vertices_324, vertices_580, vertices_56, vertices_88, vertices_152, vertices_296, vertices_328, vertices_392, vertices_368, vertices_208, vertices_592, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_333), (false, vertices_805), (false, vertices_709), (false, vertices_217), (false, vertices_393), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_546), (true, vertices_52), (true, vertices_84), (true, vertices_532), (true, vertices_56), (true, vertices_296), (true, vertices_368), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_217) then 22 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_368) then 24 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(true, vertices_368), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 50 1
cert_row_4 1 0 2 4 7 8 810 42 3
cert_row_2 2 3 4 5 7 368
cert_row_4 3 0 3 5 6 8 722 146 2
cert_rows
cert_pivot_2 1 2 4 0
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 50 566 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 810
cert_cover_5 3 1 0 2 4 7 42 810 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 722
cert_cover_5 5 3 0 3 5 6 146 722 2
cert_coverFacet 6 372
cert_cover_5 6 2 1 3 4 5 52 372 3
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 376
cert_cover_5 8 2 2 3 4 5 56 376 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0354

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0355.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0355

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 519, 595, 355, 525, 617, 425, 214, 534, 454, 908, 692, 680, 496, 624, 7, 67, 259, 515, 13, 517, 41, 265, 521, 97, 289, 577, 22, 198, 262, 518, 82, 530, 322, 268, 524, 148, 532, 388, 644, 168, 552, 392, 648, 112, 176, 560, 208, 592, 352, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_519, vertices_595, vertices_355, vertices_525, vertices_617, vertices_425, vertices_214, vertices_534, vertices_454, vertices_908, vertices_692, vertices_680, vertices_496, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_67, vertices_259, vertices_515, vertices_13, vertices_517, vertices_41, vertices_265, vertices_521, vertices_97, vertices_289, vertices_577, vertices_22, vertices_198, vertices_262, vertices_518, vertices_82, vertices_530, vertices_322, vertices_268, vertices_524, vertices_148, vertices_532, vertices_388, vertices_644, vertices_168, vertices_552, vertices_392, vertices_648, vertices_112, vertices_176, vertices_560, vertices_208, vertices_592, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_519), (false, vertices_595), (false, vertices_355), (false, vertices_525), (false, vertices_617), (false, vertices_425), (true, vertices_22), (true, vertices_198), (true, vertices_148), (true, vertices_532), (true, vertices_388), (true, vertices_644), (true, vertices_648), (true, vertices_112), (true, vertices_176), (true, vertices_560), (true, vertices_208), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 15 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_595) then 18 else
  if p.val = (false, vertices_355) then 19 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_198) then 16 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
cert_nodeAtPriority_25 1 519 0 525 22 148 532 388 644 648 112 176 560 208 672 448 271 198 595 355 617 425
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_4 1 1 2 6 7 8 908 268 2
cert_row_4 2 1 3 4 6 8 692 148 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 454
cert_cover_5 2 0 0 1 5 7 198 454 3
cert_coverFacet 3 908
cert_cover_5 3 1 1 2 6 7 268 908 2
cert_coverFacet 4 692
cert_cover_5 4 2 1 3 4 6 148 692 2
cert_coverFacet 5 680
cert_cover_2 5 4 2 6 8 168 680 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coverFacet 7 624
cert_cover_2 7 4 3 5 8 112 624 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0355

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0356.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0356

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 541, 269, 85, 357, 457, 721, 806, 234, 362, 778, 690, 780, 244, 564, 13, 21, 69, 261, 137, 265, 521, 81, 529, 193, 321, 641, 106, 138, 266, 522, 162, 290, 546, 642, 770, 268, 524, 52, 84, 532, 100, 292, 548, 772, 200, 328, 776, 176, 560, 208, 656, 224, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_541, vertices_269, vertices_85, vertices_357, vertices_457, vertices_721, vertices_806, vertices_234, vertices_362, vertices_778, vertices_690, vertices_780, vertices_244, vertices_564] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_69, vertices_261, vertices_137, vertices_265, vertices_521, vertices_81, vertices_529, vertices_193, vertices_321, vertices_641, vertices_106, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_268, vertices_524, vertices_52, vertices_84, vertices_532, vertices_100, vertices_292, vertices_548, vertices_772, vertices_200, vertices_328, vertices_776, vertices_176, vertices_560, vertices_208, vertices_656, vertices_224, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_541), (false, vertices_269), (false, vertices_85), (false, vertices_357), (false, vertices_457), (false, vertices_721), (true, vertices_106), (true, vertices_266), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_52), (true, vertices_548), (true, vertices_772), (true, vertices_776), (true, vertices_176), (true, vertices_560), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_541) then 18 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_85) then 1 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_106) then 16 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_224) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 269 1 85 266 162 290 546 770 52 548 772 776 176 560 224 651 106 541 357 457 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 3 4 6 8 690 162 1
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 234
cert_cover_5 1 0 0 2 4 6 106 234 3
cert_coverFacet 2 362
cert_cover_5 2 0 0 2 4 7 106 362 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 690
cert_cover_5 4 2 0 3 4 6 162 690 1
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 244
cert_cover_5 6 3 1 3 4 5 52 244 3
cert_coverFacet 7 564
cert_cover_2 7 3 1 4 8 52 564 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0356

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0357.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0357

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 653, 181, 277, 369, 929, 206, 526, 214, 278, 618, 850, 248, 680, 864, 21, 133, 261, 517, 49, 273, 161, 289, 641, 769, 14, 22, 198, 262, 518, 74, 522, 82, 274, 578, 770, 140, 524, 148, 276, 104, 168, 552, 200, 648, 112, 176, 208, 336, 352, 608, 672, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_653, vertices_181, vertices_277, vertices_369, vertices_929, vertices_206, vertices_526, vertices_214, vertices_278, vertices_618, vertices_850, vertices_248, vertices_680, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_49, vertices_273, vertices_161, vertices_289, vertices_641, vertices_769, vertices_14, vertices_22, vertices_198, vertices_262, vertices_518, vertices_74, vertices_522, vertices_82, vertices_274, vertices_578, vertices_770, vertices_140, vertices_524, vertices_148, vertices_276, vertices_104, vertices_168, vertices_552, vertices_200, vertices_648, vertices_112, vertices_176, vertices_208, vertices_336, vertices_352, vertices_608, vertices_672, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_653), (false, vertices_181), (false, vertices_277), (false, vertices_369), (false, vertices_929), (true, vertices_14), (true, vertices_22), (true, vertices_198), (true, vertices_74), (true, vertices_522), (true, vertices_82), (true, vertices_274), (true, vertices_578), (true, vertices_104), (true, vertices_168), (true, vertices_552), (true, vertices_200), (true, vertices_208), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_181) then 20 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_198) then 17 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_198), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_4 1 0 3 5 7 8 850 82 3
cert_row_4 2 0 2 4 5 8 618 74 2
cert_row_4 3 2 3 4 5 6 248 104 1
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 214
cert_cover_5 2 0 0 1 3 5 22 214 3
cert_coverFacet 3 278
cert_cover_2 3 1 0 3 7 22 278 3
cert_coverFacet 4 618
cert_cover_5 4 2 0 2 4 5 74 618 2
cert_coverFacet 5 850
cert_cover_5 5 1 0 3 5 7 82 850 3
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 104 248 1
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coverFacet 8 864
cert_cover_2 8 5 4 7 8 352 864 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0357

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0358.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0358

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 805, 793, 721, 337, 481, 110, 526, 550, 666, 234, 220, 284, 780, 372, 81, 273, 529, 161, 289, 545, 193, 321, 641, 769, 14, 38, 518, 106, 138, 522, 162, 546, 642, 28, 76, 268, 524, 84, 276, 100, 292, 548, 772, 152, 280, 536, 200, 776, 208, 336, 656, 224, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_805, vertices_793, vertices_721, vertices_337, vertices_481, vertices_110, vertices_526, vertices_550, vertices_666, vertices_234, vertices_220, vertices_284, vertices_780, vertices_372] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_38, vertices_518, vertices_106, vertices_138, vertices_522, vertices_162, vertices_546, vertices_642, vertices_28, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_100, vertices_292, vertices_548, vertices_772, vertices_152, vertices_280, vertices_536, vertices_200, vertices_776, vertices_208, vertices_336, vertices_656, vertices_224, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_805), (false, vertices_793), (false, vertices_721), (false, vertices_337), (false, vertices_481), (true, vertices_14), (true, vertices_38), (true, vertices_518), (true, vertices_106), (true, vertices_138), (true, vertices_522), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_276), (true, vertices_100), (true, vertices_152), (true, vertices_200)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_106) then 17 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_100) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_200) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 337 14 38 518 138 522 28 76 268 524 84 276 100 152 200 675 106 805 793 721 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 138 2
cert_row_2 1 0 2 4 5 106
cert_row_4 2 1 2 3 5 6 220 28 3
cert_row_4 3 1 3 4 5 7 372 84 2
cert_rows
cert_pivot_2 8 0 2 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 14 110 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 666
cert_cover_5 3 0 0 2 3 6 138 666 2
cert_coverFacet 4 234
cert_cover_5 4 1 0 2 4 6 106 234 3
cert_coverFacet 5 220
cert_cover_5 5 2 1 2 3 5 28 220 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 372
cert_cover_5 8 3 1 3 4 5 84 372 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0358

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0359.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0359

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 709, 681, 817, 465, 417, 334, 590, 570, 282, 338, 316, 172, 652, 484, 81, 273, 529, 161, 289, 545, 193, 577, 385, 641, 78, 26, 266, 522, 82, 274, 530, 322, 578, 44, 140, 268, 524, 164, 292, 196, 324, 580, 644, 56, 280, 168, 552, 648, 304, 560, 336, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_709, vertices_681, vertices_817, vertices_465, vertices_417, vertices_334, vertices_590, vertices_570, vertices_282, vertices_338, vertices_316, vertices_172, vertices_652, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_78, vertices_26, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_322, vertices_578, vertices_44, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_196, vertices_324, vertices_580, vertices_644, vertices_56, vertices_280, vertices_168, vertices_552, vertices_648, vertices_304, vertices_560, vertices_336, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_709), (false, vertices_681), (false, vertices_817), (false, vertices_465), (false, vertices_417), (true, vertices_78), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_322), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_164), (true, vertices_292), (true, vertices_324), (true, vertices_56), (true, vertices_280)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 16 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_324) then 12 else
  if p.val = (true, vertices_56) then 13 else
  if p.val = (true, vertices_280) then 14 else
  0
cert_priority
cert_nodeAtPriority_40 417 26 266 522 274 322 44 140 268 524 164 292 324 56 280 595 78 709 681 817 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 26 3
cert_row_2 1 0 1 2 5 78
cert_row_4 2 1 2 3 4 7 316 44 2
cert_row_4 3 1 4 5 6 7 484 164 2
cert_rows
cert_pivot_2 8 0 2 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 1 0 1 2 7 78 334 3
cert_coverFacet 1 590
cert_cover_5 1 1 0 1 2 8 78 590 3
cert_coverFacet 2 570
cert_cover_5 2 0 0 2 3 4 26 570 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 316
cert_cover_5 5 2 1 2 3 4 44 316 2
cert_coverFacet 6 172
cert_cover_2 6 2 1 4 6 44 172 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 484
cert_cover_5 8 3 1 4 5 6 164 484 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0359

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0360.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0360

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 451, 643, 341, 661, 773, 217, 558, 666, 426, 92, 540, 108, 868, 488, 131, 259, 515, 21, 261, 517, 81, 145, 193, 321, 641, 769, 42, 138, 522, 290, 546, 386, 642, 28, 44, 76, 524, 84, 532, 100, 548, 324, 772, 88, 152, 536, 104, 424, 200, 656, 352, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_451, vertices_643, vertices_341, vertices_661, vertices_773, vertices_217, vertices_558, vertices_666, vertices_426, vertices_92, vertices_540, vertices_108, vertices_868, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_21, vertices_261, vertices_517, vertices_81, vertices_145, vertices_193, vertices_321, vertices_641, vertices_769, vertices_42, vertices_138, vertices_522, vertices_290, vertices_546, vertices_386, vertices_642, vertices_28, vertices_44, vertices_76, vertices_524, vertices_84, vertices_532, vertices_100, vertices_548, vertices_324, vertices_772, vertices_88, vertices_152, vertices_536, vertices_104, vertices_424, vertices_200, vertices_656, vertices_352, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_451), (false, vertices_643), (false, vertices_341), (false, vertices_661), (false, vertices_773), (false, vertices_217), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_524), (true, vertices_100), (true, vertices_548), (true, vertices_536), (true, vertices_104), (true, vertices_424), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_773) then 1 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_424) then 22 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_424), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 138 2
cert_row_2 1 2 4 6 7 424
cert_row_4 2 0 1 2 4 8 558 42 1
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 2 0 1 2 4 42 558 1
cert_coverFacet 1 666
cert_cover_5 1 0 0 2 3 6 138 666 2
cert_coverFacet 2 426
cert_cover_5 2 1 0 2 4 6 42 426 3
cert_coverFacet 3 92
cert_cover_2 3 2 1 3 5 28 92 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 868
cert_cover_5 6 3 1 4 5 7 100 868 3
cert_coverFacet 7 488
cert_cover_5 7 1 2 4 5 6 104 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0360

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0361.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0361

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 77, 525, 613, 793, 457, 721, 806, 426, 242, 626, 786, 236, 300, 780, 13, 69, 517, 73, 265, 521, 145, 273, 529, 193, 577, 385, 114, 146, 274, 530, 162, 290, 546, 386, 770, 44, 76, 268, 524, 100, 292, 548, 772, 168, 296, 200, 392, 776, 208, 592, 784, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_77, vertices_525, vertices_613, vertices_793, vertices_457, vertices_721, vertices_806, vertices_426, vertices_242, vertices_626, vertices_786, vertices_236, vertices_300, vertices_780] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_73, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_114, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_44, vertices_76, vertices_268, vertices_524, vertices_100, vertices_292, vertices_548, vertices_772, vertices_168, vertices_296, vertices_200, vertices_392, vertices_776, vertices_208, vertices_592, vertices_784, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_77), (false, vertices_525), (false, vertices_613), (false, vertices_793), (false, vertices_457), (false, vertices_721), (true, vertices_114), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_44), (true, vertices_268), (true, vertices_292), (true, vertices_772), (true, vertices_168), (true, vertices_296), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 15 else
  if p.val = (false, vertices_77) then 0 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_114) then 16 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_224) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_77), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_114), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
cert_row_2 0 0 3 4 5 114
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 2 4 6 7 426 162 1
cert_row_4 3 1 2 4 5 6 236 44 3
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 426
cert_cover_5 1 2 0 2 4 6 162 426 1
cert_coverFacet 2 242
cert_cover_5 2 0 0 3 4 6 114 242 3
cert_coverFacet 3 626
cert_cover_5 3 0 0 3 4 8 114 626 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 236
cert_cover_5 5 3 1 2 4 5 44 236 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0361

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0362.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0362

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [91, 339, 805, 569, 841, 433, 422, 198, 326, 666, 202, 402, 716, 692, 836, 83, 25, 73, 521, 49, 273, 289, 545, 321, 769, 70, 134, 262, 26, 74, 138, 146, 274, 194, 322, 386, 164, 292, 548, 196, 324, 580, 644, 772, 536, 200, 584, 648, 176, 560, 400, 656, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_91, vertices_339, vertices_805, vertices_569, vertices_841, vertices_433, vertices_422, vertices_198, vertices_326, vertices_666, vertices_202, vertices_402, vertices_716, vertices_692, vertices_836] (by decide +kernel)
  polygons := literalFinset [vertices_83, vertices_25, vertices_73, vertices_521, vertices_49, vertices_273, vertices_289, vertices_545, vertices_321, vertices_769, vertices_70, vertices_134, vertices_262, vertices_26, vertices_74, vertices_138, vertices_146, vertices_274, vertices_194, vertices_322, vertices_386, vertices_164, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_536, vertices_200, vertices_584, vertices_648, vertices_176, vertices_560, vertices_400, vertices_656, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_91), (false, vertices_339), (false, vertices_805), (false, vertices_569), (false, vertices_841), (false, vertices_433), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_138), (true, vertices_146), (true, vertices_194), (true, vertices_386), (true, vertices_164), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_644), (true, vertices_200), (true, vertices_648), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_91) then 16 else
  if p.val = (false, vertices_339) then 17 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 7 422 134 2
cert_row_4 1 0 2 3 6 8 666 26 3
cert_row_4 2 1 2 5 6 8 716 196 1
cert_row_4 3 1 3 4 6 8 692 164 1
cert_rows
cert_pivot_2 7 0 2 1
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 134 422 2
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 326
cert_cover_2 2 1 0 5 7 70 326 3
cert_coverFacet 3 666
cert_cover_5 3 1 0 2 3 6 26 666 3
cert_coverFacet 4 202
cert_cover_2 4 2 0 5 6 74 202 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 716
cert_cover_5 6 2 1 2 5 6 196 716 1
cert_coverFacet 7 692
cert_cover_5 7 3 1 3 4 6 164 692 1
cert_coverFacet 8 836
cert_cover_2 8 5 1 7 8 324 836 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0362

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2943 : Certifies 2943 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0333.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2944 : Certifies 2944 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0334.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2945 : Certifies 2945 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0335.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2946 : Certifies 2946 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0336.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2947 : Certifies 2947 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0337.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2948 : Certifies 2948 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0338.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2949 : Certifies 2949 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0339.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2950 : Certifies 2950 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0340.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2951 : Certifies 2951 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0341.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2952 : Certifies 2952 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0342.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2953 : Certifies 2953 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0343.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2954 : Certifies 2954 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0344.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2955 : Certifies 2955 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0345.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2956 : Certifies 2956 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0346.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2957 : Certifies 2957 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0347.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2958 : Certifies 2958 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0348.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2959 : Certifies 2959 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0349.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2960 : Certifies 2960 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0350.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2961 : Certifies 2961 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0351.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2962 : Certifies 2962 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0352.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2963 : Certifies 2963 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0353.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2964 : Certifies 2964 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0354.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2965 : Certifies 2965 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0355.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2966 : Certifies 2966 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0356.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2967 : Certifies 2967 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0357.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2968 : Certifies 2968 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0358.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2969 : Certifies 2969 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0359.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2970 : Certifies 2970 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0360.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2971 : Certifies 2971 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0361.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2972 : Certifies 2972 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0362.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B097 (j : Fin 30) :
    Certifies (2943 + j.val) := by
  fin_cases j
  · exact projection_2943
  · exact projection_2944
  · exact projection_2945
  · exact projection_2946
  · exact projection_2947
  · exact projection_2948
  · exact projection_2949
  · exact projection_2950
  · exact projection_2951
  · exact projection_2952
  · exact projection_2953
  · exact projection_2954
  · exact projection_2955
  · exact projection_2956
  · exact projection_2957
  · exact projection_2958
  · exact projection_2959
  · exact projection_2960
  · exact projection_2961
  · exact projection_2962
  · exact projection_2963
  · exact projection_2964
  · exact projection_2965
  · exact projection_2966
  · exact projection_2967
  · exact projection_2968
  · exact projection_2969
  · exact projection_2970
  · exact projection_2971
  · exact projection_2972

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
