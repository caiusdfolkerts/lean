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
/- Source: ProjectionCertificates/R_m15e10q1_1065.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1065

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 419, 643, 453, 345, 665, 297, 209, 230, 614, 722, 852, 420, 804, 824, 35, 131, 515, 25, 41, 265, 521, 81, 145, 289, 193, 321, 385, 641, 102, 162, 546, 194, 578, 642, 164, 292, 548, 196, 324, 580, 388, 772, 280, 536, 296, 552, 208, 336, 592, 656, 784, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_419, vertices_643, vertices_453, vertices_345, vertices_665, vertices_297, vertices_209, vertices_230, vertices_614, vertices_722, vertices_852, vertices_420, vertices_804, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_25, vertices_41, vertices_265, vertices_521, vertices_81, vertices_145, vertices_289, vertices_193, vertices_321, vertices_385, vertices_641, vertices_102, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_164, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_280, vertices_536, vertices_296, vertices_552, vertices_208, vertices_336, vertices_592, vertices_656, vertices_784, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_419), (false, vertices_643), (false, vertices_453), (false, vertices_345), (false, vertices_665), (false, vertices_297), (false, vertices_209), (true, vertices_102), (true, vertices_194), (true, vertices_578), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_580), (true, vertices_772), (true, vertices_592), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 17 else
  if p.val = (false, vertices_419) then 18 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_453) then 14 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (false, vertices_209) then 2 else
  if p.val = (true, vertices_102) then 15 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 8 722 194 1
cert_row_2 1 0 1 4 5 102
cert_row_4 2 1 3 5 7 8 852 324 1
cert_row_4 3 2 3 4 7 8 824 280 2
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 1 0 1 4 6 102 230 3
cert_coverFacet 1 614
cert_cover_5 1 1 0 1 4 8 102 614 3
cert_coverFacet 2 722
cert_cover_5 2 0 0 3 5 6 194 722 1
cert_coverFacet 3 852
cert_cover_5 3 2 1 3 5 7 324 852 1
cert_coverFacet 4 420
cert_cover_2 4 4 1 6 7 164 420 3
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coverFacet 6 824
cert_cover_5 6 3 2 3 4 7 280 824 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1065

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_1066.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1066

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 653, 601, 457, 369, 401, 558, 310, 390, 646, 626, 402, 236, 484, 616, 73, 137, 521, 81, 145, 273, 529, 321, 385, 641, 38, 134, 262, 518, 50, 146, 274, 530, 546, 386, 642, 44, 140, 524, 228, 292, 388, 644, 104, 552, 200, 584, 112, 304, 592, 400, 352, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_653, vertices_601, vertices_457, vertices_369, vertices_401, vertices_558, vertices_310, vertices_390, vertices_646, vertices_626, vertices_402, vertices_236, vertices_484, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_521, vertices_81, vertices_145, vertices_273, vertices_529, vertices_321, vertices_385, vertices_641, vertices_38, vertices_134, vertices_262, vertices_518, vertices_50, vertices_146, vertices_274, vertices_530, vertices_546, vertices_386, vertices_642, vertices_44, vertices_140, vertices_524, vertices_228, vertices_292, vertices_388, vertices_644, vertices_104, vertices_552, vertices_200, vertices_584, vertices_112, vertices_304, vertices_592, vertices_400, vertices_352, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_653), (false, vertices_601), (false, vertices_457), (false, vertices_369), (false, vertices_401), (true, vertices_38), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_274), (true, vertices_546), (true, vertices_386), (true, vertices_44), (true, vertices_228), (true, vertices_292), (true, vertices_388), (true, vertices_104), (true, vertices_552), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_228) then 19 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 401 2 38 1 134 3 262 518 50 274 546 386 44 292 388 104 552 608 659 653 228 601 457 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 6 228
cert_row_4 1 0 1 2 4 8 558 38 2
cert_row_4 2 0 1 3 4 7 310 38 2
cert_row_4 3 0 3 4 5 8 626 50 3
cert_rows
cert_pivot_2 6 2 1 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 38 558 2
cert_coverFacet 1 310
cert_cover_5 1 2 0 1 3 4 38 310 2
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 646
cert_cover_2 3 1 0 6 8 134 646 3
cert_coverFacet 4 626
cert_cover_5 4 3 0 3 4 5 50 626 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 236
cert_cover_5 6 0 1 2 4 5 44 236 3
cert_coverFacet 7 484
cert_cover_5 7 0 1 4 5 7 228 484 3
cert_coverFacet 8 616
cert_cover_2 8 4 2 5 8 104 616 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1066

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_1067.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1067

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 789, 601, 241, 401, 865, 110, 270, 806, 218, 394, 226, 412, 540, 620, 81, 145, 273, 529, 97, 161, 289, 577, 385, 769, 14, 38, 262, 74, 138, 266, 98, 162, 290, 194, 386, 28, 108, 268, 524, 276, 532, 548, 772, 88, 152, 536, 584, 392, 208, 400, 224, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_789, vertices_601, vertices_241, vertices_401, vertices_865, vertices_110, vertices_270, vertices_806, vertices_218, vertices_394, vertices_226, vertices_412, vertices_540, vertices_620] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_769, vertices_14, vertices_38, vertices_262, vertices_74, vertices_138, vertices_266, vertices_98, vertices_162, vertices_290, vertices_194, vertices_386, vertices_28, vertices_108, vertices_268, vertices_524, vertices_276, vertices_532, vertices_548, vertices_772, vertices_88, vertices_152, vertices_536, vertices_584, vertices_392, vertices_208, vertices_400, vertices_224, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_789), (false, vertices_601), (false, vertices_241), (false, vertices_401), (false, vertices_865), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_74), (true, vertices_138), (true, vertices_266), (true, vertices_98), (true, vertices_194), (true, vertices_28), (true, vertices_108), (true, vertices_268), (true, vertices_524), (true, vertices_548), (true, vertices_152), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_194) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_108) then 19 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_548) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
cert_nodeAtPriority_9 0 401 1 14 38 262 74 138 266 98 194 28 268 524 548 152 392 419 789 108 601 241 865
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 38 3
cert_row_2 1 1 2 4 5 108
cert_row_4 2 0 2 3 5 6 218 74 2
cert_row_4 3 1 2 3 6 7 412 28 3
cert_rows
cert_pivot_2 8 4 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 806
cert_cover_5 2 0 0 1 4 7 38 806 3
cert_coverFacet 3 218
cert_cover_5 3 2 0 2 3 5 74 218 2
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 226
cert_cover_2 5 4 0 5 6 98 226 3
cert_coverFacet 6 412
cert_cover_5 6 3 1 2 3 6 28 412 3
cert_coverFacet 7 540
cert_cover_2 7 2 1 3 8 28 540 3
cert_coverFacet 8 620
cert_cover_5 8 1 1 2 4 8 108 620 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1067

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_1068.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1068

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 677, 313, 553, 713, 481, 590, 566, 214, 282, 538, 466, 436, 708, 568, 41, 73, 265, 521, 161, 289, 545, 193, 321, 641, 22, 70, 518, 26, 74, 266, 522, 210, 274, 530, 322, 52, 148, 164, 548, 196, 580, 644, 56, 280, 536, 552, 584, 304, 560, 400, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_677, vertices_313, vertices_553, vertices_713, vertices_481, vertices_590, vertices_566, vertices_214, vertices_282, vertices_538, vertices_466, vertices_436, vertices_708, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_22, vertices_70, vertices_518, vertices_26, vertices_74, vertices_266, vertices_522, vertices_210, vertices_274, vertices_530, vertices_322, vertices_52, vertices_148, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_280, vertices_536, vertices_552, vertices_584, vertices_304, vertices_560, vertices_400, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_677), (false, vertices_313), (false, vertices_553), (false, vertices_713), (false, vertices_481), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_26), (true, vertices_522), (true, vertices_210), (true, vertices_274), (true, vertices_530), (true, vertices_52), (true, vertices_148), (true, vertices_196), (true, vertices_580), (true, vertices_536), (true, vertices_560), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_210) then 17 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 553 22 70 518 26 522 274 530 52 148 196 580 536 560 400 331 210 677 313 713 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 70 2
cert_row_2 1 0 3 5 6 210
cert_row_4 2 0 1 3 4 8 566 22 3
cert_row_4 3 1 3 4 6 7 436 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 70 590 2
cert_coverFacet 1 566
cert_cover_5 1 2 0 1 3 4 22 566 3
cert_coverFacet 2 214
cert_cover_5 2 1 0 1 3 5 22 214 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 466
cert_cover_5 5 1 0 3 5 7 210 466 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 52 436 3
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coverFacet 8 568
cert_cover_2 8 3 2 4 8 56 568 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1068

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_1069.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1069

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 781, 357, 709, 241, 417, 542, 154, 426, 778, 722, 348, 596, 376, 184, 69, 261, 517, 97, 161, 289, 193, 385, 641, 769, 26, 138, 266, 522, 146, 530, 386, 642, 770, 28, 268, 524, 84, 532, 324, 580, 56, 344, 152, 168, 296, 776, 112, 176, 208, 592, 352, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_781, vertices_357, vertices_709, vertices_241, vertices_417, vertices_542, vertices_154, vertices_426, vertices_778, vertices_722, vertices_348, vertices_596, vertices_376, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_193, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_84, vertices_532, vertices_324, vertices_580, vertices_56, vertices_344, vertices_152, vertices_168, vertices_296, vertices_776, vertices_112, vertices_176, vertices_208, vertices_592, vertices_352, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_781), (false, vertices_357), (false, vertices_709), (false, vertices_241), (false, vertices_417), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_84), (true, vertices_532), (true, vertices_56), (true, vertices_344), (true, vertices_152), (true, vertices_168), (true, vertices_296), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_344) then 22 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(true, vertices_344), by decide +kernel⟩
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
cert_row_4 0 0 1 2 3 8 542 26 1
cert_row_4 1 0 2 4 6 7 426 138 2
cert_row_2 2 2 3 5 7 344
cert_row_4 3 0 3 5 6 8 722 146 2
cert_rows
cert_pivot_2 1 4 2 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 26 542 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 426
cert_cover_5 2 1 0 2 4 6 138 426 2
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 722
cert_cover_5 4 3 0 3 5 6 146 722 2
cert_coverFacet 5 348
cert_cover_5 5 2 1 2 3 5 28 348 3
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 376
cert_cover_5 7 2 2 3 4 5 56 376 3
cert_coverFacet 8 184
cert_cover_2 8 3 2 4 6 56 184 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1069

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_1070.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1070

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 805, 185, 305, 465, 737, 206, 526, 342, 774, 682, 706, 572, 220, 308, 49, 145, 273, 161, 289, 545, 193, 321, 577, 769, 14, 70, 262, 518, 138, 522, 194, 322, 578, 642, 770, 28, 204, 524, 52, 84, 276, 292, 548, 772, 56, 152, 168, 552, 304, 208, 336, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_805, vertices_185, vertices_305, vertices_465, vertices_737, vertices_206, vertices_526, vertices_342, vertices_774, vertices_682, vertices_706, vertices_572, vertices_220, vertices_308] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_273, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_769, vertices_14, vertices_70, vertices_262, vertices_518, vertices_138, vertices_522, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_204, vertices_524, vertices_52, vertices_84, vertices_276, vertices_292, vertices_548, vertices_772, vertices_56, vertices_152, vertices_168, vertices_552, vertices_304, vertices_208, vertices_336, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_805), (false, vertices_185), (false, vertices_305), (false, vertices_465), (false, vertices_737), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_522), (true, vertices_194), (true, vertices_642), (true, vertices_28), (true, vertices_204), (true, vertices_524), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_552)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_204) then 19 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_52) then 11 else
  if p.val = (true, vertices_84) then 12 else
  if p.val = (true, vertices_276) then 13 else
  if p.val = (true, vertices_552) then 14 else
  0
cert_priority
cert_nodeAtPriority_9 0 305 1 14 70 262 518 138 522 194 642 28 524 52 84 276 552 835 805 204 185 465 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 70 2
cert_row_2 1 1 2 5 6 204
cert_row_4 2 0 2 4 6 8 682 138 2
cert_row_4 3 1 2 3 4 8 572 28 3
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 342
cert_cover_5 2 0 0 1 3 5 70 342 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 682
cert_cover_5 4 2 0 2 4 6 138 682 2
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 572
cert_cover_5 6 3 1 2 3 4 28 572 3
cert_coverFacet 7 220
cert_cover_5 7 1 1 2 3 5 28 220 3
cert_coverFacet 8 308
cert_cover_2 8 3 1 4 7 52 308 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1070

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_1071.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1071

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 661, 185, 905, 369, 785, 342, 710, 774, 618, 778, 354, 244, 788, 744, 41, 137, 265, 49, 145, 273, 529, 289, 641, 769, 70, 262, 518, 42, 266, 522, 98, 290, 322, 578, 770, 84, 148, 276, 532, 196, 644, 772, 616, 168, 648, 776, 112, 176, 336, 784, 224, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_661, vertices_185, vertices_905, vertices_369, vertices_785, vertices_342, vertices_710, vertices_774, vertices_618, vertices_778, vertices_354, vertices_244, vertices_788, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_265, vertices_49, vertices_145, vertices_273, vertices_529, vertices_289, vertices_641, vertices_769, vertices_70, vertices_262, vertices_518, vertices_42, vertices_266, vertices_522, vertices_98, vertices_290, vertices_322, vertices_578, vertices_770, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_644, vertices_772, vertices_616, vertices_168, vertices_648, vertices_776, vertices_112, vertices_176, vertices_336, vertices_784, vertices_224, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_661), (false, vertices_185), (false, vertices_905), (false, vertices_369), (false, vertices_785), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_522), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_84), (true, vertices_276), (true, vertices_196), (true, vertices_772), (true, vertices_616), (true, vertices_224), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 19 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_185) then 20 else
  if p.val = (false, vertices_905) then 21 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_616) then 22 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_616), by decide +kernel⟩
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
cert_row_2 0 2 4 5 8 616
cert_row_4 1 0 1 3 5 7 342 70 2
cert_row_4 2 0 1 5 6 8 710 70 3
cert_row_4 3 1 3 4 5 6 244 84 2
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 1 0 1 3 5 70 342 2
cert_coverFacet 1 710
cert_cover_5 1 2 0 1 5 6 70 710 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 618
cert_cover_5 3 0 0 2 4 5 42 618 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 244
cert_cover_5 6 3 1 3 4 5 84 244 2
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 744
cert_cover_5 8 0 2 4 5 6 616 744 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1071

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_1072.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1072

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 109, 341, 677, 773, 481, 782, 666, 282, 466, 92, 284, 556, 632, 752, 37, 69, 261, 517, 97, 161, 321, 385, 641, 769, 26, 266, 522, 146, 274, 386, 642, 770, 28, 44, 76, 268, 524, 84, 276, 548, 772, 88, 280, 536, 104, 552, 624, 208, 336, 656, 224, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_109, vertices_341, vertices_677, vertices_773, vertices_481, vertices_782, vertices_666, vertices_282, vertices_466, vertices_92, vertices_284, vertices_556, vertices_632, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_261, vertices_517, vertices_97, vertices_161, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_266, vertices_522, vertices_146, vertices_274, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_548, vertices_772, vertices_88, vertices_280, vertices_536, vertices_104, vertices_552, vertices_624, vertices_208, vertices_336, vertices_656, vertices_224, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_109), (false, vertices_341), (false, vertices_677), (false, vertices_773), (false, vertices_481), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_552), (true, vertices_624), (true, vertices_208), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_624) then 23 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(true, vertices_624), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 8 624
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 2 3 6 8 666 26 3
cert_row_4 3 0 3 5 6 7 466 146 2
cert_rows
cert_pivot_2 4 1 2 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 666
cert_cover_5 1 2 0 2 3 6 26 666 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 466
cert_cover_5 3 3 0 3 5 6 146 466 2
cert_coverFacet 4 92
cert_cover_2 4 2 1 3 5 28 92 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 632
cert_cover_5 7 0 2 3 4 5 88 632 2
cert_coverFacet 8 752
cert_cover_5 8 0 3 4 5 6 624 752 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1072

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_1073.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1073

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 341, 569, 305, 721, 481, 206, 526, 598, 426, 554, 706, 316, 540, 460, 49, 81, 273, 529, 161, 289, 545, 193, 321, 641, 14, 70, 518, 42, 138, 522, 162, 546, 194, 578, 642, 28, 204, 268, 524, 84, 276, 532, 324, 56, 536, 296, 552, 392, 304, 592, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_341, vertices_569, vertices_305, vertices_721, vertices_481, vertices_206, vertices_526, vertices_598, vertices_426, vertices_554, vertices_706, vertices_316, vertices_540, vertices_460] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_14, vertices_70, vertices_518, vertices_42, vertices_138, vertices_522, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_204, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_324, vertices_56, vertices_536, vertices_296, vertices_552, vertices_392, vertices_304, vertices_592, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_341), (false, vertices_569), (false, vertices_305), (false, vertices_721), (false, vertices_481), (true, vertices_14), (true, vertices_70), (true, vertices_518), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_194), (true, vertices_578), (true, vertices_28), (true, vertices_204), (true, vertices_268), (true, vertices_524), (true, vertices_532), (true, vertices_296), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_204) then 19 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
cert_nodeAtPriority_9 0 305 1 14 70 518 42 138 522 194 578 28 268 524 532 296 392 675 341 204 569 721 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 70 2
cert_row_2 1 1 2 5 6 204
cert_row_4 2 0 2 4 6 7 426 42 3
cert_row_4 3 1 2 3 4 7 316 28 3
cert_rows
cert_pivot_2 8 5 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 598
cert_cover_5 2 0 0 1 3 5 70 598 2
cert_coverFacet 3 426
cert_cover_5 3 2 0 2 4 6 42 426 3
cert_coverFacet 4 554
cert_cover_2 4 2 0 4 8 42 554 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 316
cert_cover_5 6 3 1 2 3 4 28 316 3
cert_coverFacet 7 540
cert_cover_2 7 2 1 3 8 28 540 3
cert_coverFacet 8 460
cert_cover_5 8 1 1 2 5 7 204 460 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1073

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_1074.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1074

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 213, 601, 457, 433, 785, 110, 270, 422, 618, 818, 204, 396, 628, 180, 73, 265, 521, 81, 145, 273, 529, 193, 385, 769, 14, 38, 262, 106, 266, 522, 290, 546, 770, 76, 140, 268, 52, 84, 148, 100, 164, 196, 388, 200, 584, 392, 176, 304, 560, 592, 784, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_213, vertices_601, vertices_457, vertices_433, vertices_785, vertices_110, vertices_270, vertices_422, vertices_618, vertices_818, vertices_204, vertices_396, vertices_628, vertices_180] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_529, vertices_193, vertices_385, vertices_769, vertices_14, vertices_38, vertices_262, vertices_106, vertices_266, vertices_522, vertices_290, vertices_546, vertices_770, vertices_76, vertices_140, vertices_268, vertices_52, vertices_84, vertices_148, vertices_100, vertices_164, vertices_196, vertices_388, vertices_200, vertices_584, vertices_392, vertices_176, vertices_304, vertices_560, vertices_592, vertices_784, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_213), (false, vertices_601), (false, vertices_457), (false, vertices_433), (false, vertices_785), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_106), (true, vertices_290), (true, vertices_546), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_52), (true, vertices_100), (true, vertices_164), (true, vertices_388), (true, vertices_560), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_106) then 17 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_164) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 785 14 38 262 290 546 76 140 268 52 100 164 388 560 608 779 106 213 601 457 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 1 4 6 7 422 38 3
cert_row_4 2 0 3 4 7 8 818 290 1
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 422
cert_cover_5 2 1 0 1 4 6 38 422 3
cert_coverFacet 3 618
cert_cover_5 3 0 0 2 4 8 106 618 3
cert_coverFacet 4 818
cert_cover_5 4 2 0 3 4 7 290 818 1
cert_coverFacet 5 204
cert_cover_2 5 2 1 5 6 76 204 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 628
cert_cover_5 7 3 1 3 4 5 52 628 3
cert_coverFacet 8 180
cert_cover_2 8 3 1 4 6 52 180 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1074

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_1075.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1075

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 395, 563, 835, 597, 113, 481, 782, 554, 460, 652, 244, 660, 836, 696, 139, 35, 259, 515, 49, 81, 529, 97, 161, 321, 577, 385, 42, 266, 522, 546, 770, 140, 268, 524, 84, 148, 532, 196, 324, 580, 644, 772, 168, 552, 392, 648, 112, 176, 560, 656, 224, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_395, vertices_563, vertices_835, vertices_597, vertices_113, vertices_481, vertices_782, vertices_554, vertices_460, vertices_652, vertices_244, vertices_660, vertices_836, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_139, vertices_35, vertices_259, vertices_515, vertices_49, vertices_81, vertices_529, vertices_97, vertices_161, vertices_321, vertices_577, vertices_385, vertices_42, vertices_266, vertices_522, vertices_546, vertices_770, vertices_140, vertices_268, vertices_524, vertices_84, vertices_148, vertices_532, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_168, vertices_552, vertices_392, vertices_648, vertices_112, vertices_176, vertices_560, vertices_656, vertices_224, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_395), (false, vertices_563), (false, vertices_835), (false, vertices_597), (false, vertices_113), (false, vertices_481), (true, vertices_522), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_196), (true, vertices_324), (true, vertices_644), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_176), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 14 16 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 17 else
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_563) then 20 else
  if p.val = (false, vertices_835) then 21 else
  if p.val = (false, vertices_597) then 15 else
  if p.val = (false, vertices_113) then 0 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_656) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
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
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 1 2 5 6 7 460 140 2
cert_row_4 2 1 3 4 5 6 244 84 2
cert_row_4 3 2 3 4 6 8 696 168 1
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 460
cert_cover_5 2 1 1 2 5 6 140 460 2
cert_coverFacet 3 652
cert_cover_2 3 2 1 6 8 140 652 3
cert_coverFacet 4 244
cert_cover_5 4 2 1 3 4 5 84 244 2
cert_coverFacet 5 660
cert_cover_2 5 3 1 6 8 148 660 3
cert_coverFacet 6 836
cert_cover_2 6 5 1 7 8 324 836 3
cert_coverFacet 7 696
cert_cover_5 7 3 2 3 4 6 168 696 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1075

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_1076.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1076

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 677, 569, 297, 713, 481, 590, 566, 214, 282, 538, 466, 436, 708, 312, 41, 73, 265, 521, 161, 289, 545, 193, 321, 641, 22, 70, 518, 26, 74, 266, 522, 210, 274, 530, 322, 52, 148, 164, 548, 196, 580, 644, 56, 280, 536, 296, 584, 304, 560, 400, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_677, vertices_569, vertices_297, vertices_713, vertices_481, vertices_590, vertices_566, vertices_214, vertices_282, vertices_538, vertices_466, vertices_436, vertices_708, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_22, vertices_70, vertices_518, vertices_26, vertices_74, vertices_266, vertices_522, vertices_210, vertices_274, vertices_530, vertices_322, vertices_52, vertices_148, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_280, vertices_536, vertices_296, vertices_584, vertices_304, vertices_560, vertices_400, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_677), (false, vertices_569), (false, vertices_297), (false, vertices_713), (false, vertices_481), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_26), (true, vertices_522), (true, vertices_210), (true, vertices_274), (true, vertices_530), (true, vertices_52), (true, vertices_148), (true, vertices_196), (true, vertices_580), (true, vertices_280), (true, vertices_304), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_210) then 17 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 297 22 70 518 26 522 274 530 52 148 196 580 280 304 400 331 210 677 569 713 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 70 2
cert_row_2 1 0 3 5 6 210
cert_row_4 2 0 1 3 4 8 566 22 3
cert_row_4 3 1 3 4 6 7 436 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 70 590 2
cert_coverFacet 1 566
cert_cover_5 1 2 0 1 3 4 22 566 3
cert_coverFacet 2 214
cert_cover_5 2 1 0 1 3 5 22 214 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 466
cert_cover_5 5 1 0 3 5 7 210 466 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 52 436 3
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1076

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_1077.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1077

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 653, 601, 457, 369, 657, 558, 310, 390, 646, 626, 658, 236, 484, 616, 73, 137, 521, 81, 145, 273, 529, 321, 385, 641, 38, 134, 262, 518, 50, 146, 274, 530, 546, 386, 642, 44, 140, 524, 228, 292, 388, 644, 104, 552, 200, 584, 112, 304, 592, 656, 352, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_653, vertices_601, vertices_457, vertices_369, vertices_657, vertices_558, vertices_310, vertices_390, vertices_646, vertices_626, vertices_658, vertices_236, vertices_484, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_521, vertices_81, vertices_145, vertices_273, vertices_529, vertices_321, vertices_385, vertices_641, vertices_38, vertices_134, vertices_262, vertices_518, vertices_50, vertices_146, vertices_274, vertices_530, vertices_546, vertices_386, vertices_642, vertices_44, vertices_140, vertices_524, vertices_228, vertices_292, vertices_388, vertices_644, vertices_104, vertices_552, vertices_200, vertices_584, vertices_112, vertices_304, vertices_592, vertices_656, vertices_352, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_653), (false, vertices_601), (false, vertices_457), (false, vertices_369), (false, vertices_657), (true, vertices_38), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_530), (true, vertices_546), (true, vertices_642), (true, vertices_44), (true, vertices_228), (true, vertices_292), (true, vertices_388), (true, vertices_104), (true, vertices_552), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_228) then 19 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 657 2 38 1 134 3 262 518 50 530 546 642 44 292 388 104 552 608 403 653 228 601 457 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 6 228
cert_row_4 1 0 1 2 4 8 558 38 2
cert_row_4 2 0 1 3 4 7 310 38 2
cert_row_4 3 0 3 4 5 8 626 50 3
cert_rows
cert_pivot_2 6 2 1 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 38 558 2
cert_coverFacet 1 310
cert_cover_5 1 2 0 1 3 4 38 310 2
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 646
cert_cover_2 3 1 0 6 8 134 646 3
cert_coverFacet 4 626
cert_cover_5 4 3 0 3 4 5 50 626 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 236
cert_cover_5 6 0 1 2 4 5 44 236 3
cert_coverFacet 7 484
cert_cover_5 7 0 1 4 5 7 228 484 3
cert_coverFacet 8 616
cert_cover_2 8 4 2 5 8 104 616 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1077

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_1078.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1078

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 661, 569, 425, 649, 113, 465, 214, 614, 390, 774, 810, 450, 908, 628, 41, 137, 521, 49, 81, 145, 529, 97, 289, 321, 385, 641, 70, 134, 262, 518, 98, 290, 546, 194, 322, 386, 770, 84, 148, 532, 612, 388, 644, 772, 296, 552, 392, 648, 776, 112, 560, 208, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_661, vertices_569, vertices_425, vertices_649, vertices_113, vertices_465, vertices_214, vertices_614, vertices_390, vertices_774, vertices_810, vertices_450, vertices_908, vertices_628] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_521, vertices_49, vertices_81, vertices_145, vertices_529, vertices_97, vertices_289, vertices_321, vertices_385, vertices_641, vertices_70, vertices_134, vertices_262, vertices_518, vertices_98, vertices_290, vertices_546, vertices_194, vertices_322, vertices_386, vertices_770, vertices_84, vertices_148, vertices_532, vertices_612, vertices_388, vertices_644, vertices_772, vertices_296, vertices_552, vertices_392, vertices_648, vertices_776, vertices_112, vertices_560, vertices_208, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_661), (false, vertices_569), (false, vertices_425), (false, vertices_649), (false, vertices_113), (false, vertices_465), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_546), (true, vertices_194), (true, vertices_386), (true, vertices_770), (true, vertices_84), (true, vertices_612), (true, vertices_388), (true, vertices_772), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 15 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_569) then 20 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_649) then 0 else
  if p.val = (false, vertices_113) then 1 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_262) then 4 else
  if p.val = (true, vertices_518) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_612) then 18 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_776) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
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
cert_row_4 0 0 1 3 5 6 214 70 2
cert_row_2 1 1 4 5 8 612
cert_row_4 2 0 2 4 7 8 810 290 1
cert_row_4 3 1 2 6 7 8 908 388 1
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 70 214 2
cert_coverFacet 1 614
cert_cover_5 1 1 0 1 4 5 70 614 2
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 810
cert_cover_5 4 2 0 2 4 7 290 810 1
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 908
cert_cover_5 6 3 1 2 6 7 388 908 1
cert_coverFacet 7 628
cert_cover_5 7 1 1 3 4 5 84 628 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1078

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_1079.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1079

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 781, 181, 357, 645, 313, 153, 838, 218, 346, 778, 738, 612, 676, 496, 37, 133, 261, 517, 25, 137, 265, 521, 49, 145, 289, 641, 90, 138, 266, 522, 194, 322, 578, 642, 770, 100, 164, 548, 324, 580, 644, 772, 152, 280, 776, 176, 304, 208, 336, 224, 352, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_781, vertices_181, vertices_357, vertices_645, vertices_313, vertices_153, vertices_838, vertices_218, vertices_346, vertices_778, vertices_738, vertices_612, vertices_676, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_517, vertices_25, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_289, vertices_641, vertices_90, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_100, vertices_164, vertices_548, vertices_324, vertices_580, vertices_644, vertices_772, vertices_152, vertices_280, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_224, vertices_352, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_781), (false, vertices_181), (false, vertices_357), (false, vertices_645), (false, vertices_313), (false, vertices_153), (true, vertices_90), (true, vertices_266), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_548), (true, vertices_580), (true, vertices_208), (true, vertices_336), (true, vertices_224), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_153) then 1 else
  if p.val = (true, vertices_90) then 16 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 645 1 153 266 194 322 578 770 548 580 208 336 224 608 672 651 90 781 181 357 313
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
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 176 496 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1079

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_1080.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1080

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [199, 611, 643, 397, 309, 101, 689, 401, 458, 842, 914, 620, 300, 204, 824, 67, 131, 515, 37, 69, 133, 261, 49, 145, 273, 97, 545, 385, 641, 330, 194, 578, 386, 642, 770, 44, 76, 140, 268, 100, 292, 196, 296, 552, 200, 584, 392, 776, 304, 560, 400, 656, 784, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_199, vertices_611, vertices_643, vertices_397, vertices_309, vertices_101, vertices_689, vertices_401, vertices_458, vertices_842, vertices_914, vertices_620, vertices_300, vertices_204, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_515, vertices_37, vertices_69, vertices_133, vertices_261, vertices_49, vertices_145, vertices_273, vertices_97, vertices_545, vertices_385, vertices_641, vertices_330, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_140, vertices_268, vertices_100, vertices_292, vertices_196, vertices_296, vertices_552, vertices_200, vertices_584, vertices_392, vertices_776, vertices_304, vertices_560, vertices_400, vertices_656, vertices_784, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_199), (false, vertices_611), (false, vertices_643), (false, vertices_397), (false, vertices_309), (false, vertices_101), (false, vertices_689), (false, vertices_401), (true, vertices_330), (true, vertices_386), (true, vertices_770), (true, vertices_44), (true, vertices_76), (true, vertices_296), (true, vertices_552), (true, vertices_200), (true, vertices_584), (true, vertices_776), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 13 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_611) then 18 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_397) then 15 else
  if p.val = (false, vertices_309) then 16 else
  if p.val = (false, vertices_101) then 1 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (false, vertices_401) then 2 else
  if p.val = (true, vertices_330) then 19 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_784) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_101), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_330), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 6 7 8 914 386 1
cert_row_2 1 0 2 5 7 330
cert_row_4 2 1 2 4 5 8 620 44 3
cert_row_4 3 2 3 4 7 8 824 296 1
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 458
cert_cover_5 0 1 0 2 5 6 330 458 3
cert_coverFacet 1 842
cert_cover_5 1 1 0 2 5 8 330 842 3
cert_coverFacet 2 914
cert_cover_5 2 0 0 3 6 7 386 914 1
cert_coverFacet 3 620
cert_cover_5 3 2 1 2 4 5 44 620 3
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 204
cert_cover_2 5 2 1 5 6 76 204 3
cert_coverFacet 6 824
cert_cover_5 6 3 2 3 4 7 296 824 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1080

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_1082.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1082

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [103, 551, 659, 195, 789, 453, 409, 682, 482, 620, 836, 856, 664, 360, 424, 39, 67, 131, 515, 69, 261, 517, 145, 273, 529, 193, 385, 98, 162, 546, 194, 642, 100, 548, 324, 580, 772, 152, 280, 536, 104, 168, 296, 552, 328, 584, 392, 648, 656, 784, 352, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_103, vertices_551, vertices_659, vertices_195, vertices_789, vertices_453, vertices_409, vertices_682, vertices_482, vertices_620, vertices_836, vertices_856, vertices_664, vertices_360, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_39, vertices_67, vertices_131, vertices_515, vertices_69, vertices_261, vertices_517, vertices_145, vertices_273, vertices_529, vertices_193, vertices_385, vertices_98, vertices_162, vertices_546, vertices_194, vertices_642, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_296, vertices_552, vertices_328, vertices_584, vertices_392, vertices_648, vertices_656, vertices_784, vertices_352, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_103), (false, vertices_551), (false, vertices_659), (false, vertices_195), (false, vertices_789), (false, vertices_453), (false, vertices_409), (true, vertices_162), (true, vertices_580), (true, vertices_536), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_584), (true, vertices_648), (true, vertices_352), (true, vertices_416), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_103) then 15 else
  if p.val = (false, vertices_551) then 16 else
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_580) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_103), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 5 8 620 100 1
cert_row_4 1 2 3 5 7 8 856 280 2
cert_row_4 2 0 2 4 6 8 682 162 1
cert_row_4 3 0 4 5 6 7 482 98 3
cert_rows
cert_pivot_2 1 3 2 0
cert_heightProof 4
cert_coverFacet 0 682
cert_cover_5 0 2 0 2 4 6 162 682 1
cert_coverFacet 1 482
cert_cover_5 1 3 0 4 5 6 98 482 3
cert_coverFacet 2 620
cert_cover_5 2 0 1 2 4 5 100 620 1
cert_coverFacet 3 836
cert_cover_2 3 5 1 7 8 324 836 3
cert_coverFacet 4 856
cert_cover_5 4 1 2 3 5 7 280 856 2
cert_coverFacet 5 664
cert_cover_2 5 3 2 6 8 152 664 3
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1082

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_1083.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1083

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 213, 533, 901, 569, 425, 177, 710, 362, 618, 466, 898, 628, 368, 432, 21, 133, 517, 41, 265, 521, 49, 145, 529, 161, 385, 769, 106, 266, 522, 194, 322, 578, 386, 642, 770, 84, 532, 196, 580, 644, 296, 552, 112, 176, 304, 560, 208, 336, 400, 352, 608, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_213, vertices_533, vertices_901, vertices_569, vertices_425, vertices_177, vertices_710, vertices_362, vertices_618, vertices_466, vertices_898, vertices_628, vertices_368, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_41, vertices_265, vertices_521, vertices_49, vertices_145, vertices_529, vertices_161, vertices_385, vertices_769, vertices_106, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_84, vertices_532, vertices_196, vertices_580, vertices_644, vertices_296, vertices_552, vertices_112, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_400, vertices_352, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_213), (false, vertices_533), (false, vertices_901), (false, vertices_569), (false, vertices_425), (false, vertices_177), (true, vertices_106), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_580), (true, vertices_112), (true, vertices_304), (true, vertices_336), (true, vertices_400), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_177) then 1 else
  if p.val = (true, vertices_106) then 16 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
cert_nodeAtPriority_25 0 533 1 177 194 322 578 386 642 580 112 304 336 400 352 608 779 106 213 901 569 425
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 3 5 6 7 466 194 1
cert_row_4 2 0 1 5 6 8 710 194 1
cert_row_4 3 1 3 4 5 8 628 84 2
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 2 0 1 5 6 194 710 1
cert_coverFacet 1 362
cert_cover_5 1 0 0 2 4 7 106 362 3
cert_coverFacet 2 618
cert_cover_5 2 0 0 2 4 8 106 618 3
cert_coverFacet 3 466
cert_cover_5 3 1 0 3 5 6 194 466 1
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 628
cert_cover_5 5 3 1 3 4 5 84 628 2
cert_coverFacet 6 368
cert_cover_2 6 4 3 5 7 112 368 3
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1083

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_1084.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1084

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 653, 213, 837, 369, 401, 558, 314, 394, 650, 866, 236, 612, 248, 408, 69, 133, 517, 81, 145, 273, 321, 385, 641, 769, 42, 138, 266, 522, 290, 546, 386, 642, 770, 44, 140, 524, 100, 548, 196, 580, 56, 152, 280, 232, 392, 648, 112, 304, 208, 400, 352, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_653, vertices_213, vertices_837, vertices_369, vertices_401, vertices_558, vertices_314, vertices_394, vertices_650, vertices_866, vertices_236, vertices_612, vertices_248, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_81, vertices_145, vertices_273, vertices_321, vertices_385, vertices_641, vertices_769, vertices_42, vertices_138, vertices_266, vertices_522, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_524, vertices_100, vertices_548, vertices_196, vertices_580, vertices_56, vertices_152, vertices_280, vertices_232, vertices_392, vertices_648, vertices_112, vertices_304, vertices_208, vertices_400, vertices_352, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_653), (false, vertices_213), (false, vertices_837), (false, vertices_369), (false, vertices_401), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_546), (true, vertices_44), (true, vertices_100), (true, vertices_548), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_232), (true, vertices_392), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_232) then 22 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
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
cert_row_2 0 2 4 5 6 232
cert_row_4 1 0 1 2 4 8 558 42 1
cert_row_4 2 0 2 3 4 7 314 42 2
cert_row_4 3 0 4 5 7 8 866 290 2
cert_rows
cert_pivot_2 6 1 2 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 42 558 1
cert_coverFacet 1 314
cert_cover_5 1 2 0 2 3 4 42 314 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 866
cert_cover_5 4 3 0 4 5 7 290 866 2
cert_coverFacet 5 236
cert_cover_5 5 0 1 2 4 5 44 236 3
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 248
cert_cover_5 7 0 2 3 4 5 56 248 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1084

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_1085.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1085

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 781, 617, 457, 241, 417, 542, 150, 422, 774, 626, 178, 348, 468, 600, 73, 265, 521, 97, 161, 289, 545, 193, 385, 769, 22, 134, 262, 518, 50, 146, 530, 162, 290, 546, 770, 28, 268, 524, 340, 148, 388, 772, 88, 536, 328, 584, 112, 176, 208, 592, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_781, vertices_617, vertices_457, vertices_241, vertices_417, vertices_542, vertices_150, vertices_422, vertices_774, vertices_626, vertices_178, vertices_348, vertices_468, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_385, vertices_769, vertices_22, vertices_134, vertices_262, vertices_518, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_770, vertices_28, vertices_268, vertices_524, vertices_340, vertices_148, vertices_388, vertices_772, vertices_88, vertices_536, vertices_328, vertices_584, vertices_112, vertices_176, vertices_208, vertices_592, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_781), (false, vertices_617), (false, vertices_457), (false, vertices_241), (false, vertices_417), (true, vertices_22), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_28), (true, vertices_340), (true, vertices_148), (true, vertices_388), (true, vertices_88), (true, vertices_536), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_162) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_340) then 19 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 417 2 22 1 134 3 262 518 50 146 530 162 28 148 388 88 536 592 803 781 340 617 457 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 22 2
cert_row_4 1 0 1 4 6 7 422 134 2
cert_row_2 2 1 3 5 7 340
cert_row_4 3 0 3 4 5 8 626 50 3
cert_rows
cert_pivot_2 2 6 1 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 22 542 2
cert_coverFacet 1 150
cert_cover_2 1 1 0 3 6 22 150 3
cert_coverFacet 2 422
cert_cover_5 2 1 0 1 4 6 134 422 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 626
cert_cover_5 4 3 0 3 4 5 50 626 3
cert_coverFacet 5 178
cert_cover_2 5 3 0 4 6 50 178 3
cert_coverFacet 6 348
cert_cover_5 6 2 1 2 3 5 28 348 3
cert_coverFacet 7 468
cert_cover_5 7 2 1 3 5 6 340 468 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1085

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_1087.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1087

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 307, 451, 643, 361, 113, 721, 398, 278, 646, 812, 716, 820, 632, 456, 19, 131, 259, 515, 49, 81, 529, 97, 289, 193, 321, 641, 22, 134, 262, 518, 274, 386, 642, 140, 268, 524, 276, 532, 804, 644, 104, 296, 552, 200, 328, 584, 392, 112, 304, 560, 592, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_307, vertices_451, vertices_643, vertices_361, vertices_113, vertices_721, vertices_398, vertices_278, vertices_646, vertices_812, vertices_716, vertices_820, vertices_632, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_49, vertices_81, vertices_529, vertices_97, vertices_289, vertices_193, vertices_321, vertices_641, vertices_22, vertices_134, vertices_262, vertices_518, vertices_274, vertices_386, vertices_642, vertices_140, vertices_268, vertices_524, vertices_276, vertices_532, vertices_804, vertices_644, vertices_104, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_112, vertices_304, vertices_560, vertices_592, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_307), (false, vertices_451), (false, vertices_643), (false, vertices_361), (false, vertices_113), (false, vertices_721), (true, vertices_134), (true, vertices_262), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_804), (true, vertices_644), (true, vertices_552), (true, vertices_200), (true, vertices_584), (true, vertices_392), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 15 else
  if p.val = (false, vertices_307) then 16 else
  if p.val = (false, vertices_451) then 17 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_113) then 1 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_804) then 19 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_560) then 13 else
  0
cert_priority
cert_nodeAtPriority_47 643 113 134 262 140 268 524 276 644 552 200 584 392 560 535 307 451 804 361 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_2 1 1 4 7 8 804
cert_row_4 2 1 2 5 6 8 716 140 2
cert_row_4 3 2 3 4 5 8 632 104 1
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 812
cert_cover_5 3 1 1 2 4 7 268 812 2
cert_coverFacet 4 716
cert_cover_5 4 2 1 2 5 6 140 716 2
cert_coverFacet 5 820
cert_cover_5 5 1 1 3 4 7 276 820 2
cert_coverFacet 6 632
cert_cover_5 6 3 2 3 4 5 104 632 1
cert_coverFacet 7 456
cert_cover_2 7 5 2 6 7 200 456 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1087

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_1088.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1088

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 51, 403, 611, 901, 113, 721, 558, 58, 282, 364, 780, 468, 740, 376, 19, 35, 259, 515, 49, 81, 145, 97, 577, 385, 641, 769, 26, 42, 266, 522, 50, 274, 546, 44, 268, 524, 100, 548, 196, 324, 388, 644, 772, 56, 280, 360, 776, 112, 208, 336, 400, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_51, vertices_403, vertices_611, vertices_901, vertices_113, vertices_721, vertices_558, vertices_58, vertices_282, vertices_364, vertices_780, vertices_468, vertices_740, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_515, vertices_49, vertices_81, vertices_145, vertices_97, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_546, vertices_44, vertices_268, vertices_524, vertices_100, vertices_548, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_56, vertices_280, vertices_360, vertices_776, vertices_112, vertices_208, vertices_336, vertices_400, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_51), (false, vertices_403), (false, vertices_611), (false, vertices_901), (false, vertices_113), (false, vertices_721), (true, vertices_26), (true, vertices_42), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_100), (true, vertices_548), (true, vertices_196), (true, vertices_324), (true, vertices_56), (true, vertices_280), (true, vertices_360), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_51) then 0 else
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_113) then 1 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_360) then 21 else
  if p.val = (true, vertices_336) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
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
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1088

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_1089.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1089

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 709, 665, 617, 393, 481, 158, 790, 454, 58, 394, 818, 660, 868, 568, 41, 137, 265, 521, 97, 289, 193, 577, 385, 641, 22, 134, 262, 26, 42, 138, 266, 50, 786, 290, 386, 148, 532, 196, 324, 580, 644, 772, 56, 152, 536, 552, 392, 560, 656, 352, 608, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_709, vertices_665, vertices_617, vertices_393, vertices_481, vertices_158, vertices_790, vertices_454, vertices_58, vertices_394, vertices_818, vertices_660, vertices_868, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_265, vertices_521, vertices_97, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_22, vertices_134, vertices_262, vertices_26, vertices_42, vertices_138, vertices_266, vertices_50, vertices_786, vertices_290, vertices_386, vertices_148, vertices_532, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_56, vertices_152, vertices_536, vertices_552, vertices_392, vertices_560, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_709), (false, vertices_665), (false, vertices_617), (false, vertices_393), (false, vertices_481), (true, vertices_22), (true, vertices_134), (true, vertices_262), (true, vertices_26), (true, vertices_138), (true, vertices_50), (true, vertices_786), (true, vertices_386), (true, vertices_148), (true, vertices_532), (true, vertices_324), (true, vertices_772), (true, vertices_56), (true, vertices_560), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_50) then 6 else
  if p.val = (true, vertices_786) then 17 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 393 22 134 262 26 138 50 386 148 532 324 772 56 560 800 299 786 709 665 617 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 6 158 22 2
cert_row_2 1 0 3 7 8 786
cert_row_4 2 0 1 5 6 7 454 134 2
cert_row_4 3 1 4 5 7 8 868 324 1
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 22 158 2
cert_coverFacet 1 790
cert_cover_5 1 1 0 1 3 7 22 790 3
cert_coverFacet 2 454
cert_cover_5 2 2 0 1 5 6 134 454 2
cert_coverFacet 3 58
cert_cover_2 3 2 0 3 4 26 58 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 818
cert_cover_5 5 1 0 3 4 7 50 818 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 868
cert_cover_5 7 3 1 4 5 7 324 868 1
cert_coverFacet 8 568
cert_cover_2 8 3 2 4 8 56 568 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1089

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_1090.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1090

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 309, 357, 345, 665, 617, 177, 54, 278, 614, 902, 410, 178, 844, 904, 293, 25, 73, 521, 49, 145, 273, 97, 161, 545, 321, 641, 22, 38, 262, 518, 50, 146, 274, 162, 546, 386, 642, 52, 276, 100, 324, 580, 772, 152, 280, 328, 584, 392, 648, 776, 176, 608, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_309, vertices_357, vertices_345, vertices_665, vertices_617, vertices_177, vertices_54, vertices_278, vertices_614, vertices_902, vertices_410, vertices_178, vertices_844, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_293, vertices_25, vertices_73, vertices_521, vertices_49, vertices_145, vertices_273, vertices_97, vertices_161, vertices_545, vertices_321, vertices_641, vertices_22, vertices_38, vertices_262, vertices_518, vertices_50, vertices_146, vertices_274, vertices_162, vertices_546, vertices_386, vertices_642, vertices_52, vertices_276, vertices_100, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_328, vertices_584, vertices_392, vertices_648, vertices_776, vertices_176, vertices_608, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_309), (false, vertices_357), (false, vertices_345), (false, vertices_665), (false, vertices_617), (false, vertices_177), (true, vertices_22), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_386), (true, vertices_580), (true, vertices_772), (true, vertices_392), (true, vertices_776), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_309) then 17 else
  if p.val = (false, vertices_357) then 18 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_274) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
cert_nodeAtPriority_48 0 177 2 22 1 38 262 518 50 146 274 386 580 772 392 776 896 675 309 357 345 665 617
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 8 614 38 3
cert_row_4 1 0 2 3 6 7 410 146 1
cert_row_4 2 0 1 6 7 8 902 262 2
cert_row_4 3 1 2 5 7 8 844 324 1
cert_rows
cert_pivot_2 4 3 0 1
cert_heightProof 4
cert_coverFacet 0 54
cert_cover_2 0 1 0 3 4 22 54 3
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 614
cert_cover_5 2 0 0 1 4 5 38 614 3
cert_coverFacet 3 902
cert_cover_5 3 2 0 1 6 7 262 902 2
cert_coverFacet 4 410
cert_cover_5 4 1 0 2 3 6 146 410 1
cert_coverFacet 5 178
cert_cover_2 5 3 0 4 6 50 178 3
cert_coverFacet 6 844
cert_cover_5 6 3 1 2 5 7 324 844 1
cert_coverFacet 7 904
cert_cover_2 7 6 2 7 8 392 904 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1090

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_1091.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1091

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 709, 569, 433, 657, 865, 46, 206, 806, 838, 314, 394, 668, 556, 408, 49, 145, 529, 289, 545, 193, 321, 577, 385, 641, 14, 38, 70, 774, 42, 138, 266, 290, 194, 322, 386, 44, 140, 524, 548, 196, 580, 644, 56, 152, 280, 536, 552, 392, 304, 400, 656, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_709, vertices_569, vertices_433, vertices_657, vertices_865, vertices_46, vertices_206, vertices_806, vertices_838, vertices_314, vertices_394, vertices_668, vertices_556, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_529, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_14, vertices_38, vertices_70, vertices_774, vertices_42, vertices_138, vertices_266, vertices_290, vertices_194, vertices_322, vertices_386, vertices_44, vertices_140, vertices_524, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_152, vertices_280, vertices_536, vertices_552, vertices_392, vertices_304, vertices_400, vertices_656, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_709), (false, vertices_569), (false, vertices_433), (false, vertices_657), (false, vertices_865), (true, vertices_14), (true, vertices_38), (true, vertices_70), (true, vertices_774), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_290), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_548), (true, vertices_152), (true, vertices_280), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_70) then 3 else
  if p.val = (true, vertices_774) then 17 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 657 14 38 70 42 138 266 290 44 140 524 548 152 280 392 451 774 709 569 433 865
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_4 1 0 2 3 4 7 314 42 2
cert_row_2 2 0 1 7 8 774
cert_row_4 3 1 2 3 6 8 668 140 2
cert_rows
cert_pivot_2 5 4 0 1
cert_heightProof 4
cert_coverFacet 0 46
cert_cover_2 0 1 0 2 4 14 46 3
cert_coverFacet 1 206
cert_cover_5 1 0 0 1 2 5 14 206 3
cert_coverFacet 2 806
cert_cover_5 2 2 0 1 4 7 38 806 3
cert_coverFacet 3 838
cert_cover_5 3 2 0 1 5 7 70 838 3
cert_coverFacet 4 314
cert_cover_5 4 1 0 2 3 4 42 314 2
cert_coverFacet 5 394
cert_cover_2 5 2 0 6 7 138 394 3
cert_coverFacet 6 668
cert_cover_5 6 3 1 2 3 6 140 668 2
cert_coverFacet 7 556
cert_cover_2 7 2 1 4 8 44 556 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1091

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_1092.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1092

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 403, 611, 163, 601, 241, 785, 558, 166, 390, 796, 364, 484, 472, 616, 35, 131, 259, 515, 81, 145, 273, 529, 97, 161, 577, 769, 38, 134, 262, 518, 162, 546, 386, 44, 268, 524, 356, 164, 388, 772, 88, 280, 536, 104, 552, 328, 584, 208, 400, 784, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_403, vertices_611, vertices_163, vertices_601, vertices_241, vertices_785, vertices_558, vertices_166, vertices_390, vertices_796, vertices_364, vertices_484, vertices_472, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_81, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_577, vertices_769, vertices_38, vertices_134, vertices_262, vertices_518, vertices_162, vertices_546, vertices_386, vertices_44, vertices_268, vertices_524, vertices_356, vertices_164, vertices_388, vertices_772, vertices_88, vertices_280, vertices_536, vertices_104, vertices_552, vertices_328, vertices_584, vertices_208, vertices_400, vertices_784, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_403), (false, vertices_611), (false, vertices_163), (false, vertices_601), (false, vertices_241), (false, vertices_785), (true, vertices_38), (true, vertices_134), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_356), (true, vertices_164), (true, vertices_388), (true, vertices_280), (true, vertices_104), (true, vertices_552), (true, vertices_328), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_785) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_356) then 19 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
cert_nodeAtPriority_47 163 785 38 134 44 268 524 164 388 280 104 552 328 448 775 403 611 356 601 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 38 2
cert_row_2 1 1 4 5 7 356
cert_row_4 2 1 2 3 7 8 796 268 2
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 38 558 2
cert_coverFacet 1 166
cert_cover_2 1 1 0 4 6 38 166 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 796
cert_cover_5 3 2 1 2 3 7 268 796 2
cert_coverFacet 4 364
cert_cover_5 4 1 1 2 4 5 44 364 3
cert_coverFacet 5 484
cert_cover_5 5 1 1 4 5 6 356 484 3
cert_coverFacet 6 472
cert_cover_5 6 3 2 3 5 6 88 472 3
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1092

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_1095.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1095

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [205, 405, 837, 617, 905, 310, 570, 402, 658, 866, 898, 244, 356, 248, 664, 69, 133, 261, 73, 137, 521, 577, 385, 769, 50, 146, 274, 530, 290, 546, 386, 642, 770, 52, 148, 276, 100, 292, 196, 324, 56, 152, 536, 104, 552, 200, 648, 240, 400, 656, 352, 608, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_205, vertices_405, vertices_837, vertices_617, vertices_905, vertices_310, vertices_570, vertices_402, vertices_658, vertices_866, vertices_898, vertices_244, vertices_356, vertices_248, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_73, vertices_137, vertices_521, vertices_577, vertices_385, vertices_769, vertices_50, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_52, vertices_148, vertices_276, vertices_100, vertices_292, vertices_196, vertices_324, vertices_56, vertices_152, vertices_536, vertices_104, vertices_552, vertices_200, vertices_648, vertices_240, vertices_400, vertices_656, vertices_352, vertices_608, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_205), (false, vertices_405), (false, vertices_837), (false, vertices_617), (false, vertices_905), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_52), (true, vertices_100), (true, vertices_292), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_240), (true, vertices_656), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 18 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_205) then 19 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_905) then 24 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_536) then 14 else
  if p.val = (true, vertices_240) then 26 else
  if p.val = (true, vertices_656) then 15 else
  if p.val = (true, vertices_352) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 6 240
cert_row_4 1 0 1 3 4 7 310 50 1
cert_row_4 2 0 2 3 4 8 570 50 1
cert_row_4 3 0 4 5 7 8 866 290 2
cert_rows
cert_pivot_2 6 1 2 0
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 1 0 1 3 4 50 310 1
cert_coverFacet 1 570
cert_cover_5 1 2 0 2 3 4 50 570 1
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 866
cert_cover_5 4 3 0 4 5 7 290 866 2
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 244
cert_cover_5 6 0 1 3 4 5 52 244 3
cert_coverFacet 7 356
cert_cover_2 7 4 1 5 7 100 356 3
cert_coverFacet 8 248
cert_cover_5 8 0 2 3 4 5 56 248 3
cert_coverFacet 9 664
cert_cover_2 9 3 2 6 8 152 664 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1095

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_1096.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1096

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 205, 117, 661, 121, 281, 905, 566, 58, 282, 298, 866, 612, 964, 488, 21, 69, 133, 25, 73, 137, 265, 113, 273, 529, 641, 769, 26, 42, 266, 50, 274, 530, 290, 546, 770, 52, 532, 100, 548, 196, 580, 644, 56, 280, 104, 296, 200, 392, 352, 608, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_205, vertices_117, vertices_661, vertices_121, vertices_281, vertices_905, vertices_566, vertices_58, vertices_282, vertices_298, vertices_866, vertices_612, vertices_964, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_133, vertices_25, vertices_73, vertices_137, vertices_265, vertices_113, vertices_273, vertices_529, vertices_641, vertices_769, vertices_26, vertices_42, vertices_266, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_52, vertices_532, vertices_100, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_280, vertices_104, vertices_296, vertices_200, vertices_392, vertices_352, vertices_608, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_205), (false, vertices_117), (false, vertices_661), (false, vertices_121), (false, vertices_281), (false, vertices_905), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_50), (true, vertices_290), (true, vertices_546), (true, vertices_548), (true, vertices_580), (true, vertices_296), (true, vertices_352), (true, vertices_608), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 21 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_117) then 22 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_121) then 23 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_905) then 20 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_448) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 50 1
cert_row_4 1 0 4 5 7 8 866 290 2
cert_row_4 2 1 5 6 7 8 964 196 3
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
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 866
cert_cover_5 4 1 0 4 5 7 290 866 2
cert_coverFacet 5 612
cert_cover_2 5 4 1 5 8 100 612 3
cert_coverFacet 6 964
cert_cover_5 6 2 1 5 6 7 196 964 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1096

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_1097.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1097

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 453, 57, 345, 777, 241, 929, 286, 598, 902, 58, 778, 626, 340, 740, 25, 41, 265, 521, 49, 81, 161, 545, 193, 321, 385, 769, 22, 262, 518, 26, 42, 266, 522, 50, 594, 546, 770, 84, 276, 196, 324, 580, 388, 644, 56, 280, 776, 112, 336, 224, 608, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_453, vertices_57, vertices_345, vertices_777, vertices_241, vertices_929, vertices_286, vertices_598, vertices_902, vertices_58, vertices_778, vertices_626, vertices_340, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_521, vertices_49, vertices_81, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_22, vertices_262, vertices_518, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_594, vertices_546, vertices_770, vertices_84, vertices_276, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_56, vertices_280, vertices_776, vertices_112, vertices_336, vertices_224, vertices_608, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_453), (false, vertices_57), (false, vertices_345), (false, vertices_777), (false, vertices_241), (false, vertices_929), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_266), (true, vertices_50), (true, vertices_594), (true, vertices_770), (true, vertices_84), (true, vertices_276), (true, vertices_580), (true, vertices_644), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 15 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (false, vertices_929) then 24 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_50) then 7 else
  if p.val = (true, vertices_594) then 16 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_644) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_57), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_594), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 7 286 22 2
cert_row_2 1 0 3 5 8 594
cert_row_4 2 0 1 6 7 8 902 262 2
cert_row_4 3 1 4 5 6 8 740 196 1
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 22 286 2
cert_coverFacet 1 598
cert_cover_5 1 1 0 1 3 5 22 598 3
cert_coverFacet 2 902
cert_cover_5 2 2 0 1 6 7 262 902 2
cert_coverFacet 3 58
cert_cover_2 3 2 0 3 4 26 58 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 626
cert_cover_5 5 1 0 3 4 5 50 626 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 740
cert_cover_5 7 3 1 4 5 6 196 740 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1097

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_1099.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1099

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 285, 557, 837, 297, 737, 790, 410, 426, 242, 594, 834, 540, 728, 680, 13, 261, 517, 41, 265, 97, 289, 545, 321, 577, 394, 82, 146, 274, 530, 98, 162, 290, 322, 578, 770, 28, 524, 276, 532, 772, 152, 280, 536, 168, 296, 552, 648, 208, 592, 224, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_285, vertices_557, vertices_837, vertices_297, vertices_737, vertices_790, vertices_410, vertices_426, vertices_242, vertices_594, vertices_834, vertices_540, vertices_728, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_261, vertices_517, vertices_41, vertices_265, vertices_97, vertices_289, vertices_545, vertices_321, vertices_577, vertices_394, vertices_82, vertices_146, vertices_274, vertices_530, vertices_98, vertices_162, vertices_290, vertices_322, vertices_578, vertices_770, vertices_28, vertices_524, vertices_276, vertices_532, vertices_772, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_648, vertices_208, vertices_592, vertices_224, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_285), (false, vertices_557), (false, vertices_837), (false, vertices_297), (false, vertices_737), (true, vertices_394), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_578), (true, vertices_770), (true, vertices_532), (true, vertices_152), (true, vertices_536), (true, vertices_168), (true, vertices_648), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 16 else
  if p.val = (false, vertices_285) then 19 else
  if p.val = (false, vertices_557) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_394) then 17 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inl 2
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
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_2 1 0 2 6 7 394
cert_row_4 2 0 3 4 5 6 242 82 2
cert_row_4 3 2 3 5 6 8 728 152 2
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 410
cert_cover_5 1 1 0 2 3 6 394 410 2
cert_coverFacet 2 426
cert_cover_5 2 1 0 2 4 6 394 426 2
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 82 242 2
cert_coverFacet 4 594
cert_cover_2 4 3 0 5 8 82 594 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 728
cert_cover_5 7 3 2 3 5 6 152 728 2
cert_coverFacet 8 680
cert_cover_2 8 4 2 6 8 168 680 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1099

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3633 : Certifies 3633 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1065.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3634 : Certifies 3634 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1066.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3635 : Certifies 3635 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1067.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3636 : Certifies 3636 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1068.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3637 : Certifies 3637 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1069.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3638 : Certifies 3638 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1070.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3639 : Certifies 3639 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1071.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3640 : Certifies 3640 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1072.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3641 : Certifies 3641 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1073.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3642 : Certifies 3642 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1074.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3643 : Certifies 3643 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1075.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3644 : Certifies 3644 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1076.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3645 : Certifies 3645 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1077.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3646 : Certifies 3646 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1078.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3647 : Certifies 3647 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1079.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3648 : Certifies 3648 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1080.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3649 : Certifies 3649 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1082.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3650 : Certifies 3650 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1083.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3651 : Certifies 3651 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1084.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3652 : Certifies 3652 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1085.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3653 : Certifies 3653 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1087.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3654 : Certifies 3654 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1088.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3655 : Certifies 3655 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1089.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3656 : Certifies 3656 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1090.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3657 : Certifies 3657 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1091.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3658 : Certifies 3658 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1092.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3659 : Certifies 3659 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1095.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3660 : Certifies 3660 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1096.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3661 : Certifies 3661 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1097.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3662 : Certifies 3662 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1099.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B120 (j : Fin 30) :
    Certifies (3633 + j.val) := by
  fin_cases j
  · exact projection_3633
  · exact projection_3634
  · exact projection_3635
  · exact projection_3636
  · exact projection_3637
  · exact projection_3638
  · exact projection_3639
  · exact projection_3640
  · exact projection_3641
  · exact projection_3642
  · exact projection_3643
  · exact projection_3644
  · exact projection_3645
  · exact projection_3646
  · exact projection_3647
  · exact projection_3648
  · exact projection_3649
  · exact projection_3650
  · exact projection_3651
  · exact projection_3652
  · exact projection_3653
  · exact projection_3654
  · exact projection_3655
  · exact projection_3656
  · exact projection_3657
  · exact projection_3658
  · exact projection_3659
  · exact projection_3660
  · exact projection_3661
  · exact projection_3662

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
