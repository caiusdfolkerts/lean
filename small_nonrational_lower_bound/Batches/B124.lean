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
/- Source: ProjectionCertificates/R_m15e10q1_1194.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1194

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 301, 837, 681, 433, 897, 94, 710, 538, 690, 466, 348, 312, 568, 960, 13, 261, 517, 41, 521, 161, 289, 385, 641, 769, 14, 70, 518, 26, 522, 82, 146, 530, 194, 642, 92, 268, 324, 580, 56, 280, 536, 296, 552, 176, 304, 560, 336, 400, 672, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_301, vertices_837, vertices_681, vertices_433, vertices_897, vertices_94, vertices_710, vertices_538, vertices_690, vertices_466, vertices_348, vertices_312, vertices_568, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_261, vertices_517, vertices_41, vertices_521, vertices_161, vertices_289, vertices_385, vertices_641, vertices_769, vertices_14, vertices_70, vertices_518, vertices_26, vertices_522, vertices_82, vertices_146, vertices_530, vertices_194, vertices_642, vertices_92, vertices_268, vertices_324, vertices_580, vertices_56, vertices_280, vertices_536, vertices_296, vertices_552, vertices_176, vertices_304, vertices_560, vertices_336, vertices_400, vertices_672, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_301), (false, vertices_837), (false, vertices_681), (false, vertices_433), (false, vertices_897), (true, vertices_70), (true, vertices_26), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_194), (true, vertices_642), (true, vertices_92), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_560), (true, vertices_336), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 16 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_92) then 20 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_448) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
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
cert_row_2 0 1 2 3 5 92
cert_row_4 1 0 1 5 6 8 710 70 3
cert_row_4 2 0 3 4 6 8 690 146 2
cert_row_4 3 0 3 5 6 7 466 82 3
cert_rows
cert_pivot_2 2 1 4 0
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 14 94 3
cert_coverFacet 1 710
cert_cover_5 1 1 0 1 5 6 70 710 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 690
cert_cover_5 3 2 0 3 4 6 146 690 2
cert_coverFacet 4 466
cert_cover_5 4 3 0 3 5 6 82 466 3
cert_coverFacet 5 348
cert_cover_5 5 0 1 2 3 7 92 348 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coverFacet 8 960
cert_cover_2 8 6 5 7 8 448 960 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1194

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_1195.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1195

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 173, 405, 533, 549, 625, 481, 654, 662, 602, 426, 330, 402, 620, 360, 21, 37, 133, 517, 81, 273, 529, 97, 161, 545, 321, 385, 646, 74, 138, 266, 522, 82, 146, 274, 530, 322, 386, 44, 140, 524, 148, 532, 548, 104, 168, 296, 328, 584, 592, 400, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_173, vertices_405, vertices_533, vertices_549, vertices_625, vertices_481, vertices_654, vertices_662, vertices_602, vertices_426, vertices_330, vertices_402, vertices_620, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_133, vertices_517, vertices_81, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_321, vertices_385, vertices_646, vertices_74, vertices_138, vertices_266, vertices_522, vertices_82, vertices_146, vertices_274, vertices_530, vertices_322, vertices_386, vertices_44, vertices_140, vertices_524, vertices_148, vertices_532, vertices_548, vertices_104, vertices_168, vertices_296, vertices_328, vertices_584, vertices_592, vertices_400, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_173), (false, vertices_405), (false, vertices_533), (false, vertices_549), (false, vertices_625), (false, vertices_481), (true, vertices_646), (true, vertices_74), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_386), (true, vertices_524), (true, vertices_104), (true, vertices_296), (true, vertices_328), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 15 else
  if p.val = (false, vertices_173) then 18 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_549) then 1 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_646) then 16 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_584) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_549), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_646), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
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
cert_row_4 0 0 2 3 5 8 602 74 2
cert_row_4 1 0 2 4 6 7 426 138 2
cert_row_2 2 0 1 6 8 646
cert_row_4 3 1 2 4 5 8 620 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 646 654 2
cert_coverFacet 1 662
cert_cover_5 1 2 0 1 3 6 646 662 2
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 5 74 602 2
cert_coverFacet 3 426
cert_cover_5 3 1 0 2 4 6 138 426 2
cert_coverFacet 4 330
cert_cover_2 4 2 0 5 7 74 330 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 44 620 3
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1195

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_1196.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1196

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 107, 323, 771, 681, 241, 961, 286, 902, 346, 540, 692, 468, 120, 568, 11, 67, 259, 515, 41, 521, 97, 161, 193, 321, 641, 769, 14, 262, 518, 282, 74, 322, 770, 28, 524, 148, 276, 532, 388, 644, 56, 88, 536, 104, 552, 112, 176, 560, 208, 336, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_107, vertices_323, vertices_771, vertices_681, vertices_241, vertices_961, vertices_286, vertices_902, vertices_346, vertices_540, vertices_692, vertices_468, vertices_120, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_259, vertices_515, vertices_41, vertices_521, vertices_97, vertices_161, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_262, vertices_518, vertices_282, vertices_74, vertices_322, vertices_770, vertices_28, vertices_524, vertices_148, vertices_276, vertices_532, vertices_388, vertices_644, vertices_56, vertices_88, vertices_536, vertices_104, vertices_552, vertices_112, vertices_176, vertices_560, vertices_208, vertices_336, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_107), (false, vertices_323), (false, vertices_771), (false, vertices_681), (false, vertices_241), (false, vertices_961), (true, vertices_262), (true, vertices_282), (true, vertices_28), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_388), (true, vertices_644), (true, vertices_56), (true, vertices_88), (true, vertices_536), (true, vertices_560), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 14 19 21 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 15 else
  if p.val = (false, vertices_107) then 17 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_282) then 18 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_336) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_282), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 7 282
cert_row_4 1 0 1 6 7 8 902 262 2
cert_row_4 2 1 3 4 6 8 692 148 2
cert_row_4 3 1 3 5 6 7 468 148 2
cert_rows
cert_pivot_2 2 0 4 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 14 286 3
cert_coverFacet 1 902
cert_cover_5 1 1 0 1 6 7 262 902 2
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 5 282 346 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 692
cert_cover_5 4 2 1 3 4 6 148 692 2
cert_coverFacet 5 468
cert_cover_5 5 3 1 3 5 6 148 468 2
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1196

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_1197.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1197

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 653, 405, 805, 841, 449, 310, 602, 666, 114, 402, 482, 628, 660, 864, 133, 261, 517, 73, 137, 521, 193, 321, 385, 769, 538, 74, 138, 50, 82, 146, 274, 98, 290, 194, 386, 52, 148, 276, 532, 292, 548, 644, 584, 648, 112, 592, 400, 656, 352, 608, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_653, vertices_405, vertices_805, vertices_841, vertices_449, vertices_310, vertices_602, vertices_666, vertices_114, vertices_402, vertices_482, vertices_628, vertices_660, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_193, vertices_321, vertices_385, vertices_769, vertices_538, vertices_74, vertices_138, vertices_50, vertices_82, vertices_146, vertices_274, vertices_98, vertices_290, vertices_194, vertices_386, vertices_52, vertices_148, vertices_276, vertices_532, vertices_292, vertices_548, vertices_644, vertices_584, vertices_648, vertices_112, vertices_592, vertices_400, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_653), (false, vertices_405), (false, vertices_805), (false, vertices_841), (false, vertices_449), (true, vertices_538), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_98), (true, vertices_290), (true, vertices_386), (true, vertices_52), (true, vertices_532), (true, vertices_112), (true, vertices_592), (true, vertices_656), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_841) then 23 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_538) then 17 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
cert_nodeAtPriority_51 449 50 82 146 274 98 290 386 52 532 112 592 656 352 608 203 538 653 405 805 841
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 8 538
cert_row_4 1 0 4 5 6 7 482 98 3
cert_row_4 2 0 1 3 4 7 310 50 1
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 2 0 1 3 4 50 310 1
cert_coverFacet 1 602
cert_cover_5 1 0 0 2 3 5 538 602 3
cert_coverFacet 2 666
cert_cover_5 2 0 0 2 3 6 538 666 3
cert_coverFacet 3 114
cert_cover_2 3 3 0 4 5 50 114 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 482
cert_cover_5 5 1 0 4 5 6 98 482 3
cert_coverFacet 6 628
cert_cover_5 6 3 1 3 4 5 52 628 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 864
cert_cover_2 8 5 4 7 8 352 864 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1197

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_1199.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1199

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 263, 331, 211, 357, 113, 689, 902, 202, 906, 820, 676, 376, 728, 792, 7, 67, 131, 259, 37, 261, 49, 81, 145, 97, 161, 321, 134, 262, 74, 138, 266, 194, 898, 164, 292, 548, 644, 772, 88, 280, 536, 200, 328, 648, 776, 112, 304, 560, 208, 656, 784, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_263, vertices_331, vertices_211, vertices_357, vertices_113, vertices_689, vertices_902, vertices_202, vertices_906, vertices_820, vertices_676, vertices_376, vertices_728, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_67, vertices_131, vertices_259, vertices_37, vertices_261, vertices_49, vertices_81, vertices_145, vertices_97, vertices_161, vertices_321, vertices_134, vertices_262, vertices_74, vertices_138, vertices_266, vertices_194, vertices_898, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_88, vertices_280, vertices_536, vertices_200, vertices_328, vertices_648, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_656, vertices_784, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_263), (false, vertices_331), (false, vertices_211), (false, vertices_357), (false, vertices_113), (false, vertices_689), (true, vertices_138), (true, vertices_898), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_200), (true, vertices_648), (true, vertices_776), (true, vertices_304), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 15 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_331) then 18 else
  if p.val = (false, vertices_211) then 19 else
  if p.val = (false, vertices_357) then 16 else
  if p.val = (false, vertices_113) then 1 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_898) then 20 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_784) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_167), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_898), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 6 7 8 898
cert_row_4 1 1 3 4 7 8 820 292 1
cert_row_4 2 2 3 4 5 7 376 88 2
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 134 902 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 906
cert_cover_5 2 0 0 2 6 7 138 906 3
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 292 820 1
cert_coverFacet 4 676
cert_cover_2 4 4 1 6 8 164 676 3
cert_coverFacet 5 376
cert_cover_5 5 2 2 3 4 5 88 376 2
cert_coverFacet 6 728
cert_cover_5 6 3 2 3 5 6 88 728 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1199

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_1200.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1200

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 309, 837, 645, 345, 113, 737, 654, 782, 294, 314, 154, 242, 728, 840, 37, 133, 261, 517, 49, 81, 273, 97, 161, 321, 577, 641, 526, 38, 134, 262, 26, 138, 266, 50, 146, 162, 290, 292, 644, 772, 88, 152, 280, 328, 584, 648, 776, 112, 304, 208, 224, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_309, vertices_837, vertices_645, vertices_345, vertices_113, vertices_737, vertices_654, vertices_782, vertices_294, vertices_314, vertices_154, vertices_242, vertices_728, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_517, vertices_49, vertices_81, vertices_273, vertices_97, vertices_161, vertices_321, vertices_577, vertices_641, vertices_526, vertices_38, vertices_134, vertices_262, vertices_26, vertices_138, vertices_266, vertices_50, vertices_146, vertices_162, vertices_290, vertices_292, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_328, vertices_584, vertices_648, vertices_776, vertices_112, vertices_304, vertices_208, vertices_224, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_309), (false, vertices_837), (false, vertices_645), (false, vertices_345), (false, vertices_113), (false, vertices_737), (true, vertices_526), (true, vertices_262), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_50), (true, vertices_146), (true, vertices_290), (true, vertices_152), (true, vertices_584), (true, vertices_648), (true, vertices_776), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 15 else
  if p.val = (false, vertices_309) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_113) then 1 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_526) then 16 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_50) then 6 else
  if p.val = (true, vertices_146) then 7 else
  if p.val = (true, vertices_290) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_208) then 13 else
  0
cert_priority
cert_nodeAtPriority_53 0 645 1 113 262 26 138 266 50 146 290 152 584 648 776 208 167 526 309 837 345 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 8 526
cert_row_4 1 0 2 3 4 7 314 26 3
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 526 654 3
cert_coverFacet 1 782
cert_cover_5 1 0 0 1 2 7 526 782 3
cert_coverFacet 2 294
cert_cover_2 2 1 0 4 7 38 294 3
cert_coverFacet 3 314
cert_cover_5 3 1 0 2 3 4 26 314 3
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 242
cert_cover_5 5 2 0 3 4 5 50 242 3
cert_coverFacet 6 728
cert_cover_5 6 3 2 3 5 6 88 728 3
cert_coverFacet 7 840
cert_cover_2 7 5 2 7 8 328 840 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1200

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_1201.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1201

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 557, 269, 341, 709, 361, 225, 542, 410, 426, 554, 722, 284, 596, 496, 13, 69, 261, 517, 41, 265, 97, 161, 545, 193, 321, 641, 26, 42, 394, 522, 146, 530, 162, 546, 642, 28, 268, 524, 84, 276, 532, 580, 280, 296, 552, 208, 336, 592, 400, 224, 352, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_557, vertices_269, vertices_341, vertices_709, vertices_361, vertices_225, vertices_542, vertices_410, vertices_426, vertices_554, vertices_722, vertices_284, vertices_596, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_517, vertices_41, vertices_265, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_641, vertices_26, vertices_42, vertices_394, vertices_522, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_28, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_580, vertices_280, vertices_296, vertices_552, vertices_208, vertices_336, vertices_592, vertices_400, vertices_224, vertices_352, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_557), (false, vertices_269), (false, vertices_341), (false, vertices_709), (false, vertices_361), (false, vertices_225), (true, vertices_26), (true, vertices_42), (true, vertices_394), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_532), (true, vertices_280), (true, vertices_208), (true, vertices_592), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_394) then 16 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 269 1 225 26 42 522 146 530 28 532 280 208 592 400 416 675 394 557 341 709 361
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 26 1
cert_row_2 1 0 2 6 7 394
cert_row_4 2 0 3 5 6 8 722 146 2
cert_row_4 3 3 4 5 6 7 496 208 1
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 26 542 1
cert_coverFacet 1 410
cert_cover_5 1 1 0 2 3 6 26 410 3
cert_coverFacet 2 426
cert_cover_5 2 1 0 2 4 6 42 426 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 722
cert_cover_5 4 2 0 3 5 6 146 722 2
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 208 496 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1201

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_1203.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1203

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 291, 451, 579, 301, 905, 721, 310, 342, 626, 556, 460, 652, 692, 212, 35, 67, 259, 515, 41, 265, 521, 289, 193, 577, 385, 641, 278, 50, 82, 290, 546, 322, 578, 44, 140, 268, 524, 52, 84, 148, 292, 548, 196, 324, 644, 552, 392, 648, 560, 208, 592, 656, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_291, vertices_451, vertices_579, vertices_301, vertices_905, vertices_721, vertices_310, vertices_342, vertices_626, vertices_556, vertices_460, vertices_652, vertices_692, vertices_212] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_259, vertices_515, vertices_41, vertices_265, vertices_521, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_278, vertices_50, vertices_82, vertices_290, vertices_546, vertices_322, vertices_578, vertices_44, vertices_140, vertices_268, vertices_524, vertices_52, vertices_84, vertices_148, vertices_292, vertices_548, vertices_196, vertices_324, vertices_644, vertices_552, vertices_392, vertices_648, vertices_560, vertices_208, vertices_592, vertices_656, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_291), (false, vertices_451), (false, vertices_579), (false, vertices_301), (false, vertices_905), (false, vertices_721), (true, vertices_278), (true, vertices_50), (true, vertices_82), (true, vertices_140), (true, vertices_524), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_548), (true, vertices_196), (true, vertices_324), (true, vertices_644), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 15 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_579) then 1 else
  if p.val = (false, vertices_301) then 19 else
  if p.val = (false, vertices_905) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_278) then 17 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_644) then 12 else
  if p.val = (true, vertices_560) then 13 else
  0
cert_priority
cert_nodeAtPriority_23 291 579 50 82 140 524 52 84 148 548 196 324 644 560 555 451 278 301 905 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 5 6 7 460 140 2
cert_row_2 1 0 1 3 7 278
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 1 0 1 3 4 278 310 3
cert_coverFacet 1 342
cert_cover_5 1 1 0 1 3 5 278 342 3
cert_coverFacet 2 626
cert_cover_5 2 2 0 3 4 5 50 626 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 460
cert_cover_5 4 0 1 2 5 6 140 460 2
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 52 692 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1203

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_1204.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1204

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 51, 419, 901, 569, 777, 737, 94, 334, 626, 354, 540, 780, 724, 484, 19, 35, 259, 25, 265, 521, 49, 161, 545, 385, 641, 769, 78, 26, 266, 50, 82, 98, 290, 322, 28, 268, 524, 84, 532, 196, 324, 388, 644, 772, 536, 776, 560, 592, 224, 352, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_51, vertices_419, vertices_901, vertices_569, vertices_777, vertices_737, vertices_94, vertices_334, vertices_626, vertices_354, vertices_540, vertices_780, vertices_724, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_25, vertices_265, vertices_521, vertices_49, vertices_161, vertices_545, vertices_385, vertices_641, vertices_769, vertices_78, vertices_26, vertices_266, vertices_50, vertices_82, vertices_98, vertices_290, vertices_322, vertices_28, vertices_268, vertices_524, vertices_84, vertices_532, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_536, vertices_776, vertices_560, vertices_592, vertices_224, vertices_352, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_51), (false, vertices_419), (false, vertices_901), (false, vertices_569), (false, vertices_777), (false, vertices_737), (true, vertices_78), (true, vertices_82), (true, vertices_98), (true, vertices_322), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_532), (true, vertices_196), (true, vertices_324), (true, vertices_592), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 15 else
  if p.val = (false, vertices_51) then 0 else
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
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
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 3 4 5 8 626 50 3
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 1 4 5 6 7 484 196 1
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 78 94 3
cert_coverFacet 1 334
cert_cover_5 1 0 0 1 2 7 78 334 3
cert_coverFacet 2 626
cert_cover_5 2 1 0 3 4 5 50 626 3
cert_coverFacet 3 354
cert_cover_2 3 4 0 5 7 98 354 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 724
cert_cover_5 6 2 1 3 5 6 84 724 3
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 196 484 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1204

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_1206.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1206

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 309, 425, 713, 777, 689, 118, 278, 454, 602, 458, 778, 740, 420, 624, 137, 265, 521, 49, 273, 529, 161, 289, 641, 769, 22, 70, 262, 74, 266, 522, 82, 274, 530, 450, 770, 52, 276, 100, 164, 292, 196, 388, 200, 584, 392, 776, 112, 560, 592, 608, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_309, vertices_425, vertices_713, vertices_777, vertices_689, vertices_118, vertices_278, vertices_454, vertices_602, vertices_458, vertices_778, vertices_740, vertices_420, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_49, vertices_273, vertices_529, vertices_161, vertices_289, vertices_641, vertices_769, vertices_22, vertices_70, vertices_262, vertices_74, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_450, vertices_770, vertices_52, vertices_276, vertices_100, vertices_164, vertices_292, vertices_196, vertices_388, vertices_200, vertices_584, vertices_392, vertices_776, vertices_112, vertices_560, vertices_592, vertices_608, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_309), (false, vertices_425), (false, vertices_713), (false, vertices_777), (false, vertices_689), (true, vertices_22), (true, vertices_70), (true, vertices_262), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_82), (true, vertices_450), (true, vertices_100), (true, vertices_164), (true, vertices_196), (true, vertices_388), (true, vertices_112), (true, vertices_592), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_309) then 19 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_82) then 7 else
  if p.val = (true, vertices_450) then 17 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 777 22 70 262 74 266 522 82 100 164 196 388 112 592 608 787 450 309 425 713 689
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 6 7 450
cert_row_4 1 0 2 3 5 8 602 74 2
cert_row_4 2 0 1 3 4 5 118 22 3
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 2 0 1 3 4 22 118 3
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 454
cert_cover_5 2 0 0 1 5 6 70 454 3
cert_coverFacet 3 602
cert_cover_5 3 1 0 2 3 5 74 602 2
cert_coverFacet 4 458
cert_cover_5 4 0 0 2 5 6 74 458 3
cert_coverFacet 5 778
cert_cover_2 5 2 0 7 8 266 778 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 100 740 3
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coverFacet 8 624
cert_cover_2 8 4 3 5 8 112 624 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1206

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_1207.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1207

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [15, 55, 75, 355, 589, 805, 961, 30, 186, 714, 226, 412, 908, 308, 496, 7, 11, 35, 67, 13, 37, 517, 73, 289, 321, 577, 769, 14, 22, 26, 74, 138, 50, 98, 162, 194, 28, 396, 524, 52, 276, 292, 772, 152, 584, 648, 176, 304, 400, 224, 352, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_15, vertices_55, vertices_75, vertices_355, vertices_589, vertices_805, vertices_961, vertices_30, vertices_186, vertices_714, vertices_226, vertices_412, vertices_908, vertices_308, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_35, vertices_67, vertices_13, vertices_37, vertices_517, vertices_73, vertices_289, vertices_321, vertices_577, vertices_769, vertices_14, vertices_22, vertices_26, vertices_74, vertices_138, vertices_50, vertices_98, vertices_162, vertices_194, vertices_28, vertices_396, vertices_524, vertices_52, vertices_276, vertices_292, vertices_772, vertices_152, vertices_584, vertices_648, vertices_176, vertices_304, vertices_400, vertices_224, vertices_352, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_15), (false, vertices_55), (false, vertices_75), (false, vertices_355), (false, vertices_589), (false, vertices_805), (false, vertices_961), (true, vertices_26), (true, vertices_138), (true, vertices_162), (true, vertices_194), (true, vertices_28), (true, vertices_396), (true, vertices_276), (true, vertices_152), (true, vertices_648), (true, vertices_176), (true, vertices_304), (true, vertices_400), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_15) then 0 else
  if p.val = (false, vertices_55) then 15 else
  if p.val = (false, vertices_75) then 1 else
  if p.val = (false, vertices_355) then 16 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_396) then 20 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_224) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_15), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_75), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
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
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 2 5 6 8 714 74 3
cert_row_4 2 0 2 3 4 6 186 26 3
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 1 8 0 3
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 186
cert_cover_5 1 2 0 2 3 4 26 186 3
cert_coverFacet 2 714
cert_cover_5 2 1 0 2 5 6 74 714 3
cert_coverFacet 3 226
cert_cover_2 3 4 0 5 6 98 226 3
cert_coverFacet 4 412
cert_cover_5 4 0 1 2 3 6 28 412 3
cert_coverFacet 5 908
cert_cover_5 5 0 1 2 6 8 396 908 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 176 496 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1207

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_1208.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1208

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [43, 587, 179, 531, 661, 361, 737, 790, 314, 778, 716, 332, 780, 244, 372, 11, 19, 35, 515, 41, 73, 145, 529, 97, 161, 577, 641, 42, 266, 522, 50, 274, 530, 770, 76, 268, 524, 116, 148, 276, 532, 196, 324, 644, 772, 296, 328, 584, 776, 176, 304, 224, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_43, vertices_587, vertices_179, vertices_531, vertices_661, vertices_361, vertices_737, vertices_790, vertices_314, vertices_778, vertices_716, vertices_332, vertices_780, vertices_244, vertices_372] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_35, vertices_515, vertices_41, vertices_73, vertices_145, vertices_529, vertices_97, vertices_161, vertices_577, vertices_641, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_770, vertices_76, vertices_268, vertices_524, vertices_116, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_644, vertices_772, vertices_296, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_224, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_43), (false, vertices_587), (false, vertices_179), (false, vertices_531), (false, vertices_661), (false, vertices_361), (false, vertices_737), (true, vertices_266), (true, vertices_274), (true, vertices_770), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_116), (true, vertices_276), (true, vertices_196), (true, vertices_324), (true, vertices_772), (true, vertices_776), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_43) then 0 else
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_179) then 16 else
  if p.val = (false, vertices_531) then 1 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_116) then 19 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_304) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_43), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_116), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_4 0 1 2 5 6 8 716 76 3
cert_row_2 1 1 3 4 5 116
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 0 2 3 4 7 314 42 2
cert_rows
cert_pivot_2 6 5 1 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 314
cert_cover_5 1 3 0 2 3 4 42 314 2
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 716
cert_cover_5 3 0 1 2 5 6 76 716 3
cert_coverFacet 4 332
cert_cover_2 4 2 1 5 7 76 332 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 244
cert_cover_5 6 1 1 3 4 6 116 244 3
cert_coverFacet 7 372
cert_cover_5 7 1 1 3 4 7 116 372 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1208

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_1209.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1209

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 523, 563, 397, 665, 241, 417, 334, 590, 482, 610, 652, 628, 468, 660, 11, 35, 515, 137, 265, 521, 49, 145, 529, 161, 289, 385, 78, 266, 522, 98, 290, 546, 322, 578, 140, 268, 524, 84, 148, 532, 324, 580, 388, 644, 648, 112, 560, 208, 656, 224, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_523, vertices_563, vertices_397, vertices_665, vertices_241, vertices_417, vertices_334, vertices_590, vertices_482, vertices_610, vertices_652, vertices_628, vertices_468, vertices_660] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_515, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_529, vertices_161, vertices_289, vertices_385, vertices_78, vertices_266, vertices_522, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_140, vertices_268, vertices_524, vertices_84, vertices_148, vertices_532, vertices_324, vertices_580, vertices_388, vertices_644, vertices_648, vertices_112, vertices_560, vertices_208, vertices_656, vertices_224, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_523), (false, vertices_563), (false, vertices_397), (false, vertices_665), (false, vertices_241), (false, vertices_417), (true, vertices_78), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_524), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_324), (true, vertices_580), (true, vertices_644), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 15 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_417) then 1 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
cert_nodeAtPriority_23 523 417 98 322 578 524 84 148 532 324 580 644 608 448 299 563 78 397 665 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 4 5 6 7 482 98 3
cert_row_4 2 1 3 4 5 8 628 84 2
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 2 0 4 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 7 78 334 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 482
cert_cover_5 2 1 0 4 5 6 98 482 3
cert_coverFacet 3 610
cert_cover_2 3 4 0 5 8 98 610 3
cert_coverFacet 4 652
cert_cover_2 4 2 1 6 8 140 652 3
cert_coverFacet 5 628
cert_cover_5 5 2 1 3 4 5 84 628 2
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 84 468 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1209

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_1210.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1210

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 651, 589, 361, 433, 737, 542, 270, 310, 722, 402, 108, 300, 244, 596, 139, 73, 265, 521, 97, 161, 289, 577, 385, 641, 14, 22, 262, 266, 522, 146, 274, 530, 386, 642, 44, 76, 268, 524, 52, 84, 532, 100, 292, 580, 104, 296, 176, 304, 208, 592, 400, 224, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_651, vertices_589, vertices_361, vertices_433, vertices_737, vertices_542, vertices_270, vertices_310, vertices_722, vertices_402, vertices_108, vertices_300, vertices_244, vertices_596] (by decide +kernel)
  polygons := literalFinset [vertices_139, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_641, vertices_14, vertices_22, vertices_262, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_44, vertices_76, vertices_268, vertices_524, vertices_52, vertices_84, vertices_532, vertices_100, vertices_292, vertices_580, vertices_104, vertices_296, vertices_176, vertices_304, vertices_208, vertices_592, vertices_400, vertices_224, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_651), (false, vertices_589), (false, vertices_361), (false, vertices_433), (false, vertices_737), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_44), (true, vertices_268), (true, vertices_52), (true, vertices_84), (true, vertices_532), (true, vertices_100), (true, vertices_292), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_651) then 17 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_292) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 14 3
cert_row_4 1 0 1 3 4 7 310 22 3
cert_row_4 2 0 3 5 6 8 722 146 2
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 14 542 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 310
cert_cover_5 2 1 0 1 3 4 22 310 3
cert_coverFacet 3 722
cert_cover_5 3 2 0 3 5 6 146 722 2
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 244
cert_cover_5 7 3 1 3 4 5 52 244 3
cert_coverFacet 8 596
cert_cover_2 8 3 1 5 8 84 596 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1210

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_1211.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1211

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 405, 217, 713, 369, 929, 590, 270, 422, 550, 346, 354, 156, 284, 684, 201, 81, 145, 273, 97, 289, 545, 577, 385, 641, 14, 38, 262, 518, 74, 266, 98, 290, 546, 322, 578, 28, 140, 268, 524, 148, 276, 164, 548, 388, 88, 152, 280, 584, 648, 336, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_405, vertices_217, vertices_713, vertices_369, vertices_929, vertices_590, vertices_270, vertices_422, vertices_550, vertices_346, vertices_354, vertices_156, vertices_284, vertices_684] (by decide +kernel)
  polygons := literalFinset [vertices_201, vertices_81, vertices_145, vertices_273, vertices_97, vertices_289, vertices_545, vertices_577, vertices_385, vertices_641, vertices_14, vertices_38, vertices_262, vertices_518, vertices_74, vertices_266, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_28, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_164, vertices_548, vertices_388, vertices_88, vertices_152, vertices_280, vertices_584, vertices_648, vertices_336, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_405), (false, vertices_217), (false, vertices_713), (false, vertices_369), (false, vertices_929), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_74), (true, vertices_266), (true, vertices_290), (true, vertices_322), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_164), (true, vertices_548), (true, vertices_280)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 19 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_217) then 20 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_164) then 12 else
  if p.val = (true, vertices_548) then 13 else
  if p.val = (true, vertices_280) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
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
cert_row_4 0 0 2 3 5 7 346 74 2
cert_row_4 1 0 1 2 5 8 590 14 3
cert_row_4 2 0 1 4 6 7 422 38 3
cert_row_4 3 1 2 4 6 8 684 140 2
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 14 590 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 422
cert_cover_5 2 2 0 1 4 6 38 422 3
cert_coverFacet 3 550
cert_cover_2 3 1 0 4 8 38 550 3
cert_coverFacet 4 346
cert_cover_5 4 0 0 2 3 5 74 346 2
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 156
cert_cover_2 6 2 1 3 6 28 156 3
cert_coverFacet 7 284
cert_cover_2 7 2 1 3 7 28 284 3
cert_coverFacet 8 684
cert_cover_5 8 3 1 2 4 6 140 684 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1211

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_1212.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1212

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [15, 103, 75, 653, 181, 841, 737, 782, 54, 790, 362, 434, 660, 976, 480, 7, 11, 67, 13, 37, 133, 73, 521, 97, 161, 577, 641, 14, 22, 38, 774, 74, 266, 50, 274, 98, 290, 524, 52, 148, 532, 644, 328, 776, 176, 400, 656, 784, 224, 352, 416, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_15, vertices_103, vertices_75, vertices_653, vertices_181, vertices_841, vertices_737, vertices_782, vertices_54, vertices_790, vertices_362, vertices_434, vertices_660, vertices_976, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_37, vertices_133, vertices_73, vertices_521, vertices_97, vertices_161, vertices_577, vertices_641, vertices_14, vertices_22, vertices_38, vertices_774, vertices_74, vertices_266, vertices_50, vertices_274, vertices_98, vertices_290, vertices_524, vertices_52, vertices_148, vertices_532, vertices_644, vertices_328, vertices_776, vertices_176, vertices_400, vertices_656, vertices_784, vertices_224, vertices_352, vertices_416, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_15), (false, vertices_103), (false, vertices_75), (false, vertices_653), (false, vertices_181), (false, vertices_841), (false, vertices_737), (true, vertices_22), (true, vertices_774), (true, vertices_266), (true, vertices_50), (true, vertices_274), (true, vertices_290), (true, vertices_532), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_352), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_15) then 0 else
  if p.val = (false, vertices_103) then 15 else
  if p.val = (false, vertices_75) then 1 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_774) then 16 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
cert_nodeAtPriority_53 0 15 1 75 22 266 50 274 290 532 400 656 784 352 416 448 103 774 653 181 841 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 0 2 4 5 7 362 74 2
cert_row_4 2 0 3 4 6 7 434 50 3
cert_row_4 3 3 5 6 7 8 976 400 1
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 54
cert_cover_2 1 1 0 3 4 22 54 3
cert_coverFacet 2 790
cert_cover_5 2 0 0 1 3 7 22 790 3
cert_coverFacet 3 362
cert_cover_5 3 1 0 2 4 5 74 362 2
cert_coverFacet 4 434
cert_cover_5 4 2 0 3 4 6 50 434 3
cert_coverFacet 5 660
cert_cover_2 5 3 1 6 8 148 660 3
cert_coverFacet 6 976
cert_cover_5 6 3 3 5 6 7 400 976 1
cert_coverFacet 7 480
cert_cover_2 7 5 4 6 7 224 480 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1212

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_1213.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1213

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 285, 597, 773, 465, 737, 62, 270, 678, 774, 362, 482, 564, 632, 344, 21, 261, 517, 81, 273, 193, 577, 385, 641, 769, 14, 38, 262, 518, 42, 266, 354, 162, 386, 642, 770, 28, 268, 52, 532, 548, 772, 56, 88, 280, 104, 328, 560, 336, 592, 224, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_285, vertices_597, vertices_773, vertices_465, vertices_737, vertices_62, vertices_270, vertices_678, vertices_774, vertices_362, vertices_482, vertices_564, vertices_632, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_261, vertices_517, vertices_81, vertices_273, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_38, vertices_262, vertices_518, vertices_42, vertices_266, vertices_354, vertices_162, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_52, vertices_532, vertices_548, vertices_772, vertices_56, vertices_88, vertices_280, vertices_104, vertices_328, vertices_560, vertices_336, vertices_592, vertices_224, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_285), (false, vertices_597), (false, vertices_773), (false, vertices_465), (false, vertices_737), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_42), (true, vertices_266), (true, vertices_354), (true, vertices_162), (true, vertices_52), (true, vertices_548), (true, vertices_56), (true, vertices_88), (true, vertices_104), (true, vertices_328), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_285) then 19 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_354) then 17 else
  if p.val = (true, vertices_162) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_560) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_354), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 5 7 354
cert_row_4 1 0 1 4 6 8 678 38 3
cert_row_4 2 0 1 2 3 4 62 14 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 7 6 0 2
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 2 0 1 2 3 14 62 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 678
cert_cover_5 2 1 0 1 4 6 38 678 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 362
cert_cover_5 4 0 0 2 4 5 42 362 3
cert_coverFacet 5 482
cert_cover_5 5 0 0 4 5 6 354 482 3
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 632
cert_cover_5 7 3 2 3 4 5 56 632 3
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1213

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_1214.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1214

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [27, 555, 659, 709, 313, 241, 609, 398, 654, 282, 466, 620, 300, 372, 452, 11, 19, 515, 25, 41, 49, 145, 97, 545, 193, 577, 641, 142, 26, 266, 522, 146, 274, 386, 642, 44, 268, 524, 100, 292, 196, 324, 580, 388, 644, 280, 296, 552, 112, 304, 208, 336, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_27, vertices_555, vertices_659, vertices_709, vertices_313, vertices_241, vertices_609, vertices_398, vertices_654, vertices_282, vertices_466, vertices_620, vertices_300, vertices_372, vertices_452] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_515, vertices_25, vertices_41, vertices_49, vertices_145, vertices_97, vertices_545, vertices_193, vertices_577, vertices_641, vertices_142, vertices_26, vertices_266, vertices_522, vertices_146, vertices_274, vertices_386, vertices_642, vertices_44, vertices_268, vertices_524, vertices_100, vertices_292, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_280, vertices_296, vertices_552, vertices_112, vertices_304, vertices_208, vertices_336, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_27), (false, vertices_555), (false, vertices_659), (false, vertices_709), (false, vertices_313), (false, vertices_241), (false, vertices_609), (true, vertices_142), (true, vertices_266), (true, vertices_274), (true, vertices_386), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_100), (true, vertices_292), (true, vertices_324), (true, vertices_388), (true, vertices_336), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_27) then 0 else
  if p.val = (false, vertices_555) then 15 else
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_609) then 1 else
  if p.val = (true, vertices_142) then 17 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
cert_nodeAtPriority_23 27 609 266 274 386 44 268 524 100 292 324 388 336 448 555 659 142 709 313 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 5 8 620 44 3
cert_row_2 1 0 1 2 6 142
cert_row_4 2 0 3 5 6 7 466 146 2
cert_row_4 3 1 3 4 5 7 372 100 1
cert_rows
cert_pivot_2 8 2 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 7 142 398 3
cert_coverFacet 1 654
cert_cover_5 1 1 0 1 2 8 142 654 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 466
cert_cover_5 3 2 0 3 5 6 146 466 2
cert_coverFacet 4 620
cert_cover_5 4 0 1 2 4 5 44 620 3
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 372
cert_cover_5 6 3 1 3 4 5 100 372 1
cert_coverFacet 7 452
cert_cover_2 7 5 1 6 7 196 452 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1214

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_1215.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1215

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 583, 651, 403, 617, 457, 310, 534, 658, 572, 484, 612, 248, 664, 432, 71, 131, 259, 515, 73, 137, 521, 321, 577, 385, 22, 262, 518, 146, 274, 530, 642, 52, 532, 100, 292, 548, 324, 580, 56, 152, 536, 104, 552, 200, 648, 176, 304, 400, 656, 224, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_583, vertices_651, vertices_403, vertices_617, vertices_457, vertices_310, vertices_534, vertices_658, vertices_572, vertices_484, vertices_612, vertices_248, vertices_664, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_71, vertices_131, vertices_259, vertices_515, vertices_73, vertices_137, vertices_521, vertices_321, vertices_577, vertices_385, vertices_22, vertices_262, vertices_518, vertices_146, vertices_274, vertices_530, vertices_642, vertices_52, vertices_532, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_56, vertices_152, vertices_536, vertices_104, vertices_552, vertices_200, vertices_648, vertices_176, vertices_304, vertices_400, vertices_656, vertices_224, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_583), (false, vertices_651), (false, vertices_403), (false, vertices_617), (false, vertices_457), (true, vertices_22), (true, vertices_530), (true, vertices_52), (true, vertices_532), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_176), (true, vertices_304), (true, vertices_656), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 15 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 16 else
  if p.val = (false, vertices_583) then 17 else
  if p.val = (false, vertices_651) then 19 else
  if p.val = (false, vertices_403) then 20 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 22 3
cert_row_4 1 1 2 3 4 8 572 52 1
cert_row_4 2 1 4 5 6 7 484 100 3
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 22 310 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 658
cert_cover_2 2 3 0 6 8 146 658 3
cert_coverFacet 3 572
cert_cover_5 3 1 1 2 3 4 52 572 1
cert_coverFacet 4 484
cert_cover_5 4 2 1 4 5 6 100 484 3
cert_coverFacet 5 612
cert_cover_2 5 4 1 5 8 100 612 3
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 56 248 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1215

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_1216.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1216

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 149, 789, 229, 409, 609, 961, 46, 526, 794, 234, 458, 866, 188, 540, 21, 37, 133, 517, 145, 273, 97, 545, 193, 577, 385, 769, 14, 38, 518, 42, 202, 266, 522, 98, 546, 322, 770, 28, 44, 524, 148, 532, 164, 152, 280, 536, 168, 392, 784, 224, 608, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_149, vertices_789, vertices_229, vertices_409, vertices_609, vertices_961, vertices_46, vertices_526, vertices_794, vertices_234, vertices_458, vertices_866, vertices_188, vertices_540] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_133, vertices_517, vertices_145, vertices_273, vertices_97, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_38, vertices_518, vertices_42, vertices_202, vertices_266, vertices_522, vertices_98, vertices_546, vertices_322, vertices_770, vertices_28, vertices_44, vertices_524, vertices_148, vertices_532, vertices_164, vertices_152, vertices_280, vertices_536, vertices_168, vertices_392, vertices_784, vertices_224, vertices_608, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_149), (false, vertices_789), (false, vertices_229), (false, vertices_409), (false, vertices_609), (false, vertices_961), (true, vertices_14), (true, vertices_42), (true, vertices_202), (true, vertices_266), (true, vertices_522), (true, vertices_98), (true, vertices_322), (true, vertices_770), (true, vertices_28), (true, vertices_44), (true, vertices_524), (true, vertices_536), (true, vertices_168)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 15 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_609) then 1 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_202) then 16 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_44) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_168) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_609), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
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
cert_row_4 0 1 2 3 4 6 188 28 3
cert_row_2 1 0 2 5 6 202
cert_row_4 2 0 2 3 7 8 794 266 2
cert_row_4 3 0 4 5 7 8 866 98 3
cert_rows
cert_pivot_2 1 6 2 0
cert_heightProof 4
cert_coverFacet 0 46
cert_cover_2 0 1 0 2 4 14 46 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 794
cert_cover_5 2 2 0 2 3 7 266 794 2
cert_coverFacet 3 234
cert_cover_5 3 1 0 2 4 5 42 234 3
cert_coverFacet 4 458
cert_cover_5 4 1 0 2 5 7 202 458 3
cert_coverFacet 5 866
cert_cover_5 5 3 0 4 5 7 98 866 3
cert_coverFacet 6 188
cert_cover_5 6 0 1 2 3 4 28 188 3
cert_coverFacet 7 540
cert_cover_2 7 2 1 3 8 28 540 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1216

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_1217.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1217

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [15, 583, 779, 205, 409, 737, 897, 286, 310, 550, 930, 124, 612, 216, 496, 7, 11, 515, 13, 69, 137, 265, 193, 577, 385, 641, 769, 14, 278, 38, 518, 266, 290, 546, 770, 28, 76, 52, 100, 548, 580, 88, 152, 280, 200, 112, 304, 208, 400, 224, 608, 416, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_15, vertices_583, vertices_779, vertices_205, vertices_409, vertices_737, vertices_897, vertices_286, vertices_310, vertices_550, vertices_930, vertices_124, vertices_612, vertices_216, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_13, vertices_69, vertices_137, vertices_265, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_278, vertices_38, vertices_518, vertices_266, vertices_290, vertices_546, vertices_770, vertices_28, vertices_76, vertices_52, vertices_100, vertices_548, vertices_580, vertices_88, vertices_152, vertices_280, vertices_200, vertices_112, vertices_304, vertices_208, vertices_400, vertices_224, vertices_608, vertices_416, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_15), (false, vertices_583), (false, vertices_779), (false, vertices_205), (false, vertices_409), (false, vertices_737), (false, vertices_897), (true, vertices_278), (true, vertices_38), (true, vertices_290), (true, vertices_546), (true, vertices_28), (true, vertices_52), (true, vertices_100), (true, vertices_548), (true, vertices_88), (true, vertices_112), (true, vertices_304), (true, vertices_208), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_15) then 0 else
  if p.val = (false, vertices_583) then 15 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_205) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_278) then 17 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_112) then 10 else
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
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_278), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
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
cert_row_4 2 1 2 3 4 5 124 28 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 8 0 1 3
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 1 0 1 2 3 14 286 3
cert_coverFacet 1 310
cert_cover_5 1 1 0 1 3 4 278 310 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 930
cert_cover_5 3 0 0 4 6 7 290 930 2
cert_coverFacet 4 124
cert_cover_5 4 2 1 2 3 4 28 124 3
cert_coverFacet 5 612
cert_cover_2 5 4 1 5 8 100 612 3
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1217

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_1218.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1218

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 283, 333, 233, 369, 689, 270, 526, 806, 714, 914, 588, 740, 356, 816, 27, 73, 137, 265, 49, 145, 273, 97, 161, 321, 14, 262, 518, 138, 266, 522, 146, 274, 642, 770, 76, 268, 524, 100, 292, 548, 324, 580, 200, 584, 304, 560, 656, 784, 224, 352, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_283, vertices_333, vertices_233, vertices_369, vertices_689, vertices_270, vertices_526, vertices_806, vertices_714, vertices_914, vertices_588, vertices_740, vertices_356, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_73, vertices_137, vertices_265, vertices_49, vertices_145, vertices_273, vertices_97, vertices_161, vertices_321, vertices_14, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_642, vertices_770, vertices_76, vertices_268, vertices_524, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_200, vertices_584, vertices_304, vertices_560, vertices_656, vertices_784, vertices_224, vertices_352, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_283), (false, vertices_333), (false, vertices_233), (false, vertices_369), (false, vertices_689), (true, vertices_14), (true, vertices_262), (true, vertices_518), (true, vertices_522), (true, vertices_642), (true, vertices_770), (true, vertices_524), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_580), (true, vertices_584), (true, vertices_784), (true, vertices_800), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 16 else
  if p.val = (false, vertices_283) then 17 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_800) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 138 2
cert_row_4 1 0 3 6 7 8 914 146 3
cert_row_4 2 0 1 4 7 8 806 262 2
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 806
cert_cover_5 2 2 0 1 4 7 262 806 2
cert_coverFacet 3 714
cert_cover_5 3 0 0 2 5 6 138 714 2
cert_coverFacet 4 914
cert_cover_5 4 1 0 3 6 7 146 914 3
cert_coverFacet 5 588
cert_cover_2 5 2 1 5 8 76 588 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 100 740 3
cert_coverFacet 7 356
cert_cover_2 7 4 1 5 7 100 356 3
cert_coverFacet 8 816
cert_cover_2 8 4 3 7 8 304 816 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1218

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_1219.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1219

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 279, 779, 611, 241, 849, 654, 270, 550, 460, 436, 676, 744, 840, 464, 23, 35, 259, 515, 49, 81, 273, 97, 577, 769, 14, 38, 262, 518, 266, 522, 546, 140, 268, 52, 276, 164, 548, 388, 644, 200, 328, 584, 648, 776, 176, 208, 336, 400, 224, 608, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_279, vertices_779, vertices_611, vertices_241, vertices_849, vertices_654, vertices_270, vertices_550, vertices_460, vertices_436, vertices_676, vertices_744, vertices_840, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_35, vertices_259, vertices_515, vertices_49, vertices_81, vertices_273, vertices_97, vertices_577, vertices_769, vertices_14, vertices_38, vertices_262, vertices_518, vertices_266, vertices_522, vertices_546, vertices_140, vertices_268, vertices_52, vertices_276, vertices_164, vertices_548, vertices_388, vertices_644, vertices_200, vertices_328, vertices_584, vertices_648, vertices_776, vertices_176, vertices_208, vertices_336, vertices_400, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_279), (false, vertices_779), (false, vertices_611), (false, vertices_241), (false, vertices_849), (true, vertices_14), (true, vertices_518), (true, vertices_140), (true, vertices_268), (true, vertices_164), (true, vertices_548), (true, vertices_388), (true, vertices_644), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_648), (true, vertices_400), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 15 21 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 16 else
  if p.val = (false, vertices_279) then 17 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_611) then 20 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 1 3 4 6 7 436 52 3
cert_row_4 2 1 2 5 6 7 460 140 2
cert_row_4 3 2 4 5 6 8 744 200 1
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 460
cert_cover_5 3 2 1 2 5 6 140 460 2
cert_coverFacet 4 436
cert_cover_5 4 1 1 3 4 6 52 436 3
cert_coverFacet 5 676
cert_cover_2 5 4 1 6 8 164 676 3
cert_coverFacet 6 744
cert_cover_5 6 3 2 4 5 6 200 744 1
cert_coverFacet 7 840
cert_cover_2 7 5 2 7 8 328 840 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1219

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_1220.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1220

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 99, 675, 387, 397, 713, 625, 182, 406, 370, 684, 780, 564, 852, 840, 35, 67, 131, 259, 73, 137, 265, 97, 545, 577, 385, 641, 150, 50, 274, 98, 162, 322, 386, 140, 268, 524, 52, 276, 532, 164, 548, 388, 772, 328, 584, 648, 776, 112, 560, 336, 592, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_99, vertices_675, vertices_387, vertices_397, vertices_713, vertices_625, vertices_182, vertices_406, vertices_370, vertices_684, vertices_780, vertices_564, vertices_852, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_131, vertices_259, vertices_73, vertices_137, vertices_265, vertices_97, vertices_545, vertices_577, vertices_385, vertices_641, vertices_150, vertices_50, vertices_274, vertices_98, vertices_162, vertices_322, vertices_386, vertices_140, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_164, vertices_548, vertices_388, vertices_772, vertices_328, vertices_584, vertices_648, vertices_776, vertices_112, vertices_560, vertices_336, vertices_592, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_99), (false, vertices_675), (false, vertices_387), (false, vertices_397), (false, vertices_713), (false, vertices_625), (true, vertices_150), (true, vertices_50), (true, vertices_274), (true, vertices_524), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_548), (true, vertices_772), (true, vertices_776), (true, vertices_336), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_99) then 0 else
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (true, vertices_150) then 17 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
cert_nodeAtPriority_23 99 387 50 274 524 52 276 532 164 548 772 776 336 832 331 675 150 397 713 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 6 8 684 140 2
cert_row_2 1 0 1 3 6 150
cert_row_4 2 0 3 4 5 7 370 50 3
cert_row_4 3 1 3 5 7 8 852 276 2
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 1 0 1 3 4 150 182 3
cert_coverFacet 1 406
cert_cover_5 1 1 0 1 3 7 150 406 3
cert_coverFacet 2 370
cert_cover_5 2 2 0 3 4 5 50 370 3
cert_coverFacet 3 684
cert_cover_5 3 0 1 2 4 6 140 684 2
cert_coverFacet 4 780
cert_cover_2 4 2 1 7 8 268 780 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 852
cert_cover_5 6 3 1 3 5 7 276 852 2
cert_coverFacet 7 840
cert_cover_2 7 5 2 7 8 328 840 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1220

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_1221.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1221

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [211, 29, 525, 597, 409, 809, 961, 158, 174, 566, 594, 226, 866, 556, 488, 13, 21, 517, 25, 265, 521, 81, 145, 193, 577, 385, 769, 142, 22, 38, 82, 146, 530, 98, 162, 546, 194, 578, 28, 44, 524, 532, 548, 152, 168, 296, 552, 392, 592, 224, 352, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_29, vertices_525, vertices_597, vertices_409, vertices_809, vertices_961, vertices_158, vertices_174, vertices_566, vertices_594, vertices_226, vertices_866, vertices_556, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_517, vertices_25, vertices_265, vertices_521, vertices_81, vertices_145, vertices_193, vertices_577, vertices_385, vertices_769, vertices_142, vertices_22, vertices_38, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_28, vertices_44, vertices_524, vertices_532, vertices_548, vertices_152, vertices_168, vertices_296, vertices_552, vertices_392, vertices_592, vertices_224, vertices_352, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_29), (false, vertices_525), (false, vertices_597), (false, vertices_409), (false, vertices_809), (false, vertices_961), (true, vertices_142), (true, vertices_22), (true, vertices_38), (true, vertices_530), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_578), (true, vertices_44), (true, vertices_548), (true, vertices_168), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 22 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 15 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_142) then 16 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_38) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_29), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_142), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
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
cert_row_4 0 0 1 3 4 8 566 22 3
cert_row_2 1 0 1 2 6 142
cert_row_4 2 0 4 5 7 8 866 98 3
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 142 158 3
cert_coverFacet 1 174
cert_cover_5 1 1 0 1 2 4 142 174 3
cert_coverFacet 2 566
cert_cover_5 2 0 0 1 3 4 22 566 3
cert_coverFacet 3 594
cert_cover_2 3 3 0 5 8 82 594 3
cert_coverFacet 4 226
cert_cover_2 4 4 0 5 6 98 226 3
cert_coverFacet 5 866
cert_cover_5 5 2 0 4 5 7 98 866 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 168 488 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1221

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_1222.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1222

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 661, 837, 389, 425, 817, 206, 710, 122, 170, 850, 658, 364, 396, 368, 133, 261, 517, 49, 145, 529, 161, 289, 385, 769, 198, 42, 74, 138, 50, 82, 146, 530, 162, 578, 642, 76, 140, 268, 324, 580, 388, 644, 104, 168, 296, 392, 112, 304, 336, 656, 784, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_661, vertices_837, vertices_389, vertices_425, vertices_817, vertices_206, vertices_710, vertices_122, vertices_170, vertices_850, vertices_658, vertices_364, vertices_396, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_49, vertices_145, vertices_529, vertices_161, vertices_289, vertices_385, vertices_769, vertices_198, vertices_42, vertices_74, vertices_138, vertices_50, vertices_82, vertices_146, vertices_530, vertices_162, vertices_578, vertices_642, vertices_76, vertices_140, vertices_268, vertices_324, vertices_580, vertices_388, vertices_644, vertices_104, vertices_168, vertices_296, vertices_392, vertices_112, vertices_304, vertices_336, vertices_656, vertices_784, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_661), (false, vertices_837), (false, vertices_389), (false, vertices_425), (false, vertices_817), (true, vertices_198), (true, vertices_42), (true, vertices_74), (true, vertices_138), (true, vertices_82), (true, vertices_530), (true, vertices_578), (true, vertices_642), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_104), (true, vertices_112), (true, vertices_336), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 16 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_198) then 17 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 389 42 74 138 82 530 578 642 76 140 268 104 112 336 352 179 198 661 837 425 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_4 1 0 3 5 7 8 850 82 3
cert_row_4 2 0 2 3 4 5 122 42 2
cert_row_4 3 1 2 4 5 7 364 76 2
cert_rows
cert_pivot_2 6 8 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 198 206 2
cert_coverFacet 1 710
cert_cover_5 1 0 0 1 5 8 198 710 3
cert_coverFacet 2 122
cert_cover_5 2 2 0 2 3 4 42 122 2
cert_coverFacet 3 170
cert_cover_2 3 2 0 4 6 42 170 3
cert_coverFacet 4 850
cert_cover_5 4 1 0 3 5 7 82 850 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 364
cert_cover_5 6 3 1 2 4 5 76 364 2
cert_coverFacet 7 396
cert_cover_2 7 2 1 6 7 140 396 3
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1222

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_1223.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1223

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 651, 453, 569, 361, 737, 62, 270, 406, 538, 722, 300, 628, 212, 356, 139, 41, 265, 521, 97, 545, 193, 321, 385, 641, 14, 22, 262, 26, 266, 522, 146, 530, 386, 642, 44, 268, 52, 84, 148, 100, 292, 196, 324, 388, 56, 536, 296, 560, 208, 592, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_651, vertices_453, vertices_569, vertices_361, vertices_737, vertices_62, vertices_270, vertices_406, vertices_538, vertices_722, vertices_300, vertices_628, vertices_212, vertices_356] (by decide +kernel)
  polygons := literalFinset [vertices_139, vertices_41, vertices_265, vertices_521, vertices_97, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_14, vertices_22, vertices_262, vertices_26, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_642, vertices_44, vertices_268, vertices_52, vertices_84, vertices_148, vertices_100, vertices_292, vertices_196, vertices_324, vertices_388, vertices_56, vertices_536, vertices_296, vertices_560, vertices_208, vertices_592, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_651), (false, vertices_453), (false, vertices_569), (false, vertices_361), (false, vertices_737), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_26), (true, vertices_146), (true, vertices_530), (true, vertices_44), (true, vertices_268), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_100), (true, vertices_292), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_651) then 17 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_292) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_4 0 0 1 2 3 4 62 14 3
cert_row_4 1 0 1 3 6 7 406 22 3
cert_row_4 2 0 3 5 6 8 722 146 2
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 14 62 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 406
cert_cover_5 2 1 0 1 3 6 22 406 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 722
cert_cover_5 4 2 0 3 5 6 146 722 2
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 628
cert_cover_5 6 3 1 3 4 5 52 628 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coverFacet 8 356
cert_cover_2 8 4 1 5 7 100 356 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1223

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_1224.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1224

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 653, 341, 597, 421, 737, 406, 346, 154, 106, 682, 418, 156, 540, 632, 85, 133, 261, 517, 97, 161, 289, 321, 577, 641, 26, 42, 74, 138, 146, 274, 98, 162, 290, 322, 386, 28, 140, 524, 148, 276, 532, 388, 88, 152, 536, 104, 552, 648, 336, 592, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_653, vertices_341, vertices_597, vertices_421, vertices_737, vertices_406, vertices_346, vertices_154, vertices_106, vertices_682, vertices_418, vertices_156, vertices_540, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_85, vertices_133, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_321, vertices_577, vertices_641, vertices_26, vertices_42, vertices_74, vertices_138, vertices_146, vertices_274, vertices_98, vertices_162, vertices_290, vertices_322, vertices_386, vertices_28, vertices_140, vertices_524, vertices_148, vertices_276, vertices_532, vertices_388, vertices_88, vertices_152, vertices_536, vertices_104, vertices_552, vertices_648, vertices_336, vertices_592, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_653), (false, vertices_341), (false, vertices_597), (false, vertices_421), (false, vertices_737), (true, vertices_26), (true, vertices_42), (true, vertices_74), (true, vertices_138), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_386), (true, vertices_28), (true, vertices_148), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_104), (true, vertices_552)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 17 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 16 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_341) then 20 else
  if p.val = (false, vertices_597) then 21 else
  if p.val = (false, vertices_421) then 22 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_104) then 13 else
  if p.val = (true, vertices_552) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
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
cert_row_4 0 0 1 3 6 7 406 146 1
cert_row_4 1 0 2 3 5 7 346 26 3
cert_row_4 2 0 2 4 6 8 682 42 3
cert_row_4 3 2 3 4 5 8 632 88 2
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 146 406 1
cert_coverFacet 1 346
cert_cover_5 1 1 0 2 3 5 26 346 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 106
cert_cover_2 3 2 0 4 5 42 106 3
cert_coverFacet 4 682
cert_cover_5 4 2 0 2 4 6 42 682 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 156
cert_cover_2 6 2 1 3 6 28 156 3
cert_coverFacet 7 540
cert_cover_2 7 2 1 3 8 28 540 3
cert_coverFacet 8 632
cert_cover_5 8 3 2 3 4 5 88 632 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1224

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_1225.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1225

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [59, 541, 269, 709, 325, 361, 625, 398, 654, 538, 298, 434, 722, 484, 240, 13, 69, 261, 517, 25, 41, 265, 49, 529, 97, 321, 577, 142, 26, 42, 266, 522, 50, 146, 530, 290, 386, 642, 268, 524, 196, 324, 388, 644, 536, 296, 112, 176, 208, 592, 224, 352, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_59, vertices_541, vertices_269, vertices_709, vertices_325, vertices_361, vertices_625, vertices_398, vertices_654, vertices_538, vertices_298, vertices_434, vertices_722, vertices_484, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_517, vertices_25, vertices_41, vertices_265, vertices_49, vertices_529, vertices_97, vertices_321, vertices_577, vertices_142, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_146, vertices_530, vertices_290, vertices_386, vertices_642, vertices_268, vertices_524, vertices_196, vertices_324, vertices_388, vertices_644, vertices_536, vertices_296, vertices_112, vertices_176, vertices_208, vertices_592, vertices_224, vertices_352, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_59), (false, vertices_541), (false, vertices_269), (false, vertices_709), (false, vertices_325), (false, vertices_361), (false, vertices_625), (true, vertices_142), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_290), (true, vertices_386), (true, vertices_642), (true, vertices_388), (true, vertices_176), (true, vertices_208), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_59) then 15 else
  if p.val = (false, vertices_541) then 18 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_325) then 1 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (true, vertices_142) then 16 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 269 1 325 266 522 146 530 290 386 642 388 176 208 224 416 59 142 541 709 361 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 6 142
cert_row_4 1 0 3 5 6 8 722 146 2
cert_row_4 2 0 3 4 6 7 434 50 3
cert_row_4 3 1 4 5 6 7 484 196 1
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 7 142 398 3
cert_coverFacet 1 654
cert_cover_5 1 0 0 1 2 8 142 654 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 434
cert_cover_5 4 2 0 3 4 6 50 434 3
cert_coverFacet 5 722
cert_cover_5 5 1 0 3 5 6 146 722 2
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 196 484 1
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1225

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_1226.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1226

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 405, 677, 837, 809, 393, 214, 710, 122, 154, 866, 674, 348, 408, 360, 133, 261, 517, 41, 137, 265, 161, 545, 385, 769, 198, 26, 42, 138, 82, 146, 98, 162, 546, 578, 642, 84, 148, 276, 324, 580, 644, 88, 152, 280, 104, 296, 328, 392, 400, 352, 672, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_405, vertices_677, vertices_837, vertices_809, vertices_393, vertices_214, vertices_710, vertices_122, vertices_154, vertices_866, vertices_674, vertices_348, vertices_408, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_137, vertices_265, vertices_161, vertices_545, vertices_385, vertices_769, vertices_198, vertices_26, vertices_42, vertices_138, vertices_82, vertices_146, vertices_98, vertices_162, vertices_546, vertices_578, vertices_642, vertices_84, vertices_148, vertices_276, vertices_324, vertices_580, vertices_644, vertices_88, vertices_152, vertices_280, vertices_104, vertices_296, vertices_328, vertices_392, vertices_400, vertices_352, vertices_672, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_405), (false, vertices_677), (false, vertices_837), (false, vertices_809), (false, vertices_393), (true, vertices_198), (true, vertices_26), (true, vertices_82), (true, vertices_146), (true, vertices_98), (true, vertices_546), (true, vertices_578), (true, vertices_642), (true, vertices_84), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_104), (true, vertices_328), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 16 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_809) then 23 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (true, vertices_198) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
cert_nodeAtPriority_51 393 26 82 146 98 546 578 642 84 88 152 280 104 328 352 171 198 405 677 837 809
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_4 1 0 4 5 7 8 866 98 3
cert_row_4 2 0 2 3 4 5 122 26 3
cert_row_4 3 1 2 3 5 7 348 84 1
cert_rows
cert_pivot_2 6 8 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 198 214 2
cert_coverFacet 1 710
cert_cover_5 1 0 0 1 5 8 198 710 3
cert_coverFacet 2 122
cert_cover_5 2 2 0 2 3 4 26 122 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 866
cert_cover_5 4 1 0 4 5 7 98 866 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 348
cert_cover_5 6 3 1 2 3 5 84 348 1
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1226

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3753 : Certifies 3753 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1194.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3754 : Certifies 3754 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1195.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3755 : Certifies 3755 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1196.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3756 : Certifies 3756 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1197.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3757 : Certifies 3757 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1199.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3758 : Certifies 3758 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1200.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3759 : Certifies 3759 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1201.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3760 : Certifies 3760 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1203.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3761 : Certifies 3761 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1204.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3762 : Certifies 3762 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1206.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3763 : Certifies 3763 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1207.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3764 : Certifies 3764 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1208.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3765 : Certifies 3765 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1209.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3766 : Certifies 3766 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1210.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3767 : Certifies 3767 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1211.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3768 : Certifies 3768 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1212.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3769 : Certifies 3769 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1213.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3770 : Certifies 3770 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1214.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3771 : Certifies 3771 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1215.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3772 : Certifies 3772 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1216.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3773 : Certifies 3773 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1217.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3774 : Certifies 3774 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1218.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3775 : Certifies 3775 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1219.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3776 : Certifies 3776 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1220.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3777 : Certifies 3777 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1221.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3778 : Certifies 3778 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1222.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3779 : Certifies 3779 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1223.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3780 : Certifies 3780 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1224.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3781 : Certifies 3781 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1225.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3782 : Certifies 3782 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1226.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B124 (j : Fin 30) :
    Certifies (3753 + j.val) := by
  fin_cases j
  · exact projection_3753
  · exact projection_3754
  · exact projection_3755
  · exact projection_3756
  · exact projection_3757
  · exact projection_3758
  · exact projection_3759
  · exact projection_3760
  · exact projection_3761
  · exact projection_3762
  · exact projection_3763
  · exact projection_3764
  · exact projection_3765
  · exact projection_3766
  · exact projection_3767
  · exact projection_3768
  · exact projection_3769
  · exact projection_3770
  · exact projection_3771
  · exact projection_3772
  · exact projection_3773
  · exact projection_3774
  · exact projection_3775
  · exact projection_3776
  · exact projection_3777
  · exact projection_3778
  · exact projection_3779
  · exact projection_3780
  · exact projection_3781
  · exact projection_3782

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
