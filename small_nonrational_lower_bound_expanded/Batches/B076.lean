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
/- Source: ProjectionCertificates/R_m14e10q1_0179.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0179

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 659, 653, 181, 613, 369, 398, 650, 778, 466, 866, 812, 420, 432, 531, 37, 133, 517, 49, 81, 145, 97, 577, 641, 138, 266, 522, 82, 146, 322, 578, 386, 642, 770, 140, 268, 524, 164, 292, 548, 388, 648, 776, 176, 304, 336, 400, 352, 608, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_659, vertices_653, vertices_181, vertices_613, vertices_369, vertices_398, vertices_650, vertices_778, vertices_466, vertices_866, vertices_812, vertices_420, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_531, vertices_37, vertices_133, vertices_517, vertices_49, vertices_81, vertices_145, vertices_97, vertices_577, vertices_641, vertices_138, vertices_266, vertices_522, vertices_82, vertices_146, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_388, vertices_648, vertices_776, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_608, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_659), (false, vertices_653), (false, vertices_181), (false, vertices_613), (false, vertices_369), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_268), (true, vertices_292), (true, vertices_388), (true, vertices_776), (true, vertices_400), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
cert_nodeAtPriority_30 0 138 1 266 522 322 386 770 268 292 388 776 400 416 800 595 659 653 181 613 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 7 466 82 3
cert_row_4 1 0 1 2 6 7 398 138 1
cert_row_4 2 0 4 5 7 8 866 322 1
cert_row_4 3 1 2 4 7 8 812 268 2
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 138 398 1
cert_coverFacet 1 650
cert_cover_2 1 2 0 6 8 138 650 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 466
cert_cover_5 3 0 0 3 5 6 82 466 3
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 322 866 1
cert_coverFacet 5 812
cert_cover_5 5 3 1 2 4 7 268 812 2
cert_coverFacet 6 420
cert_cover_2 6 4 1 6 7 164 420 3
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0179

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m14e10q1_0181.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0181

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 551, 339, 659, 653, 405, 618, 594, 354, 236, 556, 420, 728, 496, 39, 19, 259, 515, 133, 261, 517, 145, 273, 641, 82, 530, 98, 290, 546, 322, 578, 44, 140, 524, 164, 292, 548, 388, 104, 552, 200, 584, 648, 208, 336, 592, 400, 656, 224, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_551, vertices_339, vertices_659, vertices_653, vertices_405, vertices_618, vertices_594, vertices_354, vertices_236, vertices_556, vertices_420, vertices_728, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_39, vertices_19, vertices_259, vertices_515, vertices_133, vertices_261, vertices_517, vertices_145, vertices_273, vertices_641, vertices_82, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_44, vertices_140, vertices_524, vertices_164, vertices_292, vertices_548, vertices_388, vertices_104, vertices_552, vertices_200, vertices_584, vertices_648, vertices_208, vertices_336, vertices_592, vertices_400, vertices_656, vertices_224, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_551), (false, vertices_339), (false, vertices_659), (false, vertices_653), (false, vertices_405), (true, vertices_98), (true, vertices_578), (true, vertices_44), (true, vertices_164), (true, vertices_104), (true, vertices_552), (true, vertices_200), (true, vertices_584), (true, vertices_208), (true, vertices_592), (true, vertices_224), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 15 13 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 16 else
  if p.val = (false, vertices_551) then 17 else
  if p.val = (false, vertices_339) then 20 else
  if p.val = (false, vertices_659) then 21 else
  if p.val = (false, vertices_653) then 14 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
cert_nodeAtPriority 2 98 1 578 0 44 164 104 552 200 584 208 592 224 352 416 653 295 551 405 339 659
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 8 618 98 1
cert_row_4 1 1 2 4 5 6 236 44 3
cert_row_4 2 2 3 5 6 8 728 200 1
cert_row_4 3 3 4 5 6 7 496 208 1
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 618
cert_cover_5 0 0 0 2 4 5 98 618 1
cert_coverFacet 1 594
cert_cover_2 1 3 0 5 8 82 594 3
cert_coverFacet 2 354
cert_cover_2 2 4 0 5 7 98 354 3
cert_coverFacet 3 236
cert_cover_5 3 1 1 2 4 5 44 236 3
cert_coverFacet 4 556
cert_cover_2 4 2 1 4 8 44 556 3
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 728
cert_cover_5 6 2 2 3 5 6 200 728 1
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 208 496 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0181

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m14e10q1_0182.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0182

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 275, 803, 677, 793, 721, 422, 454, 346, 210, 604, 812, 332, 708, 19, 35, 259, 145, 273, 529, 161, 545, 641, 769, 390, 82, 146, 274, 162, 290, 194, 322, 76, 268, 524, 164, 292, 548, 196, 324, 580, 644, 88, 280, 536, 328, 776, 208, 592, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_275, vertices_803, vertices_677, vertices_793, vertices_721, vertices_422, vertices_454, vertices_346, vertices_210, vertices_604, vertices_812, vertices_332, vertices_708] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_145, vertices_273, vertices_529, vertices_161, vertices_545, vertices_641, vertices_769, vertices_390, vertices_82, vertices_146, vertices_274, vertices_162, vertices_290, vertices_194, vertices_322, vertices_76, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_644, vertices_88, vertices_280, vertices_536, vertices_328, vertices_776, vertices_208, vertices_592, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_275), (false, vertices_803), (false, vertices_677), (false, vertices_793), (false, vertices_721), (true, vertices_390), (true, vertices_82), (true, vertices_194), (true, vertices_322), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_292), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_88), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 14 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (true, vertices_390) then 16 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_328) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_4 1 0 2 3 5 7 346 82 1
cert_row_4 2 1 2 3 5 8 604 76 2
cert_row_4 3 1 2 4 7 8 812 268 2
cert_rows
cert_pivot_2 6 0 3 1
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 390 422 2
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 390 454 2
cert_coverFacet 2 346
cert_cover_5 2 1 0 2 3 5 82 346 1
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 604
cert_cover_5 4 2 1 2 3 5 76 604 2
cert_coverFacet 5 812
cert_cover_5 5 3 1 2 4 7 268 812 2
cert_coverFacet 6 332
cert_cover_2 6 2 1 5 7 76 332 3
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0182

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m14e10q1_0188.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0188

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 213, 277, 901, 601, 737, 94, 110, 278, 294, 570, 930, 484, 616, 21, 133, 261, 81, 273, 529, 193, 577, 641, 769, 78, 22, 38, 262, 26, 42, 274, 530, 290, 546, 770, 84, 276, 100, 292, 196, 388, 88, 536, 104, 552, 584, 224, 608, 416, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_213, vertices_277, vertices_901, vertices_601, vertices_737, vertices_94, vertices_110, vertices_278, vertices_294, vertices_570, vertices_930, vertices_484, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_81, vertices_273, vertices_529, vertices_193, vertices_577, vertices_641, vertices_769, vertices_78, vertices_22, vertices_38, vertices_262, vertices_26, vertices_42, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_84, vertices_276, vertices_100, vertices_292, vertices_196, vertices_388, vertices_88, vertices_536, vertices_104, vertices_552, vertices_584, vertices_224, vertices_608, vertices_416, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_213), (false, vertices_277), (false, vertices_901), (false, vertices_601), (false, vertices_737), (true, vertices_78), (true, vertices_22), (true, vertices_38), (true, vertices_262), (true, vertices_26), (true, vertices_42), (true, vertices_290), (true, vertices_546), (true, vertices_100), (true, vertices_292), (true, vertices_104), (true, vertices_552), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_901) then 18 else
  if p.val = (false, vertices_601) then 20 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_78) then 15 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 26 3
cert_row_2 1 0 1 2 5 78
cert_row_4 2 0 4 6 7 8 930 290 2
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 3 78 94 3
cert_coverFacet 1 110
cert_cover_5 1 1 0 1 2 4 78 110 3
cert_coverFacet 2 278
cert_cover_2 2 1 0 3 7 22 278 3
cert_coverFacet 3 294
cert_cover_2 3 1 0 4 7 38 294 3
cert_coverFacet 4 570
cert_cover_5 4 0 0 2 3 4 26 570 3
cert_coverFacet 5 930
cert_cover_5 5 2 0 4 6 7 290 930 2
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 100 484 3
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0188

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m14e10q1_0189.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0189

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [79, 519, 659, 451, 525, 841, 929, 566, 214, 108, 812, 244, 488, 688, 7, 67, 131, 515, 13, 517, 73, 521, 321, 385, 641, 769, 22, 70, 518, 146, 530, 194, 44, 76, 524, 52, 212, 100, 548, 104, 296, 328, 776, 176, 560, 656, 224, 416, 672, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_79, vertices_519, vertices_659, vertices_451, vertices_525, vertices_841, vertices_929, vertices_566, vertices_214, vertices_108, vertices_812, vertices_244, vertices_488, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_67, vertices_131, vertices_515, vertices_13, vertices_517, vertices_73, vertices_521, vertices_321, vertices_385, vertices_641, vertices_769, vertices_22, vertices_70, vertices_518, vertices_146, vertices_530, vertices_194, vertices_44, vertices_76, vertices_524, vertices_52, vertices_212, vertices_100, vertices_548, vertices_104, vertices_296, vertices_328, vertices_776, vertices_176, vertices_560, vertices_656, vertices_224, vertices_416, vertices_672, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_79), (false, vertices_519), (false, vertices_659), (false, vertices_451), (false, vertices_525), (false, vertices_841), (false, vertices_929), (true, vertices_22), (true, vertices_44), (true, vertices_52), (true, vertices_212), (true, vertices_100), (true, vertices_548), (true, vertices_104), (true, vertices_296), (true, vertices_176), (true, vertices_560), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_79) then 13 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (false, vertices_929) then 22 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_212) then 17 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_79), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 22 3
cert_row_2 1 1 3 5 6 212
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 22 566 3
cert_coverFacet 1 214
cert_cover_5 1 1 0 1 3 5 22 214 3
cert_coverFacet 2 108
cert_cover_2 2 2 1 4 5 44 108 3
cert_coverFacet 3 812
cert_cover_5 3 2 1 2 4 7 44 812 3
cert_coverFacet 4 244
cert_cover_5 4 1 1 3 4 5 52 244 3
cert_coverFacet 5 488
cert_cover_5 5 3 2 4 5 6 104 488 3
cert_coverFacet 6 688
cert_cover_2 6 4 3 6 8 176 688 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0189

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m14e10q1_0190.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0190

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 789, 89, 409, 713, 929, 94, 110, 566, 738, 284, 300, 804, 488, 25, 73, 137, 81, 273, 529, 577, 385, 641, 769, 78, 22, 38, 82, 530, 98, 546, 578, 28, 44, 268, 276, 532, 292, 548, 772, 88, 280, 104, 296, 200, 392, 224, 416, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_789, vertices_89, vertices_409, vertices_713, vertices_929, vertices_94, vertices_110, vertices_566, vertices_738, vertices_284, vertices_300, vertices_804, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_137, vertices_81, vertices_273, vertices_529, vertices_577, vertices_385, vertices_641, vertices_769, vertices_78, vertices_22, vertices_38, vertices_82, vertices_530, vertices_98, vertices_546, vertices_578, vertices_28, vertices_44, vertices_268, vertices_276, vertices_532, vertices_292, vertices_548, vertices_772, vertices_88, vertices_280, vertices_104, vertices_296, vertices_200, vertices_392, vertices_224, vertices_416, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_789), (false, vertices_89), (false, vertices_409), (false, vertices_713), (false, vertices_929), (true, vertices_78), (true, vertices_22), (true, vertices_38), (true, vertices_98), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_292), (true, vertices_548), (true, vertices_104), (true, vertices_296), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_89) then 0 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_78) then 15 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_224) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_89), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 22 3
cert_row_2 1 0 1 2 5 78
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 3 78 94 3
cert_coverFacet 1 110
cert_cover_5 1 1 0 1 2 4 78 110 3
cert_coverFacet 2 566
cert_cover_5 2 0 0 1 3 4 22 566 3
cert_coverFacet 3 738
cert_cover_5 3 2 0 4 5 6 98 738 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0190

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m14e10q1_0206.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0206

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 155, 531, 451, 569, 201, 841, 182, 566, 390, 620, 228, 964, 248, 19, 131, 259, 515, 25, 73, 137, 521, 529, 193, 321, 769, 54, 134, 262, 518, 146, 530, 386, 100, 164, 548, 196, 580, 388, 772, 56, 152, 104, 552, 200, 584, 176, 560, 224, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_155, vertices_531, vertices_451, vertices_569, vertices_201, vertices_841, vertices_182, vertices_566, vertices_390, vertices_620, vertices_228, vertices_964, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_25, vertices_73, vertices_137, vertices_521, vertices_529, vertices_193, vertices_321, vertices_769, vertices_54, vertices_134, vertices_262, vertices_518, vertices_146, vertices_530, vertices_386, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_388, vertices_772, vertices_56, vertices_152, vertices_104, vertices_552, vertices_200, vertices_584, vertices_176, vertices_560, vertices_224, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_155), (false, vertices_531), (false, vertices_451), (false, vertices_569), (false, vertices_201), (false, vertices_841), (true, vertices_54), (true, vertices_134), (true, vertices_100), (true, vertices_164), (true, vertices_548), (true, vertices_196), (true, vertices_580), (true, vertices_388), (true, vertices_104), (true, vertices_176), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_155) then 16 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_451) then 17 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (true, vertices_54) then 14 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
cert_nodeAtPriority_10 1 531 0 201 134 100 164 548 196 580 388 104 176 224 775 54 155 451 569 841
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 1 5 6 7 8 964 196 3
cert_row_4 2 1 2 4 5 8 620 100 1
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 6 54 182 3
cert_coverFacet 1 566
cert_cover_5 1 0 0 1 3 8 54 566 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 620
cert_cover_5 3 2 1 2 4 5 100 620 1
cert_coverFacet 4 228
cert_cover_2 4 4 1 5 6 100 228 3
cert_coverFacet 5 964
cert_cover_5 5 1 1 5 6 7 196 964 3
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 56 248 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0206

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m14e10q1_0209.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0209

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 339, 659, 313, 681, 177, 838, 594, 236, 364, 908, 724, 240, 368, 19, 259, 515, 41, 265, 521, 49, 145, 273, 161, 641, 82, 530, 322, 578, 770, 108, 140, 268, 196, 324, 580, 644, 772, 168, 296, 648, 776, 112, 176, 304, 208, 336, 592, 656, 224, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_339, vertices_659, vertices_313, vertices_681, vertices_177, vertices_838, vertices_594, vertices_236, vertices_364, vertices_908, vertices_724, vertices_240, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_259, vertices_515, vertices_41, vertices_265, vertices_521, vertices_49, vertices_145, vertices_273, vertices_161, vertices_641, vertices_82, vertices_530, vertices_322, vertices_578, vertices_770, vertices_108, vertices_140, vertices_268, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_168, vertices_296, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_336, vertices_592, vertices_656, vertices_224, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_339), (false, vertices_659), (false, vertices_313), (false, vertices_681), (false, vertices_177), (true, vertices_578), (true, vertices_108), (true, vertices_140), (true, vertices_268), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_644), (true, vertices_772), (true, vertices_112), (true, vertices_208), (true, vertices_592), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_339) then 16 else
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_108) then 19 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 1 2 6 7 8 908 140 3
cert_row_4 3 1 3 5 6 8 724 196 1
cert_rows
cert_pivot_2 4 0 2 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 594
cert_cover_2 1 3 0 5 8 82 594 3
cert_coverFacet 2 236
cert_cover_5 2 0 1 2 4 6 108 236 3
cert_coverFacet 3 364
cert_cover_5 3 0 1 2 4 7 108 364 3
cert_coverFacet 4 908
cert_cover_5 4 2 1 2 6 7 140 908 3
cert_coverFacet 5 724
cert_cover_5 5 3 1 3 5 6 196 724 1
cert_coverFacet 6 240
cert_cover_2 6 4 3 5 6 112 240 3
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0209

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m14e10q1_0212.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0212

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 541, 341, 709, 569, 241, 838, 810, 434, 450, 706, 316, 780, 464, 21, 69, 517, 537, 49, 81, 161, 545, 193, 641, 162, 290, 546, 194, 322, 578, 386, 642, 770, 28, 268, 524, 276, 324, 580, 772, 56, 296, 552, 776, 176, 304, 208, 336, 400, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_541, vertices_341, vertices_709, vertices_569, vertices_241, vertices_838, vertices_810, vertices_434, vertices_450, vertices_706, vertices_316, vertices_780, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_517, vertices_537, vertices_49, vertices_81, vertices_161, vertices_545, vertices_193, vertices_641, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_276, vertices_324, vertices_580, vertices_772, vertices_56, vertices_296, vertices_552, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_400, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_541), (false, vertices_341), (false, vertices_709), (false, vertices_569), (false, vertices_241), (true, vertices_290), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_770), (true, vertices_268), (true, vertices_772), (true, vertices_296), (true, vertices_776), (true, vertices_304), (true, vertices_400), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_709) then 17 else
  if p.val = (false, vertices_569) then 20 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (true, vertices_290) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
cert_priority
cert_nodeAtPriority_12 290 1 194 2 322 578 386 770 268 772 296 776 304 400 448 675 341 709 541 569 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 7 8 838 322 1
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_4 2 0 3 4 6 7 434 162 1
cert_row_4 3 1 2 3 4 7 316 28 3
cert_rows
cert_pivot_2 5 8 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 0 0 1 5 7 322 838 1
cert_coverFacet 1 810
cert_cover_5 1 1 0 2 4 7 290 810 1
cert_coverFacet 2 434
cert_cover_5 2 2 0 3 4 6 162 434 1
cert_coverFacet 3 450
cert_cover_2 3 5 0 6 7 194 450 3
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 316
cert_cover_5 5 3 1 2 3 4 28 316 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0212

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m14e10q1_0213.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0213

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 653, 405, 805, 841, 465, 678, 810, 330, 650, 242, 354, 372, 180, 133, 261, 517, 73, 137, 521, 401, 193, 321, 769, 74, 138, 266, 522, 98, 162, 290, 546, 194, 322, 642, 52, 148, 276, 164, 292, 548, 644, 328, 648, 776, 112, 176, 208, 336, 352, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_653, vertices_405, vertices_805, vertices_841, vertices_465, vertices_678, vertices_810, vertices_330, vertices_650, vertices_242, vertices_354, vertices_372, vertices_180] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_401, vertices_193, vertices_321, vertices_769, vertices_74, vertices_138, vertices_266, vertices_522, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_642, vertices_52, vertices_148, vertices_276, vertices_164, vertices_292, vertices_548, vertices_644, vertices_328, vertices_648, vertices_776, vertices_112, vertices_176, vertices_208, vertices_336, vertices_352, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_653), (false, vertices_405), (false, vertices_805), (false, vertices_841), (false, vertices_465), (true, vertices_266), (true, vertices_522), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_642), (true, vertices_52), (true, vertices_164), (true, vertices_112), (true, vertices_176), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_405) then 21 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 266 2
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 0 3 4 5 6 242 98 1
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 266 810 2
cert_coverFacet 2 330
cert_cover_2 2 2 0 5 7 74 330 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 242
cert_cover_5 4 2 0 3 4 5 98 242 1
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 372
cert_cover_5 6 3 1 3 4 5 52 372 3
cert_coverFacet 7 180
cert_cover_2 7 3 1 4 6 52 180 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0213

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m14e10q1_0214.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0214

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 267, 803, 677, 345, 713, 833, 566, 58, 282, 850, 124, 236, 724, 11, 35, 259, 73, 137, 265, 161, 545, 321, 577, 641, 769, 26, 42, 266, 50, 274, 530, 546, 770, 108, 52, 84, 532, 164, 548, 196, 644, 56, 88, 280, 168, 200, 336, 592, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_267, vertices_803, vertices_677, vertices_345, vertices_713, vertices_833, vertices_566, vertices_58, vertices_282, vertices_850, vertices_124, vertices_236, vertices_724] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_73, vertices_137, vertices_265, vertices_161, vertices_545, vertices_321, vertices_577, vertices_641, vertices_769, vertices_26, vertices_42, vertices_266, vertices_50, vertices_274, vertices_530, vertices_546, vertices_770, vertices_108, vertices_52, vertices_84, vertices_532, vertices_164, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_280, vertices_168, vertices_200, vertices_336, vertices_592, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_267), (false, vertices_803), (false, vertices_677), (false, vertices_345), (false, vertices_713), (false, vertices_833), (true, vertices_26), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_108), (true, vertices_52), (true, vertices_84), (true, vertices_532), (true, vertices_196), (true, vertices_56), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 13 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_833) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_108) then 17 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_592) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 1 3 4 8 566 50 1
cert_row_4 2 0 3 5 7 8 850 274 2
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 1 0 1 3 4 50 566 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 850
cert_cover_5 3 2 0 3 5 7 274 850 2
cert_coverFacet 4 124
cert_cover_5 4 0 1 2 3 4 108 124 2
cert_coverFacet 5 236
cert_cover_5 5 0 1 2 4 6 108 236 3
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 84 724 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0214

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m14e10q1_0216.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0216

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 565, 597, 313, 217, 681, 838, 394, 650, 778, 466, 812, 372, 408, 533, 25, 41, 137, 49, 81, 545, 193, 577, 641, 138, 266, 522, 194, 322, 578, 386, 642, 770, 52, 84, 292, 548, 324, 580, 772, 152, 280, 296, 552, 392, 648, 776, 304, 208, 336, 400]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_565, vertices_597, vertices_313, vertices_217, vertices_681, vertices_838, vertices_394, vertices_650, vertices_778, vertices_466, vertices_812, vertices_372, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_533, vertices_25, vertices_41, vertices_137, vertices_49, vertices_81, vertices_545, vertices_193, vertices_577, vertices_641, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_296, vertices_552, vertices_392, vertices_648, vertices_776, vertices_304, vertices_208, vertices_336, vertices_400] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_565), (false, vertices_597), (false, vertices_313), (false, vertices_217), (false, vertices_681), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_292), (true, vertices_324), (true, vertices_772), (true, vertices_392), (true, vertices_776), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_565) then 16 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_313) then 19 else
  if p.val = (false, vertices_217) then 20 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 7 466 194 1
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 1 2 4 7 8 812 292 1
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 6 0 2 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 466
cert_cover_5 4 0 0 3 5 6 194 466 1
cert_coverFacet 5 812
cert_cover_5 5 2 1 2 4 7 292 812 1
cert_coverFacet 6 372
cert_cover_5 6 3 1 3 4 5 52 372 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0216

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m14e10q1_0219.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0219

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 837, 185, 617, 457, 673, 790, 154, 282, 394, 690, 316, 364, 628, 41, 73, 137, 161, 545, 321, 577, 385, 641, 769, 26, 138, 266, 146, 274, 530, 386, 642, 770, 300, 52, 276, 532, 100, 324, 580, 772, 56, 152, 280, 104, 328, 392, 176, 560, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_837, vertices_185, vertices_617, vertices_457, vertices_673, vertices_790, vertices_154, vertices_282, vertices_394, vertices_690, vertices_316, vertices_364, vertices_628] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_137, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_300, vertices_52, vertices_276, vertices_532, vertices_100, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_104, vertices_328, vertices_392, vertices_176, vertices_560, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_837), (false, vertices_185), (false, vertices_617), (false, vertices_457), (false, vertices_673), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_300), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_100), (true, vertices_280), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_185) then 19 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_673) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_300) then 17 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_560) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_300), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 7 300
cert_row_4 1 0 1 3 7 8 790 274 1
cert_row_4 2 0 3 4 6 8 690 146 2
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 274 790 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 690
cert_cover_5 4 2 0 3 4 6 146 690 2
cert_coverFacet 5 316
cert_cover_5 5 0 1 2 3 4 300 316 2
cert_coverFacet 6 364
cert_cover_5 6 0 1 2 4 5 300 364 3
cert_coverFacet 7 628
cert_cover_5 7 3 1 3 4 5 52 628 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0219

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m14e10q1_0220.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0220

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 565, 229, 837, 457, 673, 790, 154, 282, 394, 690, 316, 364, 248, 37, 69, 517, 161, 545, 193, 321, 385, 641, 769, 26, 138, 266, 146, 274, 530, 386, 642, 770, 300, 52, 276, 532, 100, 324, 772, 56, 152, 280, 104, 200, 328, 392, 176, 560, 224, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_565, vertices_229, vertices_837, vertices_457, vertices_673, vertices_790, vertices_154, vertices_282, vertices_394, vertices_690, vertices_316, vertices_364, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_300, vertices_52, vertices_276, vertices_532, vertices_100, vertices_324, vertices_772, vertices_56, vertices_152, vertices_280, vertices_104, vertices_200, vertices_328, vertices_392, vertices_176, vertices_560, vertices_224, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_565), (false, vertices_229), (false, vertices_837), (false, vertices_457), (false, vertices_673), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_300), (true, vertices_276), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_104), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 18 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_229) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_457) then 16 else
  if p.val = (false, vertices_673) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_300) then 17 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_176) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_300), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 5 6 248 56 3
cert_row_2 1 1 2 4 7 300
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 0 3 4 6 8 690 146 2
cert_rows
cert_pivot_2 5 2 1 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 690
cert_cover_5 4 3 0 3 4 6 146 690 2
cert_coverFacet 5 316
cert_cover_5 5 1 1 2 3 4 300 316 2
cert_coverFacet 6 364
cert_cover_5 6 1 1 2 4 5 300 364 3
cert_coverFacet 7 248
cert_cover_5 7 0 2 3 4 5 56 248 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0220

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m14e10q1_0222.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0222

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 899, 285, 601, 457, 737, 310, 690, 482, 540, 620, 332, 564, 356, 771, 25, 73, 265, 273, 529, 193, 577, 385, 641, 50, 274, 530, 162, 290, 386, 642, 28, 76, 268, 524, 52, 276, 532, 100, 292, 548, 324, 536, 328, 584, 560, 224, 352, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_899, vertices_285, vertices_601, vertices_457, vertices_737, vertices_310, vertices_690, vertices_482, vertices_540, vertices_620, vertices_332, vertices_564, vertices_356] (by decide +kernel)
  polygons := literalFinset [vertices_771, vertices_25, vertices_73, vertices_265, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_641, vertices_50, vertices_274, vertices_530, vertices_162, vertices_290, vertices_386, vertices_642, vertices_28, vertices_76, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_324, vertices_536, vertices_328, vertices_584, vertices_560, vertices_224, vertices_352, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_899), (false, vertices_285), (false, vertices_601), (false, vertices_457), (false, vertices_737), (true, vertices_50), (true, vertices_162), (true, vertices_290), (true, vertices_76), (true, vertices_524), (true, vertices_52), (true, vertices_532), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_324), (true, vertices_560), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_285) then 17 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 5 8 620 76 2
cert_row_4 1 0 1 3 4 7 310 50 1
cert_row_4 2 0 3 4 6 8 690 50 3
cert_row_4 3 0 4 5 6 7 482 162 2
cert_rows
cert_pivot_2 2 1 3 0
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 1 0 1 3 4 50 310 1
cert_coverFacet 1 690
cert_cover_5 1 2 0 3 4 6 50 690 3
cert_coverFacet 2 482
cert_cover_5 2 3 0 4 5 6 162 482 2
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 620
cert_cover_5 4 0 1 2 4 5 76 620 2
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 356
cert_cover_2 7 4 1 5 7 100 356 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0222

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m14e10q1_0226.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0226

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 707, 565, 121, 681, 457, 278, 534, 806, 906, 466, 372, 360, 808, 579, 41, 73, 137, 49, 81, 529, 545, 193, 641, 22, 262, 518, 82, 274, 530, 194, 386, 642, 770, 52, 276, 532, 292, 548, 104, 296, 552, 328, 392, 648, 776, 112, 336, 352, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_707, vertices_565, vertices_121, vertices_681, vertices_457, vertices_278, vertices_534, vertices_806, vertices_906, vertices_466, vertices_372, vertices_360, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_579, vertices_41, vertices_73, vertices_137, vertices_49, vertices_81, vertices_529, vertices_545, vertices_193, vertices_641, vertices_22, vertices_262, vertices_518, vertices_82, vertices_274, vertices_530, vertices_194, vertices_386, vertices_642, vertices_770, vertices_52, vertices_276, vertices_532, vertices_292, vertices_548, vertices_104, vertices_296, vertices_552, vertices_328, vertices_392, vertices_648, vertices_776, vertices_112, vertices_336, vertices_352, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_707), (false, vertices_565), (false, vertices_121), (false, vertices_681), (false, vertices_457), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_274), (true, vertices_386), (true, vertices_770), (true, vertices_276), (true, vertices_292), (true, vertices_296), (true, vertices_776), (true, vertices_336), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_565) then 17 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 386 1
cert_row_4 1 0 1 4 7 8 806 262 2
cert_row_4 2 0 3 5 6 7 466 82 3
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 806
cert_cover_5 2 1 0 1 4 7 262 806 2
cert_coverFacet 3 906
cert_cover_5 3 0 0 2 6 7 386 906 1
cert_coverFacet 4 466
cert_cover_5 4 2 0 3 5 6 82 466 3
cert_coverFacet 5 372
cert_cover_5 5 3 1 3 4 5 52 372 3
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0226

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m14e10q1_0228.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0228

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 173, 781, 357, 569, 369, 454, 906, 690, 210, 338, 396, 244, 680, 13, 37, 261, 41, 521, 49, 273, 529, 353, 769, 82, 146, 274, 530, 194, 322, 386, 642, 770, 140, 268, 100, 164, 196, 324, 388, 168, 552, 392, 648, 776, 112, 176, 560, 208, 336, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_173, vertices_781, vertices_357, vertices_569, vertices_369, vertices_454, vertices_906, vertices_690, vertices_210, vertices_338, vertices_396, vertices_244, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_261, vertices_41, vertices_521, vertices_49, vertices_273, vertices_529, vertices_353, vertices_769, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_140, vertices_268, vertices_100, vertices_164, vertices_196, vertices_324, vertices_388, vertices_168, vertices_552, vertices_392, vertices_648, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_336, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_173), (false, vertices_781), (false, vertices_357), (false, vertices_569), (false, vertices_369), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_642), (true, vertices_196), (true, vertices_388), (true, vertices_392), (true, vertices_648), (true, vertices_176), (true, vertices_208), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 21 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_173) then 16 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 386 1
cert_row_4 1 0 1 5 6 7 454 194 1
cert_row_4 2 0 3 4 6 8 690 146 2
cert_row_4 3 1 3 4 5 6 244 100 1
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 1 0 1 5 6 194 454 1
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 386 906 1
cert_coverFacet 2 690
cert_cover_5 2 2 0 3 4 6 146 690 2
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 244
cert_cover_5 6 3 1 3 4 5 100 244 1
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0228

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m14e10q1_0230.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0230

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 171, 395, 563, 677, 453, 58, 602, 778, 844, 708, 120, 488, 752, 139, 35, 259, 515, 133, 261, 517, 161, 545, 385, 26, 42, 266, 522, 50, 530, 770, 196, 324, 580, 644, 772, 56, 88, 104, 168, 328, 584, 392, 776, 112, 560, 592, 224, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_171, vertices_395, vertices_563, vertices_677, vertices_453, vertices_58, vertices_602, vertices_778, vertices_844, vertices_708, vertices_120, vertices_488, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_139, vertices_35, vertices_259, vertices_515, vertices_133, vertices_261, vertices_517, vertices_161, vertices_545, vertices_385, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_530, vertices_770, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_56, vertices_88, vertices_104, vertices_168, vertices_328, vertices_584, vertices_392, vertices_776, vertices_112, vertices_560, vertices_592, vertices_224, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_171), (false, vertices_395), (false, vertices_563), (false, vertices_677), (false, vertices_453), (true, vertices_26), (true, vertices_522), (true, vertices_580), (true, vertices_56), (true, vertices_88), (true, vertices_104), (true, vertices_328), (true, vertices_584), (true, vertices_776), (true, vertices_112), (true, vertices_592), (true, vertices_224), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 13 21 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_171) then 18 else
  if p.val = (false, vertices_395) then 19 else
  if p.val = (false, vertices_563) then 20 else
  if p.val = (false, vertices_677) then 15 else
  if p.val = (false, vertices_453) then 16 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_580) then 2 else
  if p.val = (true, vertices_56) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_4 1 1 2 5 7 8 844 324 1
cert_row_4 2 2 4 5 6 7 488 104 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 58
cert_cover_2 0 2 0 3 4 26 58 3
cert_coverFacet 1 602
cert_cover_5 1 0 0 2 3 5 26 602 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 844
cert_cover_5 3 1 1 2 5 7 324 844 1
cert_coverFacet 4 708
cert_cover_2 4 5 1 6 8 196 708 3
cert_coverFacet 5 120
cert_cover_2 5 3 2 4 5 56 120 3
cert_coverFacet 6 488
cert_cover_5 6 2 2 4 5 6 104 488 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0230

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m14e10q1_0248.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0248

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 789, 121, 689, 337, 481, 542, 270, 774, 618, 458, 738, 348, 568, 49, 81, 273, 529, 97, 161, 321, 385, 641, 769, 14, 262, 518, 74, 266, 522, 610, 194, 386, 642, 770, 28, 268, 276, 532, 772, 56, 88, 536, 104, 552, 328, 560, 336, 224, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_789, vertices_121, vertices_689, vertices_337, vertices_481, vertices_542, vertices_270, vertices_774, vertices_618, vertices_458, vertices_738, vertices_348, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_273, vertices_529, vertices_97, vertices_161, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_262, vertices_518, vertices_74, vertices_266, vertices_522, vertices_610, vertices_194, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_276, vertices_532, vertices_772, vertices_56, vertices_88, vertices_536, vertices_104, vertices_552, vertices_328, vertices_560, vertices_336, vertices_224, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_789), (false, vertices_121), (false, vertices_689), (false, vertices_337), (false, vertices_481), (true, vertices_14), (true, vertices_262), (true, vertices_518), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_610), (true, vertices_194), (true, vertices_28), (true, vertices_268), (true, vertices_536), (true, vertices_552), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_610) then 15 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_328) then 12 else
  0
cert_priority
cert_nodeAtPriority_49 337 14 262 518 74 266 522 194 28 268 536 552 328 899 610 789 121 689 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 5 8 610
cert_row_4 1 0 1 2 3 8 542 14 3
cert_row_4 2 0 2 5 6 7 458 74 3
cert_row_4 3 1 2 3 5 7 348 28 3
cert_rows
cert_pivot_2 4 8 0 1
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 1 0 1 2 3 14 542 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 618
cert_cover_5 3 0 0 2 4 5 74 618 2
cert_coverFacet 4 458
cert_cover_5 4 2 0 2 5 6 74 458 3
cert_coverFacet 5 738
cert_cover_5 5 0 0 4 5 6 610 738 3
cert_coverFacet 6 348
cert_cover_5 6 3 1 2 3 5 28 348 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0248

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m14e10q1_0249.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0249

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 563, 419, 589, 233, 393, 609, 790, 306, 460, 780, 436, 724, 752, 35, 259, 515, 73, 137, 265, 521, 97, 161, 545, 577, 385, 50, 274, 530, 290, 770, 76, 268, 524, 148, 276, 532, 196, 580, 388, 772, 200, 392, 776, 176, 304, 560, 720, 224, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_563, vertices_419, vertices_589, vertices_233, vertices_393, vertices_609, vertices_790, vertices_306, vertices_460, vertices_780, vertices_436, vertices_724, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_73, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_577, vertices_385, vertices_50, vertices_274, vertices_530, vertices_290, vertices_770, vertices_76, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_196, vertices_580, vertices_388, vertices_772, vertices_200, vertices_392, vertices_776, vertices_176, vertices_304, vertices_560, vertices_720, vertices_224, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_563), (false, vertices_419), (false, vertices_589), (false, vertices_233), (false, vertices_393), (false, vertices_609), (true, vertices_274), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_196), (true, vertices_388), (true, vertices_772), (true, vertices_176), (true, vertices_304), (true, vertices_720)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_563) then 14 else
  if p.val = (false, vertices_419) then 15 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (false, vertices_609) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_720) then 21 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_609), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_2 1 3 5 6 8 720
cert_row_4 2 1 2 5 6 7 460 76 3
cert_row_4 3 1 3 4 6 7 436 148 2
cert_rows
cert_pivot_2 0 8 2 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 306
cert_cover_2 1 3 0 4 7 50 306 3
cert_coverFacet 2 460
cert_cover_5 2 2 1 2 5 6 76 460 3
cert_coverFacet 3 780
cert_cover_2 3 2 1 7 8 268 780 3
cert_coverFacet 4 436
cert_cover_5 4 3 1 3 4 6 148 436 2
cert_coverFacet 5 724
cert_cover_5 5 1 1 3 5 6 148 724 2
cert_coverFacet 6 752
cert_cover_5 6 1 3 4 5 6 176 752 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0249

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m14e10q1_0251.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0251

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 141, 269, 661, 805, 217, 841, 678, 122, 186, 658, 866, 364, 172, 13, 133, 261, 517, 73, 137, 265, 81, 145, 529, 577, 769, 58, 82, 146, 530, 98, 162, 546, 578, 642, 44, 140, 268, 164, 292, 548, 644, 88, 152, 104, 168, 328, 656, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_141, vertices_269, vertices_661, vertices_805, vertices_217, vertices_841, vertices_678, vertices_122, vertices_186, vertices_658, vertices_866, vertices_364, vertices_172] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_81, vertices_145, vertices_529, vertices_577, vertices_769, vertices_58, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_578, vertices_642, vertices_44, vertices_140, vertices_268, vertices_164, vertices_292, vertices_548, vertices_644, vertices_88, vertices_152, vertices_104, vertices_168, vertices_328, vertices_656, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_141), (false, vertices_269), (false, vertices_661), (false, vertices_805), (false, vertices_217), (false, vertices_841), (true, vertices_58), (true, vertices_146), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_642), (true, vertices_44), (true, vertices_164), (true, vertices_104), (true, vertices_168), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 13 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_269) then 1 else
  if p.val = (false, vertices_661) then 16 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_217) then 19 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (true, vertices_58) then 14 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
cert_nodeAtPriority_10 0 141 1 269 146 98 162 546 642 44 164 104 168 352 595 58 661 805 217 841
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 4 58
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 0 4 5 7 8 866 98 3
cert_row_4 3 1 2 4 5 7 364 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 5 58 122 3
cert_coverFacet 2 186
cert_cover_5 2 0 0 2 3 6 58 186 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 98 866 3
cert_coverFacet 5 364
cert_cover_5 5 3 1 2 4 5 44 364 3
cert_coverFacet 6 172
cert_cover_2 6 2 1 4 6 44 172 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0251

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m14e10q1_0261.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0261

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [87, 539, 355, 547, 533, 837, 929, 218, 234, 554, 212, 916, 484, 696, 19, 35, 67, 515, 21, 69, 517, 529, 289, 545, 321, 769, 26, 42, 202, 522, 82, 98, 546, 84, 148, 532, 196, 324, 388, 772, 152, 536, 168, 552, 208, 656, 224, 352, 416, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_87, vertices_539, vertices_355, vertices_547, vertices_533, vertices_837, vertices_929, vertices_218, vertices_234, vertices_554, vertices_212, vertices_916, vertices_484, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_67, vertices_515, vertices_21, vertices_69, vertices_517, vertices_529, vertices_289, vertices_545, vertices_321, vertices_769, vertices_26, vertices_42, vertices_202, vertices_522, vertices_82, vertices_98, vertices_546, vertices_84, vertices_148, vertices_532, vertices_196, vertices_324, vertices_388, vertices_772, vertices_152, vertices_536, vertices_168, vertices_552, vertices_208, vertices_656, vertices_224, vertices_352, vertices_416, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_87), (false, vertices_539), (false, vertices_355), (false, vertices_547), (false, vertices_533), (false, vertices_837), (false, vertices_929), (true, vertices_42), (true, vertices_202), (true, vertices_148), (true, vertices_196), (true, vertices_388), (true, vertices_152), (true, vertices_168), (true, vertices_552), (true, vertices_208), (true, vertices_656), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_87) then 13 else
  if p.val = (false, vertices_539) then 16 else
  if p.val = (false, vertices_355) then 17 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_837) then 14 else
  if p.val = (false, vertices_929) then 22 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_87), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_4 1 1 4 5 6 7 484 196 1
cert_row_4 2 1 3 6 7 8 916 148 3
cert_row_4 3 2 3 4 6 8 696 152 2
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 218
cert_cover_5 0 0 0 2 3 5 26 218 3
cert_coverFacet 1 234
cert_cover_5 1 0 0 2 4 5 42 234 3
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 212
cert_cover_2 3 3 1 5 6 84 212 3
cert_coverFacet 4 916
cert_cover_5 4 2 1 3 6 7 148 916 3
cert_coverFacet 5 484
cert_cover_5 5 1 1 4 5 6 196 484 1
cert_coverFacet 6 696
cert_cover_5 6 3 2 3 4 6 152 696 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0261

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m14e10q1_0264.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0264

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 267, 675, 291, 421, 345, 961, 302, 558, 284, 540, 692, 468, 728, 11, 35, 259, 515, 73, 265, 161, 289, 321, 577, 385, 641, 46, 266, 522, 290, 546, 28, 268, 524, 148, 276, 532, 164, 292, 548, 388, 88, 280, 536, 584, 208, 336, 656, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_267, vertices_675, vertices_291, vertices_421, vertices_345, vertices_961, vertices_302, vertices_558, vertices_284, vertices_540, vertices_692, vertices_468, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_515, vertices_73, vertices_265, vertices_161, vertices_289, vertices_321, vertices_577, vertices_385, vertices_641, vertices_46, vertices_266, vertices_522, vertices_290, vertices_546, vertices_28, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_88, vertices_280, vertices_536, vertices_584, vertices_208, vertices_336, vertices_656, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_267), (false, vertices_675), (false, vertices_291), (false, vertices_421), (false, vertices_345), (false, vertices_961), (true, vertices_46), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_548), (true, vertices_536), (true, vertices_208), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 13 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_291) then 1 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_46) then 15 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_656) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 1 3 4 6 8 692 148 2
cert_row_4 2 1 3 5 6 7 468 148 2
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 7 46 302 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 8 46 558 3
cert_coverFacet 2 284
cert_cover_2 2 2 1 3 7 28 284 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 692
cert_cover_5 4 1 1 3 4 6 148 692 2
cert_coverFacet 5 468
cert_cover_5 5 2 1 3 5 6 148 468 2
cert_coverFacet 6 728
cert_cover_5 6 3 2 3 5 6 88 728 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0264

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m14e10q1_0265.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0265

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 527, 357, 709, 313, 617, 390, 646, 570, 282, 722, 402, 468, 880, 15, 69, 261, 517, 41, 265, 521, 97, 289, 577, 134, 262, 518, 26, 266, 522, 146, 274, 530, 386, 642, 196, 324, 388, 644, 56, 280, 552, 304, 560, 208, 336, 592, 400, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_527, vertices_357, vertices_709, vertices_313, vertices_617, vertices_390, vertices_646, vertices_570, vertices_282, vertices_722, vertices_402, vertices_468, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_15, vertices_69, vertices_261, vertices_517, vertices_41, vertices_265, vertices_521, vertices_97, vertices_289, vertices_577, vertices_134, vertices_262, vertices_518, vertices_26, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_196, vertices_324, vertices_388, vertices_644, vertices_56, vertices_280, vertices_552, vertices_304, vertices_560, vertices_208, vertices_336, vertices_592, vertices_400, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_527), (false, vertices_357), (false, vertices_709), (false, vertices_313), (false, vertices_617), (true, vertices_134), (true, vertices_26), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_388), (true, vertices_560), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 14 else
  if p.val = (false, vertices_527) then 15 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_313) then 20 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
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
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 722
cert_cover_5 4 1 0 3 5 6 146 722 2
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 468
cert_cover_5 6 2 1 3 5 6 196 468 1
cert_coverFacet 7 880
cert_cover_5 7 3 3 4 5 7 304 880 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0265

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m14e10q1_0266.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0266

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 535, 589, 229, 433, 721, 302, 526, 842, 306, 914, 332, 356, 992, 23, 37, 69, 517, 49, 145, 529, 161, 193, 577, 14, 38, 518, 266, 522, 50, 274, 530, 290, 770, 76, 268, 524, 100, 292, 324, 328, 584, 304, 400, 656, 224, 352, 416, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_535, vertices_589, vertices_229, vertices_433, vertices_721, vertices_302, vertices_526, vertices_842, vertices_306, vertices_914, vertices_332, vertices_356, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_37, vertices_69, vertices_517, vertices_49, vertices_145, vertices_529, vertices_161, vertices_193, vertices_577, vertices_14, vertices_38, vertices_518, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_290, vertices_770, vertices_76, vertices_268, vertices_524, vertices_100, vertices_292, vertices_324, vertices_328, vertices_584, vertices_304, vertices_400, vertices_656, vertices_224, vertices_352, vertices_416, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_535), (false, vertices_589), (false, vertices_229), (false, vertices_433), (false, vertices_721), (true, vertices_14), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_290), (true, vertices_770), (true, vertices_268), (true, vertices_292), (true, vertices_324), (true, vertices_328), (true, vertices_352), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 14 else
  if p.val = (false, vertices_535) then 15 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 7 302 14 3
cert_row_4 1 0 2 5 7 8 842 266 2
cert_row_4 2 0 3 6 7 8 914 274 2
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 1 2 0 4
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 4 14 302 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 842
cert_cover_5 2 1 0 2 5 7 266 842 2
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 914
cert_cover_5 4 2 0 3 6 7 274 914 2
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 356
cert_cover_2 6 4 1 5 7 100 356 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0266

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m14e10q1_0267.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0267

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 227, 541, 205, 149, 841, 625, 406, 458, 306, 866, 396, 780, 820, 163, 13, 21, 133, 73, 521, 49, 145, 529, 97, 193, 577, 50, 146, 274, 98, 290, 194, 322, 386, 140, 268, 524, 148, 276, 532, 388, 772, 200, 328, 392, 776, 304, 560, 608, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_227, vertices_541, vertices_205, vertices_149, vertices_841, vertices_625, vertices_406, vertices_458, vertices_306, vertices_866, vertices_396, vertices_780, vertices_820] (by decide +kernel)
  polygons := literalFinset [vertices_163, vertices_13, vertices_21, vertices_133, vertices_73, vertices_521, vertices_49, vertices_145, vertices_529, vertices_97, vertices_193, vertices_577, vertices_50, vertices_146, vertices_274, vertices_98, vertices_290, vertices_194, vertices_322, vertices_386, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_200, vertices_328, vertices_392, vertices_776, vertices_304, vertices_560, vertices_608, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_227), (false, vertices_541), (false, vertices_205), (false, vertices_149), (false, vertices_841), (false, vertices_625), (true, vertices_274), (true, vertices_290), (true, vertices_322), (true, vertices_386), (true, vertices_268), (true, vertices_276), (true, vertices_388), (true, vertices_772), (true, vertices_392), (true, vertices_304), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 13 else
  if p.val = (false, vertices_227) then 14 else
  if p.val = (false, vertices_541) then 16 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 7 458 194 1
cert_row_4 1 0 1 3 6 7 406 146 1
cert_row_4 2 0 4 5 7 8 866 98 3
cert_row_4 3 1 3 4 7 8 820 276 2
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 1 0 1 3 6 146 406 1
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 194 458 1
cert_coverFacet 2 306
cert_cover_2 2 3 0 4 7 50 306 3
cert_coverFacet 3 866
cert_cover_5 3 2 0 4 5 7 98 866 3
cert_coverFacet 4 396
cert_cover_2 4 2 1 6 7 140 396 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 820
cert_cover_5 6 3 1 3 4 7 276 820 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0267

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m14e10q1_0269.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0269

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 307, 595, 837, 809, 689, 398, 198, 210, 402, 684, 780, 724, 440, 19, 67, 259, 325, 49, 529, 289, 545, 577, 769, 70, 134, 262, 82, 146, 274, 194, 386, 140, 268, 524, 196, 580, 644, 772, 168, 296, 552, 392, 776, 176, 304, 208, 592, 400, 656, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_307, vertices_595, vertices_837, vertices_809, vertices_689, vertices_398, vertices_198, vertices_210, vertices_402, vertices_684, vertices_780, vertices_724, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_259, vertices_325, vertices_49, vertices_529, vertices_289, vertices_545, vertices_577, vertices_769, vertices_70, vertices_134, vertices_262, vertices_82, vertices_146, vertices_274, vertices_194, vertices_386, vertices_140, vertices_268, vertices_524, vertices_196, vertices_580, vertices_644, vertices_772, vertices_168, vertices_296, vertices_552, vertices_392, vertices_776, vertices_176, vertices_304, vertices_208, vertices_592, vertices_400, vertices_656, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_307), (false, vertices_595), (false, vertices_837), (false, vertices_809), (false, vertices_689), (true, vertices_134), (true, vertices_146), (true, vertices_194), (true, vertices_386), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_196), (true, vertices_644), (true, vertices_168), (true, vertices_392), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 17 else
  if p.val = (false, vertices_307) then 14 else
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_4 1 1 3 5 6 8 724 196 1
cert_row_4 2 1 2 4 6 8 684 140 2
cert_row_4 3 2 3 4 6 7 440 168 1
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 210
cert_cover_2 2 3 0 5 6 82 210 3
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 684
cert_cover_5 4 2 1 2 4 6 140 684 2
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 724
cert_cover_5 6 1 1 3 5 6 196 724 1
cert_coverFacet 7 440
cert_cover_5 7 3 2 3 4 6 168 440 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0269

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m14e10q1_0270.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0270

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 541, 405, 837, 665, 481, 558, 234, 650, 866, 316, 804, 408, 424, 21, 261, 517, 537, 145, 193, 321, 577, 385, 641, 42, 138, 522, 98, 546, 194, 578, 642, 28, 44, 524, 276, 292, 548, 772, 152, 280, 168, 296, 392, 648, 400, 224, 352, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_541, vertices_405, vertices_837, vertices_665, vertices_481, vertices_558, vertices_234, vertices_650, vertices_866, vertices_316, vertices_804, vertices_408, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_261, vertices_517, vertices_537, vertices_145, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_42, vertices_138, vertices_522, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_44, vertices_524, vertices_276, vertices_292, vertices_548, vertices_772, vertices_152, vertices_280, vertices_168, vertices_296, vertices_392, vertices_648, vertices_400, vertices_224, vertices_352, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_541), (false, vertices_405), (false, vertices_837), (false, vertices_665), (false, vertices_481), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_98), (true, vertices_546), (true, vertices_44), (true, vertices_292), (true, vertices_548), (true, vertices_280), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_405) then 16 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 6 234 42 3
cert_row_4 1 0 4 5 7 8 866 98 3
cert_row_4 2 0 1 2 4 8 558 42 1
cert_row_4 3 1 2 3 4 7 316 28 3
cert_rows
cert_pivot_2 6 5 0 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 2 0 1 2 4 42 558 1
cert_coverFacet 1 234
cert_cover_5 1 0 0 2 4 5 42 234 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 866
cert_cover_5 3 1 0 4 5 7 98 866 3
cert_coverFacet 4 316
cert_cover_5 4 3 1 2 3 4 28 316 3
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0270

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m14e10q1_0271.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0271

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 531, 355, 771, 661, 841, 737, 542, 314, 778, 124, 716, 244, 360, 19, 35, 259, 515, 145, 529, 97, 161, 321, 577, 641, 769, 26, 266, 522, 50, 530, 290, 770, 28, 76, 524, 116, 148, 532, 196, 644, 56, 104, 296, 328, 584, 776, 176, 224, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_531, vertices_355, vertices_771, vertices_661, vertices_841, vertices_737, vertices_542, vertices_314, vertices_778, vertices_124, vertices_716, vertices_244, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_515, vertices_145, vertices_529, vertices_97, vertices_161, vertices_321, vertices_577, vertices_641, vertices_769, vertices_26, vertices_266, vertices_522, vertices_50, vertices_530, vertices_290, vertices_770, vertices_28, vertices_76, vertices_524, vertices_116, vertices_148, vertices_532, vertices_196, vertices_644, vertices_56, vertices_104, vertices_296, vertices_328, vertices_584, vertices_776, vertices_176, vertices_224, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_531), (false, vertices_355), (false, vertices_771), (false, vertices_661), (false, vertices_841), (false, vertices_737), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_28), (true, vertices_76), (true, vertices_524), (true, vertices_116), (true, vertices_196), (true, vertices_56), (true, vertices_104), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 13 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_355) then 14 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_661) then 16 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (false, vertices_737) then 22 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_116) then 17 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_296) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_116), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 7 314 26 3
cert_row_2 1 1 3 4 5 116
cert_row_4 2 0 1 2 3 8 542 26 1
cert_row_4 3 1 2 5 6 8 716 76 3
cert_rows
cert_pivot_2 7 4 0 1
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 2 0 1 2 3 26 542 1
cert_coverFacet 1 314
cert_cover_5 1 0 0 2 3 4 26 314 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 124
cert_cover_5 3 1 1 2 3 4 28 124 3
cert_coverFacet 4 716
cert_cover_5 4 3 1 2 5 6 76 716 3
cert_coverFacet 5 244
cert_cover_5 5 1 1 3 4 6 116 244 3
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0271

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m14e10q1_0272.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0272

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 787, 547, 397, 677, 713, 777, 602, 370, 738, 236, 364, 344, 792, 35, 259, 515, 37, 133, 261, 137, 265, 521, 545, 641, 769, 82, 274, 530, 98, 290, 546, 578, 108, 140, 268, 164, 292, 88, 280, 536, 200, 328, 584, 776, 336, 784, 224, 352, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_787, vertices_547, vertices_397, vertices_677, vertices_713, vertices_777, vertices_602, vertices_370, vertices_738, vertices_236, vertices_364, vertices_344, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_37, vertices_133, vertices_261, vertices_137, vertices_265, vertices_521, vertices_545, vertices_641, vertices_769, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_578, vertices_108, vertices_140, vertices_268, vertices_164, vertices_292, vertices_88, vertices_280, vertices_536, vertices_200, vertices_328, vertices_584, vertices_776, vertices_336, vertices_784, vertices_224, vertices_352, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_787), (false, vertices_547), (false, vertices_397), (false, vertices_677), (false, vertices_713), (false, vertices_777), (true, vertices_82), (true, vertices_98), (true, vertices_578), (true, vertices_108), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_328), (true, vertices_336), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 13 else
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_397) then 16 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_108) then 18 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 2 3 5 8 602 82 1
cert_row_4 2 0 3 4 5 7 370 82 2
cert_row_4 3 0 4 5 6 8 738 98 3
cert_rows
cert_pivot_2 1 2 3 0
cert_heightProof 4
cert_coverFacet 0 602
cert_cover_5 0 1 0 2 3 5 82 602 1
cert_coverFacet 1 370
cert_cover_5 1 2 0 3 4 5 82 370 2
cert_coverFacet 2 738
cert_cover_5 2 3 0 4 5 6 98 738 3
cert_coverFacet 3 236
cert_cover_5 3 0 1 2 4 6 108 236 3
cert_coverFacet 4 364
cert_cover_5 4 0 1 2 4 7 108 364 3
cert_coverFacet 5 344
cert_cover_2 5 3 2 5 7 88 344 3
cert_coverFacet 6 792
cert_cover_2 6 3 2 7 8 280 792 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0272

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2313 : Certifies 2313 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0179.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2314 : Certifies 2314 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0181.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2315 : Certifies 2315 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0182.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2316 : Certifies 2316 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0188.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2317 : Certifies 2317 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0189.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2318 : Certifies 2318 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0190.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2319 : Certifies 2319 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0206.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2320 : Certifies 2320 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0209.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2321 : Certifies 2321 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0212.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2322 : Certifies 2322 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0213.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2323 : Certifies 2323 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0214.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2324 : Certifies 2324 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0216.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2325 : Certifies 2325 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0219.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2326 : Certifies 2326 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0220.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2327 : Certifies 2327 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0222.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2328 : Certifies 2328 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0226.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2329 : Certifies 2329 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0228.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2330 : Certifies 2330 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0230.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2331 : Certifies 2331 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0248.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2332 : Certifies 2332 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0249.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2333 : Certifies 2333 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0251.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2334 : Certifies 2334 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0261.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2335 : Certifies 2335 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0264.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2336 : Certifies 2336 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0265.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2337 : Certifies 2337 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0266.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2338 : Certifies 2338 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0267.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2339 : Certifies 2339 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0269.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2340 : Certifies 2340 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0270.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2341 : Certifies 2341 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0271.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2342 : Certifies 2342 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0272.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B076 (j : Fin 30) :
    Certifies (2313 + j.val) := by
  fin_cases j
  · exact projection_2313
  · exact projection_2314
  · exact projection_2315
  · exact projection_2316
  · exact projection_2317
  · exact projection_2318
  · exact projection_2319
  · exact projection_2320
  · exact projection_2321
  · exact projection_2322
  · exact projection_2323
  · exact projection_2324
  · exact projection_2325
  · exact projection_2326
  · exact projection_2327
  · exact projection_2328
  · exact projection_2329
  · exact projection_2330
  · exact projection_2331
  · exact projection_2332
  · exact projection_2333
  · exact projection_2334
  · exact projection_2335
  · exact projection_2336
  · exact projection_2337
  · exact projection_2338
  · exact projection_2339
  · exact projection_2340
  · exact projection_2341
  · exact projection_2342

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
