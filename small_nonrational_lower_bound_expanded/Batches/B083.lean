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
/- Source: ProjectionCertificates/R_m14e10q1_0751.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0751

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 397, 341, 709, 689, 401, 334, 590, 570, 426, 306, 338, 684, 432, 69, 133, 261, 81, 145, 273, 529, 577, 385, 641, 78, 42, 266, 522, 50, 82, 274, 530, 290, 322, 578, 140, 268, 524, 324, 580, 644, 168, 552, 392, 176, 304, 560, 336, 400, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_397, vertices_341, vertices_709, vertices_689, vertices_401, vertices_334, vertices_590, vertices_570, vertices_426, vertices_306, vertices_338, vertices_684, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_81, vertices_145, vertices_273, vertices_529, vertices_577, vertices_385, vertices_641, vertices_78, vertices_42, vertices_266, vertices_522, vertices_50, vertices_82, vertices_274, vertices_530, vertices_290, vertices_322, vertices_578, vertices_140, vertices_268, vertices_524, vertices_324, vertices_580, vertices_644, vertices_168, vertices_552, vertices_392, vertices_176, vertices_304, vertices_560, vertices_336, vertices_400, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_397), (false, vertices_341), (false, vertices_709), (false, vertices_689), (false, vertices_401), (true, vertices_78), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_290), (true, vertices_322), (true, vertices_524), (true, vertices_168), (true, vertices_552), (true, vertices_304), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (true, vertices_78) then 15 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
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
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 2 3 4 8 570 42 2
cert_row_4 2 0 2 4 6 7 426 42 3
cert_row_4 3 1 2 4 6 8 684 140 2
cert_rows
cert_pivot_2 5 3 0 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 7 78 334 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 570
cert_cover_5 2 1 0 2 3 4 42 570 2
cert_coverFacet 3 426
cert_cover_5 3 2 0 2 4 6 42 426 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 684
cert_cover_5 6 3 1 2 4 6 140 684 2
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0751

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m14e10q1_0753.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0753

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 397, 341, 709, 625, 657, 654, 570, 298, 394, 370, 658, 812, 868, 69, 133, 261, 81, 145, 273, 529, 577, 385, 641, 42, 138, 266, 522, 50, 146, 274, 530, 290, 386, 642, 140, 268, 524, 804, 324, 580, 644, 296, 552, 392, 112, 560, 336, 656, 352, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_397, vertices_341, vertices_709, vertices_625, vertices_657, vertices_654, vertices_570, vertices_298, vertices_394, vertices_370, vertices_658, vertices_812, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_81, vertices_145, vertices_273, vertices_529, vertices_577, vertices_385, vertices_641, vertices_42, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_530, vertices_290, vertices_386, vertices_642, vertices_140, vertices_268, vertices_524, vertices_804, vertices_324, vertices_580, vertices_644, vertices_296, vertices_552, vertices_392, vertices_112, vertices_560, vertices_336, vertices_656, vertices_352, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_397), (false, vertices_341), (false, vertices_709), (false, vertices_625), (false, vertices_657), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_530), (true, vertices_290), (true, vertices_642), (true, vertices_524), (true, vertices_804), (true, vertices_296), (true, vertices_552), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 15 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 14 else
  if p.val = (false, vertices_397) then 16 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_804) then 20 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_2 1 1 4 7 8 804
cert_row_4 2 0 2 3 4 8 570 42 2
cert_row_4 3 0 3 4 5 7 370 50 3
cert_rows
cert_pivot_2 6 1 2 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 570
cert_cover_5 1 2 0 2 3 4 42 570 2
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 370
cert_cover_5 4 3 0 3 4 5 50 370 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 812
cert_cover_5 6 1 1 2 4 7 268 812 2
cert_coverFacet 7 868
cert_cover_5 7 1 1 4 5 7 804 868 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0753

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m14e10q1_0754.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0754

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 557, 597, 293, 453, 737, 542, 314, 682, 850, 962, 284, 300, 340, 37, 69, 261, 517, 161, 289, 545, 193, 577, 385, 26, 42, 522, 274, 530, 162, 290, 834, 386, 642, 28, 44, 268, 524, 84, 276, 532, 292, 324, 280, 296, 552, 336, 592, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_557, vertices_597, vertices_293, vertices_453, vertices_737, vertices_542, vertices_314, vertices_682, vertices_850, vertices_962, vertices_284, vertices_300, vertices_340] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_26, vertices_42, vertices_522, vertices_274, vertices_530, vertices_162, vertices_290, vertices_834, vertices_386, vertices_642, vertices_28, vertices_44, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_292, vertices_324, vertices_280, vertices_296, vertices_552, vertices_336, vertices_592, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_557), (false, vertices_597), (false, vertices_293), (false, vertices_453), (false, vertices_737), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_834), (true, vertices_642), (true, vertices_28), (true, vertices_268), (true, vertices_276), (true, vertices_280), (true, vertices_296), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 14 else
  if p.val = (false, vertices_557) then 17 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_834) then 15 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_336) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_834), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 20 => Sum.inl 2
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
cert_row_2 0 0 5 7 8 834
cert_row_4 1 0 1 2 3 8 542 26 1
cert_row_4 2 0 2 3 4 7 314 26 3
cert_row_4 3 0 2 4 6 8 682 42 3
cert_rows
cert_pivot_2 5 1 3 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 1 0 1 2 3 26 542 1
cert_coverFacet 1 314
cert_cover_5 1 2 0 2 3 4 26 314 3
cert_coverFacet 2 682
cert_cover_5 2 3 0 2 4 6 42 682 3
cert_coverFacet 3 850
cert_cover_5 3 0 0 3 5 7 274 850 2
cert_coverFacet 4 962
cert_cover_5 4 0 0 5 6 7 834 962 2
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0754

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m14e10q1_0758.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0758

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 421, 901, 313, 665, 233, 662, 230, 326, 774, 346, 210, 364, 216, 389, 25, 41, 137, 273, 529, 161, 289, 641, 769, 70, 134, 262, 518, 82, 146, 274, 530, 194, 322, 770, 100, 164, 292, 324, 644, 772, 88, 152, 280, 104, 296, 200, 328, 208, 656, 224]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_421, vertices_901, vertices_313, vertices_665, vertices_233, vertices_662, vertices_230, vertices_326, vertices_774, vertices_346, vertices_210, vertices_364, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_389, vertices_25, vertices_41, vertices_137, vertices_273, vertices_529, vertices_161, vertices_289, vertices_641, vertices_769, vertices_70, vertices_134, vertices_262, vertices_518, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_770, vertices_100, vertices_164, vertices_292, vertices_324, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_104, vertices_296, vertices_200, vertices_328, vertices_208, vertices_656, vertices_224] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_421), (false, vertices_901), (false, vertices_313), (false, vertices_665), (false, vertices_233), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_322), (true, vertices_100), (true, vertices_324), (true, vertices_88), (true, vertices_328), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_421) then 16 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_313) then 19 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_208) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 134 2
cert_row_4 1 0 1 4 5 6 230 70 2
cert_row_4 2 0 2 3 5 7 346 82 1
cert_row_4 3 1 2 4 5 7 364 100 1
cert_rows
cert_pivot_2 8 6 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 134 662 2
cert_coverFacet 1 230
cert_cover_5 1 1 0 1 4 5 70 230 2
cert_coverFacet 2 326
cert_cover_2 2 1 0 5 7 70 326 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 346
cert_cover_5 4 2 0 2 3 5 82 346 1
cert_coverFacet 5 210
cert_cover_2 5 3 0 5 6 82 210 3
cert_coverFacet 6 364
cert_cover_5 6 3 1 2 4 5 100 364 1
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0758

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m14e10q1_0759.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0759

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 899, 397, 229, 805, 625, 782, 602, 154, 394, 242, 572, 172, 184, 643, 37, 133, 261, 97, 545, 193, 577, 385, 769, 26, 138, 266, 522, 82, 146, 194, 578, 386, 770, 44, 140, 268, 524, 164, 548, 772, 56, 152, 536, 168, 392, 112, 176, 560, 592, 224]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_899, vertices_397, vertices_229, vertices_805, vertices_625, vertices_782, vertices_602, vertices_154, vertices_394, vertices_242, vertices_572, vertices_172, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_643, vertices_37, vertices_133, vertices_261, vertices_97, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_82, vertices_146, vertices_194, vertices_578, vertices_386, vertices_770, vertices_44, vertices_140, vertices_268, vertices_524, vertices_164, vertices_548, vertices_772, vertices_56, vertices_152, vertices_536, vertices_168, vertices_392, vertices_112, vertices_176, vertices_560, vertices_592, vertices_224] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_899), (false, vertices_397), (false, vertices_229), (false, vertices_805), (false, vertices_625), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_82), (true, vertices_146), (true, vertices_44), (true, vertices_524), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_168), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_176) then 12 else
  0
cert_priority
cert_nodeAtPriority_30 0 26 1 138 266 522 82 146 44 524 56 152 536 168 176 707 899 397 229 805 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 0 3 4 5 6 242 82 2
cert_row_4 2 0 2 3 5 8 602 26 3
cert_row_4 3 1 2 3 4 8 572 44 2
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 602
cert_cover_5 1 2 0 2 3 5 26 602 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 242
cert_cover_5 4 1 0 3 4 5 82 242 2
cert_coverFacet 5 572
cert_cover_5 5 3 1 2 3 4 44 572 2
cert_coverFacet 6 172
cert_cover_2 6 2 1 4 6 44 172 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0759

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m14e10q1_0761.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0761

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 589, 233, 777, 433, 961, 542, 110, 118, 778, 306, 914, 596, 752, 41, 73, 265, 521, 161, 289, 193, 577, 385, 769, 14, 22, 102, 42, 266, 522, 50, 274, 530, 290, 770, 76, 524, 84, 532, 580, 104, 776, 112, 176, 304, 592, 400, 656, 224, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_589, vertices_233, vertices_777, vertices_433, vertices_961, vertices_542, vertices_110, vertices_118, vertices_778, vertices_306, vertices_914, vertices_596, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_22, vertices_102, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_290, vertices_770, vertices_76, vertices_524, vertices_84, vertices_532, vertices_580, vertices_104, vertices_776, vertices_112, vertices_176, vertices_304, vertices_592, vertices_400, vertices_656, vertices_224, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_589), (false, vertices_233), (false, vertices_777), (false, vertices_433), (false, vertices_961), (true, vertices_14), (true, vertices_22), (true, vertices_102), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_770), (true, vertices_84), (true, vertices_532), (true, vertices_112), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 14 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_102) then 15 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_656) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 14 3
cert_row_2 1 0 1 4 5 102
cert_row_4 2 0 3 6 7 8 914 274 2
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 14 542 3
cert_coverFacet 1 110
cert_cover_5 1 1 0 1 2 4 14 110 3
cert_coverFacet 2 118
cert_cover_5 2 1 0 1 3 4 22 118 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 914
cert_cover_5 5 2 0 3 6 7 274 914 2
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0761

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m14e10q1_0762.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0762

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [15, 551, 395, 659, 45, 361, 929, 158, 598, 220, 108, 868, 968, 720, 7, 11, 131, 515, 13, 37, 41, 265, 289, 545, 385, 641, 14, 22, 518, 138, 146, 530, 156, 44, 76, 84, 100, 548, 580, 104, 200, 328, 392, 208, 592, 656, 352, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_15, vertices_551, vertices_395, vertices_659, vertices_45, vertices_361, vertices_929, vertices_158, vertices_598, vertices_220, vertices_108, vertices_868, vertices_968, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_515, vertices_13, vertices_37, vertices_41, vertices_265, vertices_289, vertices_545, vertices_385, vertices_641, vertices_14, vertices_22, vertices_518, vertices_138, vertices_146, vertices_530, vertices_156, vertices_44, vertices_76, vertices_84, vertices_100, vertices_548, vertices_580, vertices_104, vertices_200, vertices_328, vertices_392, vertices_208, vertices_592, vertices_656, vertices_352, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_15), (false, vertices_551), (false, vertices_395), (false, vertices_659), (false, vertices_45), (false, vertices_361), (false, vertices_929), (true, vertices_22), (true, vertices_156), (true, vertices_76), (true, vertices_84), (true, vertices_100), (true, vertices_580), (true, vertices_200), (true, vertices_208), (true, vertices_592), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_15) then 0 else
  if p.val = (false, vertices_551) then 13 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_45) then 1 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_929) then 22 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_156) then 17 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_15), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_4 0 0 1 3 5 8 598 22 3
cert_row_2 1 1 2 3 6 156
cert_row_4 2 1 4 5 7 8 868 100 3
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 14 158 3
cert_coverFacet 1 598
cert_cover_5 1 0 0 1 3 5 22 598 3
cert_coverFacet 2 220
cert_cover_5 2 1 1 2 3 5 156 220 3
cert_coverFacet 3 108
cert_cover_2 3 2 1 4 5 44 108 3
cert_coverFacet 4 868
cert_cover_5 4 2 1 4 5 7 100 868 3
cert_coverFacet 5 968
cert_cover_5 5 3 2 5 6 7 200 968 3
cert_coverFacet 6 720
cert_cover_2 6 5 3 6 8 208 720 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0762

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m14e10q1_0764.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0764

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 535, 779, 419, 241, 913, 590, 270, 294, 364, 116, 724, 840, 992, 23, 35, 259, 515, 49, 145, 529, 161, 385, 769, 14, 38, 262, 518, 266, 522, 290, 76, 268, 52, 84, 532, 100, 292, 580, 328, 584, 776, 112, 208, 656, 224, 352, 416, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_535, vertices_779, vertices_419, vertices_241, vertices_913, vertices_590, vertices_270, vertices_294, vertices_364, vertices_116, vertices_724, vertices_840, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_35, vertices_259, vertices_515, vertices_49, vertices_145, vertices_529, vertices_161, vertices_385, vertices_769, vertices_14, vertices_38, vertices_262, vertices_518, vertices_266, vertices_522, vertices_290, vertices_76, vertices_268, vertices_52, vertices_84, vertices_532, vertices_100, vertices_292, vertices_580, vertices_328, vertices_584, vertices_776, vertices_112, vertices_208, vertices_656, vertices_224, vertices_352, vertices_416, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_535), (false, vertices_779), (false, vertices_419), (false, vertices_241), (false, vertices_913), (true, vertices_14), (true, vertices_262), (true, vertices_76), (true, vertices_268), (true, vertices_84), (true, vertices_100), (true, vertices_292), (true, vertices_580), (true, vertices_328), (true, vertices_584), (true, vertices_352), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 19 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 14 else
  if p.val = (false, vertices_535) then 15 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_419) then 18 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (false, vertices_913) then 22 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 5 7 364 76 2
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 2 1 4
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 294
cert_cover_2 2 1 0 4 7 38 294 3
cert_coverFacet 3 364
cert_cover_5 3 1 1 2 4 5 76 364 2
cert_coverFacet 4 116
cert_cover_2 4 3 1 4 5 52 116 3
cert_coverFacet 5 724
cert_cover_5 5 2 1 3 5 6 84 724 3
cert_coverFacet 6 840
cert_cover_2 6 5 2 7 8 328 840 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0764

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m14e10q1_0765.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0765

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 535, 357, 677, 345, 625, 654, 422, 602, 282, 394, 872, 424, 680, 23, 37, 261, 517, 81, 273, 529, 97, 545, 321, 134, 262, 518, 26, 138, 266, 522, 274, 530, 386, 164, 292, 644, 88, 280, 168, 296, 552, 328, 584, 392, 648, 592, 352, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_535, vertices_357, vertices_677, vertices_345, vertices_625, vertices_654, vertices_422, vertices_602, vertices_282, vertices_394, vertices_872, vertices_424, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_37, vertices_261, vertices_517, vertices_81, vertices_273, vertices_529, vertices_97, vertices_545, vertices_321, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_386, vertices_164, vertices_292, vertices_644, vertices_88, vertices_280, vertices_168, vertices_296, vertices_552, vertices_328, vertices_584, vertices_392, vertices_648, vertices_592, vertices_352, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_535), (false, vertices_357), (false, vertices_677), (false, vertices_345), (false, vertices_625), (true, vertices_134), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_386), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_584), (true, vertices_392), (true, vertices_648), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 14 else
  if p.val = (false, vertices_535) then 15 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_4 1 2 4 5 7 8 872 296 2
cert_row_4 2 0 1 2 6 8 654 134 2
cert_row_4 3 0 1 4 6 7 422 134 2
cert_rows
cert_pivot_2 3 5 2 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 134 654 2
cert_coverFacet 1 422
cert_cover_5 1 3 0 1 4 6 134 422 2
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 5 26 602 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 872
cert_cover_5 5 1 2 4 5 7 296 872 2
cert_coverFacet 6 424
cert_cover_2 6 4 2 6 7 168 424 3
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0765

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m14e10q1_0766.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0766

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 397, 313, 665, 625, 801, 654, 614, 326, 390, 370, 802, 348, 604, 25, 137, 265, 49, 529, 289, 545, 385, 641, 769, 70, 134, 262, 518, 98, 290, 546, 322, 386, 642, 770, 92, 140, 268, 524, 324, 580, 388, 280, 536, 648, 112, 304, 336, 592, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_397, vertices_313, vertices_665, vertices_625, vertices_801, vertices_654, vertices_614, vertices_326, vertices_390, vertices_370, vertices_802, vertices_348, vertices_604] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_49, vertices_529, vertices_289, vertices_545, vertices_385, vertices_641, vertices_769, vertices_70, vertices_134, vertices_262, vertices_518, vertices_98, vertices_290, vertices_546, vertices_322, vertices_386, vertices_642, vertices_770, vertices_92, vertices_140, vertices_268, vertices_524, vertices_324, vertices_580, vertices_388, vertices_280, vertices_536, vertices_648, vertices_112, vertices_304, vertices_336, vertices_592, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_397), (false, vertices_313), (false, vertices_665), (false, vertices_625), (false, vertices_801), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_92), (true, vertices_524), (true, vertices_324), (true, vertices_580), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_397) then 16 else
  if p.val = (false, vertices_313) then 19 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_92) then 17 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_336) then 12 else
  0
cert_priority
cert_nodeAtPriority_2 0 801 1 70 2 134 3 262 518 98 290 546 322 524 324 580 336 899 397 92 313 665 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 134 2
cert_row_2 1 1 2 3 5 92
cert_row_4 2 0 1 4 5 8 614 70 2
cert_row_4 3 0 3 4 5 7 370 98 1
cert_rows
cert_pivot_2 6 2 1 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 134 654 2
cert_coverFacet 1 614
cert_cover_5 1 2 0 1 4 5 70 614 2
cert_coverFacet 2 326
cert_cover_2 2 1 0 5 7 70 326 3
cert_coverFacet 3 390
cert_cover_2 3 1 0 6 7 134 390 3
cert_coverFacet 4 370
cert_cover_5 4 3 0 3 4 5 98 370 1
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 348
cert_cover_5 6 1 1 2 3 7 92 348 3
cert_coverFacet 7 604
cert_cover_5 7 1 1 2 3 8 92 604 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0766

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m14e10q1_0770.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0770

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 29, 301, 149, 453, 569, 929, 158, 206, 602, 962, 108, 868, 616, 13, 21, 133, 261, 25, 41, 145, 529, 289, 545, 385, 641, 142, 26, 74, 146, 530, 194, 578, 642, 28, 44, 76, 148, 100, 292, 196, 324, 536, 104, 552, 584, 608, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_29, vertices_301, vertices_149, vertices_453, vertices_569, vertices_929, vertices_158, vertices_206, vertices_602, vertices_962, vertices_108, vertices_868, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_133, vertices_261, vertices_25, vertices_41, vertices_145, vertices_529, vertices_289, vertices_545, vertices_385, vertices_641, vertices_142, vertices_26, vertices_74, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_28, vertices_44, vertices_76, vertices_148, vertices_100, vertices_292, vertices_196, vertices_324, vertices_536, vertices_104, vertices_552, vertices_584, vertices_608, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_29), (false, vertices_301), (false, vertices_149), (false, vertices_453), (false, vertices_569), (false, vertices_929), (true, vertices_142), (true, vertices_26), (true, vertices_74), (true, vertices_194), (true, vertices_578), (true, vertices_76), (true, vertices_100), (true, vertices_104), (true, vertices_584), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 13 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_301) then 16 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_453) then 17 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_929) then 22 else
  if p.val = (true, vertices_142) then 14 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_29), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_142), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
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
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_2 1 0 1 2 6 142
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 142 158 3
cert_coverFacet 1 206
cert_cover_5 1 1 0 1 2 5 142 206 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 5 26 602 3
cert_coverFacet 3 962
cert_cover_5 3 2 0 5 6 7 194 962 3
cert_coverFacet 4 108
cert_cover_2 4 2 1 4 5 44 108 3
cert_coverFacet 5 868
cert_cover_5 5 3 1 4 5 7 100 868 3
cert_coverFacet 6 616
cert_cover_2 6 4 2 5 8 104 616 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0770

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m14e10q1_0771.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0771

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 355, 675, 421, 665, 337, 401, 838, 802, 604, 684, 460, 804, 472, 35, 67, 515, 81, 145, 273, 529, 161, 289, 321, 385, 641, 290, 546, 322, 578, 770, 76, 140, 524, 164, 292, 548, 324, 580, 388, 772, 88, 152, 536, 456, 648, 336, 592, 400, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_355, vertices_675, vertices_421, vertices_665, vertices_337, vertices_401, vertices_838, vertices_802, vertices_604, vertices_684, vertices_460, vertices_804, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_515, vertices_81, vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_321, vertices_385, vertices_641, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_76, vertices_140, vertices_524, vertices_164, vertices_292, vertices_548, vertices_324, vertices_580, vertices_388, vertices_772, vertices_88, vertices_152, vertices_536, vertices_456, vertices_648, vertices_336, vertices_592, vertices_400, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_355), (false, vertices_675), (false, vertices_421), (false, vertices_665), (false, vertices_337), (false, vertices_401), (true, vertices_770), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_548), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_88), (true, vertices_456), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 13 else
  if p.val = (false, vertices_355) then 14 else
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_665) then 19 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_456) then 20 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_456), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 7 8 838 322 1
cert_row_2 1 2 5 6 7 456
cert_row_4 2 1 2 3 5 8 604 76 2
cert_row_4 3 1 2 4 6 8 684 140 2
cert_rows
cert_pivot_2 0 7 3 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 0 0 1 5 7 322 838 1
cert_coverFacet 1 802
cert_cover_2 1 4 0 7 8 290 802 3
cert_coverFacet 2 604
cert_cover_5 2 2 1 2 3 5 76 604 2
cert_coverFacet 3 684
cert_cover_5 3 3 1 2 4 6 140 684 2
cert_coverFacet 4 460
cert_cover_5 4 1 1 2 5 6 76 460 3
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coverFacet 6 472
cert_cover_5 6 1 2 3 5 6 88 472 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0771

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m14e10q1_0772.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0772

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 397, 661, 773, 625, 433, 782, 218, 410, 618, 114, 306, 716, 720, 133, 261, 517, 49, 145, 529, 289, 545, 385, 769, 154, 74, 266, 522, 50, 82, 274, 98, 290, 546, 770, 140, 268, 524, 644, 772, 200, 584, 392, 112, 304, 208, 592, 400, 656, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_397, vertices_661, vertices_773, vertices_625, vertices_433, vertices_782, vertices_218, vertices_410, vertices_618, vertices_114, vertices_306, vertices_716, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_49, vertices_145, vertices_529, vertices_289, vertices_545, vertices_385, vertices_769, vertices_154, vertices_74, vertices_266, vertices_522, vertices_50, vertices_82, vertices_274, vertices_98, vertices_290, vertices_546, vertices_770, vertices_140, vertices_268, vertices_524, vertices_644, vertices_772, vertices_200, vertices_584, vertices_392, vertices_112, vertices_304, vertices_208, vertices_592, vertices_400, vertices_656, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_397), (false, vertices_661), (false, vertices_773), (false, vertices_625), (false, vertices_433), (true, vertices_154), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_98), (true, vertices_524), (true, vertices_200), (true, vertices_584), (true, vertices_208), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (true, vertices_154) then 15 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 2 4 5 8 618 74 2
cert_row_4 3 1 2 5 6 8 716 140 2
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 5 154 218 3
cert_coverFacet 2 410
cert_cover_5 2 0 0 2 3 7 154 410 3
cert_coverFacet 3 618
cert_cover_5 3 2 0 2 4 5 74 618 2
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 306
cert_cover_2 5 3 0 4 7 50 306 3
cert_coverFacet 6 716
cert_cover_5 6 3 1 2 5 6 140 716 2
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0772

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m14e10q1_0773.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0773

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 397, 789, 645, 433, 737, 782, 218, 410, 618, 114, 786, 716, 240, 133, 261, 517, 49, 273, 529, 161, 545, 385, 641, 154, 74, 266, 522, 50, 82, 274, 530, 98, 546, 770, 140, 268, 524, 644, 772, 200, 584, 392, 112, 176, 208, 400, 784, 224, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_397, vertices_789, vertices_645, vertices_433, vertices_737, vertices_782, vertices_218, vertices_410, vertices_618, vertices_114, vertices_786, vertices_716, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_161, vertices_545, vertices_385, vertices_641, vertices_154, vertices_74, vertices_266, vertices_522, vertices_50, vertices_82, vertices_274, vertices_530, vertices_98, vertices_546, vertices_770, vertices_140, vertices_268, vertices_524, vertices_644, vertices_772, vertices_200, vertices_584, vertices_392, vertices_112, vertices_176, vertices_208, vertices_400, vertices_784, vertices_224, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_397), (false, vertices_789), (false, vertices_645), (false, vertices_433), (false, vertices_737), (true, vertices_154), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_82), (true, vertices_274), (true, vertices_98), (true, vertices_770), (true, vertices_524), (true, vertices_200), (true, vertices_584), (true, vertices_112), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_154) then 15 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_208) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_645), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 2 4 5 8 618 74 2
cert_row_4 3 1 2 5 6 8 716 140 2
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 5 154 218 3
cert_coverFacet 2 410
cert_cover_5 2 0 0 2 3 7 154 410 3
cert_coverFacet 3 618
cert_cover_5 3 2 0 2 4 5 74 618 2
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 716
cert_cover_5 6 3 1 2 5 6 140 716 2
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0773

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m14e10q1_0778.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0778

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 595, 147, 589, 405, 325, 369, 682, 434, 562, 236, 652, 484, 632, 19, 131, 515, 69, 133, 261, 517, 81, 145, 273, 321, 577, 50, 146, 530, 162, 546, 642, 76, 140, 524, 228, 324, 388, 644, 104, 168, 552, 584, 648, 112, 304, 560, 592, 400, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_595, vertices_147, vertices_589, vertices_405, vertices_325, vertices_369, vertices_682, vertices_434, vertices_562, vertices_236, vertices_652, vertices_484, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_515, vertices_69, vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_273, vertices_321, vertices_577, vertices_50, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_76, vertices_140, vertices_524, vertices_228, vertices_324, vertices_388, vertices_644, vertices_104, vertices_168, vertices_552, vertices_584, vertices_648, vertices_112, vertices_304, vertices_560, vertices_592, vertices_400, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_595), (false, vertices_147), (false, vertices_589), (false, vertices_405), (false, vertices_325), (false, vertices_369), (true, vertices_50), (true, vertices_162), (true, vertices_546), (true, vertices_140), (true, vertices_228), (true, vertices_104), (true, vertices_168), (true, vertices_552), (true, vertices_648), (true, vertices_560), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_589) then 16 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_325) then 1 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_228) then 18 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_228), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 6 228
cert_row_4 1 0 3 4 6 7 434 50 3
cert_row_4 2 0 2 4 6 8 682 162 1
cert_row_4 3 2 3 4 5 8 632 104 1
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 682
cert_cover_5 0 2 0 2 4 6 162 682 1
cert_coverFacet 1 434
cert_cover_5 1 1 0 3 4 6 50 434 3
cert_coverFacet 2 562
cert_cover_2 2 3 0 4 8 50 562 3
cert_coverFacet 3 236
cert_cover_5 3 0 1 2 4 5 76 236 2
cert_coverFacet 4 652
cert_cover_2 4 2 1 6 8 140 652 3
cert_coverFacet 5 484
cert_cover_5 5 0 1 4 5 7 228 484 3
cert_coverFacet 6 632
cert_cover_5 6 3 2 3 4 5 104 632 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0778

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m14e10q1_0779.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0779

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 147, 419, 771, 837, 185, 369, 902, 666, 604, 236, 652, 484, 120, 19, 131, 259, 515, 49, 81, 145, 161, 289, 321, 577, 769, 146, 530, 386, 642, 770, 76, 140, 524, 228, 324, 580, 388, 644, 772, 56, 88, 152, 536, 104, 168, 648, 112, 592, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_147, vertices_419, vertices_771, vertices_837, vertices_185, vertices_369, vertices_902, vertices_666, vertices_604, vertices_236, vertices_652, vertices_484, vertices_120] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_49, vertices_81, vertices_145, vertices_161, vertices_289, vertices_321, vertices_577, vertices_769, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_228, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_536, vertices_104, vertices_168, vertices_648, vertices_112, vertices_592, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_147), (false, vertices_419), (false, vertices_771), (false, vertices_837), (false, vertices_185), (false, vertices_369), (true, vertices_642), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_228), (true, vertices_388), (true, vertices_644), (true, vertices_88), (true, vertices_536), (true, vertices_104), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 13 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_419) then 14 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_185) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_228) then 17 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_648) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_228), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 6 228
cert_row_4 1 0 1 6 7 8 902 386 1
cert_row_4 2 0 2 3 6 8 666 146 1
cert_row_4 3 1 2 3 5 8 604 76 2
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 666
cert_cover_5 1 2 0 2 3 6 146 666 1
cert_coverFacet 2 604
cert_cover_5 2 3 1 2 3 5 76 604 2
cert_coverFacet 3 236
cert_cover_5 3 0 1 2 4 5 76 236 2
cert_coverFacet 4 652
cert_cover_2 4 2 1 6 8 140 652 3
cert_coverFacet 5 484
cert_cover_5 5 0 1 4 5 7 228 484 3
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0779

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m14e10q1_0783.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0783

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 659, 451, 709, 569, 329, 585, 806, 902, 306, 562, 620, 484, 376, 19, 131, 259, 25, 73, 265, 521, 529, 193, 321, 577, 641, 774, 50, 274, 530, 290, 546, 386, 642, 100, 292, 548, 196, 580, 388, 644, 56, 280, 104, 552, 328, 584, 304, 560, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_659, vertices_451, vertices_709, vertices_569, vertices_329, vertices_585, vertices_806, vertices_902, vertices_306, vertices_562, vertices_620, vertices_484, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_25, vertices_73, vertices_265, vertices_521, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_774, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_100, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_644, vertices_56, vertices_280, vertices_104, vertices_552, vertices_328, vertices_584, vertices_304, vertices_560, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_659), (false, vertices_451), (false, vertices_709), (false, vertices_569), (false, vertices_329), (false, vertices_585), (true, vertices_774), (true, vertices_50), (true, vertices_290), (true, vertices_546), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_388), (true, vertices_104), (true, vertices_304), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 16 else
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_451) then 18 else
  if p.val = (false, vertices_709) then 13 else
  if p.val = (false, vertices_569) then 20 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_585) then 1 else
  if p.val = (true, vertices_774) then 14 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 1 2 4 5 8 620 100 1
cert_row_4 2 1 4 5 6 7 484 100 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 774 806 2
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 774 902 2
cert_coverFacet 2 306
cert_cover_2 2 3 0 4 7 50 306 3
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 620
cert_cover_5 4 1 1 2 4 5 100 620 1
cert_coverFacet 5 484
cert_cover_5 5 2 1 4 5 6 100 484 3
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 56 376 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0783

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m14e10q1_0788.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0788

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 527, 357, 677, 345, 617, 662, 390, 602, 282, 434, 420, 880, 688, 15, 37, 261, 517, 73, 265, 521, 97, 545, 321, 134, 262, 518, 26, 266, 522, 146, 274, 530, 386, 164, 292, 388, 644, 88, 280, 584, 176, 304, 560, 336, 592, 656, 352, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_527, vertices_357, vertices_677, vertices_345, vertices_617, vertices_662, vertices_390, vertices_602, vertices_282, vertices_434, vertices_420, vertices_880, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_15, vertices_37, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_97, vertices_545, vertices_321, vertices_134, vertices_262, vertices_518, vertices_26, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_164, vertices_292, vertices_388, vertices_644, vertices_88, vertices_280, vertices_584, vertices_176, vertices_304, vertices_560, vertices_336, vertices_592, vertices_656, vertices_352, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_527), (false, vertices_357), (false, vertices_677), (false, vertices_345), (false, vertices_617), (true, vertices_134), (true, vertices_26), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_388), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_592), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 14 else
  if p.val = (false, vertices_527) then 15 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
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
cert_row_4 0 0 1 3 6 8 662 134 2
cert_row_4 1 0 2 3 5 8 602 26 3
cert_row_4 2 0 3 4 6 7 434 146 2
cert_row_4 3 3 4 5 7 8 880 304 2
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 134 662 2
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 602
cert_cover_5 2 1 0 2 3 5 26 602 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 434
cert_cover_5 4 2 0 3 4 6 146 434 2
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 304 880 2
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0788

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m14e10q1_0790.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0790

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 565, 149, 421, 361, 553, 905, 214, 598, 842, 482, 898, 620, 228, 21, 37, 133, 41, 265, 521, 145, 529, 289, 545, 385, 641, 86, 146, 530, 194, 322, 578, 386, 642, 770, 148, 532, 100, 164, 548, 196, 580, 104, 552, 328, 584, 776, 224, 352, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_565, vertices_149, vertices_421, vertices_361, vertices_553, vertices_905, vertices_214, vertices_598, vertices_842, vertices_482, vertices_898, vertices_620, vertices_228] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_133, vertices_41, vertices_265, vertices_521, vertices_145, vertices_529, vertices_289, vertices_545, vertices_385, vertices_641, vertices_86, vertices_146, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_104, vertices_552, vertices_328, vertices_584, vertices_776, vertices_224, vertices_352, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_565), (false, vertices_149), (false, vertices_421), (false, vertices_361), (false, vertices_553), (false, vertices_905), (true, vertices_86), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_770), (true, vertices_100), (true, vertices_196), (true, vertices_580), (true, vertices_584), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 13 else
  if p.val = (false, vertices_565) then 16 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_905) then 20 else
  if p.val = (true, vertices_86) then 14 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
cert_nodeAtPriority_10 0 149 1 553 194 322 578 386 770 100 196 580 584 224 659 86 565 421 361 905
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 4 5 6 7 482 194 1
cert_row_4 2 0 2 5 7 8 842 322 1
cert_row_4 3 1 2 4 5 8 620 100 1
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 6 86 214 3
cert_coverFacet 1 598
cert_cover_5 1 0 0 1 3 8 86 598 3
cert_coverFacet 2 842
cert_cover_5 2 2 0 2 5 7 322 842 1
cert_coverFacet 3 482
cert_cover_5 3 1 0 4 5 6 194 482 1
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 620
cert_cover_5 5 3 1 2 4 5 100 620 1
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0790

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m14e10q1_0794.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0794

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 403, 355, 611, 589, 341, 149, 682, 418, 188, 92, 652, 632, 496, 99, 131, 259, 515, 21, 69, 133, 517, 145, 273, 321, 577, 162, 290, 546, 386, 642, 28, 76, 140, 524, 84, 148, 644, 56, 88, 168, 552, 584, 648, 112, 176, 336, 400, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_403, vertices_355, vertices_611, vertices_589, vertices_341, vertices_149, vertices_682, vertices_418, vertices_188, vertices_92, vertices_652, vertices_632, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_99, vertices_131, vertices_259, vertices_515, vertices_21, vertices_69, vertices_133, vertices_517, vertices_145, vertices_273, vertices_321, vertices_577, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_28, vertices_76, vertices_140, vertices_524, vertices_84, vertices_148, vertices_644, vertices_56, vertices_88, vertices_168, vertices_552, vertices_584, vertices_648, vertices_112, vertices_176, vertices_336, vertices_400, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_403), (false, vertices_355), (false, vertices_611), (false, vertices_589), (false, vertices_341), (false, vertices_149), (true, vertices_162), (true, vertices_28), (true, vertices_140), (true, vertices_56), (true, vertices_88), (true, vertices_168), (true, vertices_552), (true, vertices_648), (true, vertices_112), (true, vertices_176), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 12 20 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_403) then 17 else
  if p.val = (false, vertices_355) then 18 else
  if p.val = (false, vertices_611) then 19 else
  if p.val = (false, vertices_589) then 14 else
  if p.val = (false, vertices_341) then 15 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_56) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 162 1
cert_row_4 1 1 2 3 4 6 188 28 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 682
cert_cover_5 0 0 0 2 4 6 162 682 1
cert_coverFacet 1 418
cert_cover_2 1 4 0 6 7 162 418 3
cert_coverFacet 2 188
cert_cover_5 2 1 1 2 3 4 28 188 3
cert_coverFacet 3 92
cert_cover_2 3 2 1 3 5 28 92 3
cert_coverFacet 4 652
cert_cover_2 4 2 1 6 8 140 652 3
cert_coverFacet 5 632
cert_cover_5 5 2 2 3 4 5 56 632 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0794

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m14e10q1_0795.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0795

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 523, 595, 323, 341, 681, 913, 358, 618, 298, 428, 244, 404, 752, 11, 67, 259, 515, 137, 521, 81, 273, 529, 321, 385, 641, 42, 266, 522, 98, 290, 322, 578, 84, 148, 276, 100, 164, 292, 324, 388, 168, 296, 552, 392, 240, 592, 400, 656, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_523, vertices_595, vertices_323, vertices_341, vertices_681, vertices_913, vertices_358, vertices_618, vertices_298, vertices_428, vertices_244, vertices_404, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_259, vertices_515, vertices_137, vertices_521, vertices_81, vertices_273, vertices_529, vertices_321, vertices_385, vertices_641, vertices_42, vertices_266, vertices_522, vertices_98, vertices_290, vertices_322, vertices_578, vertices_84, vertices_148, vertices_276, vertices_100, vertices_164, vertices_292, vertices_324, vertices_388, vertices_168, vertices_296, vertices_552, vertices_392, vertices_240, vertices_592, vertices_400, vertices_656, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_523), (false, vertices_595), (false, vertices_323), (false, vertices_341), (false, vertices_681), (false, vertices_913), (true, vertices_42), (true, vertices_98), (true, vertices_290), (true, vertices_148), (true, vertices_100), (true, vertices_164), (true, vertices_292), (true, vertices_388), (true, vertices_296), (true, vertices_240), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_323) then 1 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_681) then 18 else
  if p.val = (false, vertices_913) then 20 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_240) then 21 else
  if p.val = (true, vertices_608) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 6 240
cert_row_4 1 0 2 4 5 8 618 42 3
cert_row_4 2 0 1 4 5 7 358 98 1
cert_row_4 3 1 2 4 6 7 428 164 1
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 2 0 1 4 5 98 358 1
cert_coverFacet 1 618
cert_cover_5 1 1 0 2 4 5 42 618 3
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 428
cert_cover_5 3 3 1 2 4 6 164 428 1
cert_coverFacet 4 244
cert_cover_5 4 0 1 3 4 5 84 244 2
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 752
cert_cover_5 6 0 3 4 5 8 240 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0795

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m14e10q1_0796.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0796

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 675, 653, 569, 409, 369, 710, 618, 466, 354, 124, 156, 588, 212, 163, 25, 137, 521, 49, 273, 289, 545, 385, 641, 98, 290, 546, 194, 322, 578, 386, 642, 28, 76, 140, 524, 84, 148, 196, 580, 644, 56, 152, 104, 552, 584, 112, 208, 336, 400, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_675, vertices_653, vertices_569, vertices_409, vertices_369, vertices_710, vertices_618, vertices_466, vertices_354, vertices_124, vertices_156, vertices_588, vertices_212] (by decide +kernel)
  polygons := literalFinset [vertices_163, vertices_25, vertices_137, vertices_521, vertices_49, vertices_273, vertices_289, vertices_545, vertices_385, vertices_641, vertices_98, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_28, vertices_76, vertices_140, vertices_524, vertices_84, vertices_148, vertices_196, vertices_580, vertices_644, vertices_56, vertices_152, vertices_104, vertices_552, vertices_584, vertices_112, vertices_208, vertices_336, vertices_400, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_675), (false, vertices_653), (false, vertices_569), (false, vertices_409), (false, vertices_369), (true, vertices_98), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_28), (true, vertices_76), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_580), (true, vertices_104), (true, vertices_584), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 14 else
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_208) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 7 466 194 1
cert_row_4 1 0 1 5 6 8 710 194 1
cert_row_4 2 0 2 4 5 8 618 98 1
cert_row_4 3 1 2 3 4 5 124 28 3
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 1 0 1 5 6 194 710 1
cert_coverFacet 1 618
cert_cover_5 1 2 0 2 4 5 98 618 1
cert_coverFacet 2 466
cert_cover_5 2 0 0 3 5 6 194 466 1
cert_coverFacet 3 354
cert_cover_2 3 4 0 5 7 98 354 3
cert_coverFacet 4 124
cert_cover_5 4 3 1 2 3 4 28 124 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 588
cert_cover_2 6 2 1 5 8 76 588 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0796

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m14e10q1_0797.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0797

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 523, 675, 291, 357, 665, 233, 806, 778, 796, 628, 340, 472, 752, 11, 35, 259, 515, 73, 137, 521, 97, 161, 289, 321, 641, 266, 522, 290, 546, 770, 84, 276, 532, 100, 292, 548, 324, 772, 152, 280, 536, 200, 328, 776, 624, 208, 336, 656, 224, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_523, vertices_675, vertices_291, vertices_357, vertices_665, vertices_233, vertices_806, vertices_778, vertices_796, vertices_628, vertices_340, vertices_472, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_515, vertices_73, vertices_137, vertices_521, vertices_97, vertices_161, vertices_289, vertices_321, vertices_641, vertices_266, vertices_522, vertices_290, vertices_546, vertices_770, vertices_84, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_324, vertices_772, vertices_152, vertices_280, vertices_536, vertices_200, vertices_328, vertices_776, vertices_624, vertices_208, vertices_336, vertices_656, vertices_224, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_523), (false, vertices_675), (false, vertices_291), (false, vertices_357), (false, vertices_665), (false, vertices_233), (true, vertices_770), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_548), (true, vertices_772), (true, vertices_280), (true, vertices_776), (true, vertices_624), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_291) then 1 else
  if p.val = (false, vertices_357) then 16 else
  if p.val = (false, vertices_665) then 18 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_624) then 21 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_336) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_624), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_2 1 3 4 5 8 624
cert_row_4 2 1 2 3 7 8 796 276 1
cert_row_4 3 2 3 5 6 7 472 152 2
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 796
cert_cover_5 2 2 1 2 3 7 276 796 1
cert_coverFacet 3 628
cert_cover_5 3 1 1 3 4 5 84 628 2
cert_coverFacet 4 340
cert_cover_2 4 3 1 5 7 84 340 3
cert_coverFacet 5 472
cert_cover_5 5 3 2 3 5 6 152 472 2
cert_coverFacet 6 752
cert_cover_5 6 1 3 4 5 6 624 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0797

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m14e10q1_0798.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0798

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 77, 653, 341, 389, 617, 721, 422, 682, 370, 626, 658, 364, 172, 13, 69, 133, 261, 73, 521, 81, 145, 273, 577, 385, 641, 114, 146, 274, 530, 162, 290, 546, 386, 642, 44, 76, 140, 164, 292, 324, 388, 104, 168, 552, 648, 336, 592, 656, 352, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_77, vertices_653, vertices_341, vertices_389, vertices_617, vertices_721, vertices_422, vertices_682, vertices_370, vertices_626, vertices_658, vertices_364, vertices_172] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_133, vertices_261, vertices_73, vertices_521, vertices_81, vertices_145, vertices_273, vertices_577, vertices_385, vertices_641, vertices_114, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_44, vertices_76, vertices_140, vertices_164, vertices_292, vertices_324, vertices_388, vertices_104, vertices_168, vertices_552, vertices_648, vertices_336, vertices_592, vertices_656, vertices_352, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_77), (false, vertices_653), (false, vertices_341), (false, vertices_389), (false, vertices_617), (false, vertices_721), (true, vertices_114), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_44), (true, vertices_164), (true, vertices_292), (true, vertices_168), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 13 else
  if p.val = (false, vertices_77) then 0 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_341) then 17 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_721) then 21 else
  if p.val = (true, vertices_114) then 14 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
cert_nodeAtPriority_67 0 77 1 389 530 162 290 546 642 44 164 292 168 352 403 114 653 341 617 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 5 114
cert_row_4 1 0 2 4 6 8 682 162 1
cert_row_4 2 0 1 4 6 7 422 162 1
cert_row_4 3 1 2 4 5 7 364 44 3
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 2 0 1 4 6 162 422 1
cert_coverFacet 1 682
cert_cover_5 1 1 0 2 4 6 162 682 1
cert_coverFacet 2 370
cert_cover_5 2 0 0 3 4 7 114 370 3
cert_coverFacet 3 626
cert_cover_5 3 0 0 3 4 8 114 626 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 364
cert_cover_5 5 3 1 2 4 5 44 364 3
cert_coverFacet 6 172
cert_cover_2 6 2 1 4 6 44 172 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0798

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m14e10q1_0799.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0799

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 587, 613, 569, 409, 369, 710, 666, 394, 482, 436, 564, 660, 228, 75, 25, 265, 521, 49, 273, 97, 545, 321, 577, 138, 266, 522, 194, 322, 578, 386, 642, 52, 148, 532, 100, 164, 548, 196, 580, 644, 152, 536, 392, 304, 560, 400, 656, 224, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_587, vertices_613, vertices_569, vertices_409, vertices_369, vertices_710, vertices_666, vertices_394, vertices_482, vertices_436, vertices_564, vertices_660, vertices_228] (by decide +kernel)
  polygons := literalFinset [vertices_75, vertices_25, vertices_265, vertices_521, vertices_49, vertices_273, vertices_97, vertices_545, vertices_321, vertices_577, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_52, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_152, vertices_536, vertices_392, vertices_304, vertices_560, vertices_400, vertices_656, vertices_224, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_587), (false, vertices_613), (false, vertices_569), (false, vertices_409), (false, vertices_369), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_52), (true, vertices_148), (true, vertices_532), (true, vertices_164), (true, vertices_196), (true, vertices_644), (true, vertices_656), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 138 2
cert_row_4 1 0 1 5 6 8 710 194 1
cert_row_4 2 0 4 5 6 7 482 194 1
cert_row_4 3 1 3 4 6 7 436 52 3
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 1 0 1 5 6 194 710 1
cert_coverFacet 1 666
cert_cover_5 1 0 0 2 3 6 138 666 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 482
cert_cover_5 3 2 0 4 5 6 194 482 1
cert_coverFacet 4 436
cert_cover_5 4 3 1 3 4 6 52 436 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0799

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m14e10q1_0801.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0801

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 551, 779, 451, 213, 837, 570, 170, 394, 188, 628, 216, 600, 968, 39, 131, 259, 515, 69, 133, 517, 193, 321, 769, 42, 138, 266, 522, 162, 546, 386, 52, 84, 148, 164, 548, 580, 56, 88, 152, 536, 168, 200, 584, 392, 776, 560, 208, 592, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_551, vertices_779, vertices_451, vertices_213, vertices_837, vertices_570, vertices_170, vertices_394, vertices_188, vertices_628, vertices_216, vertices_600, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_39, vertices_131, vertices_259, vertices_515, vertices_69, vertices_133, vertices_517, vertices_193, vertices_321, vertices_769, vertices_42, vertices_138, vertices_266, vertices_522, vertices_162, vertices_546, vertices_386, vertices_52, vertices_84, vertices_148, vertices_164, vertices_548, vertices_580, vertices_56, vertices_88, vertices_152, vertices_536, vertices_168, vertices_200, vertices_584, vertices_392, vertices_776, vertices_560, vertices_208, vertices_592, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_551), (false, vertices_779), (false, vertices_451), (false, vertices_213), (false, vertices_837), (true, vertices_42), (true, vertices_138), (true, vertices_52), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_168), (true, vertices_200), (true, vertices_584), (true, vertices_392), (true, vertices_560), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 13 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 16 else
  if p.val = (false, vertices_551) then 17 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_451) then 18 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_56) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_592) then 12 else
  0
cert_priority
cert_nodeAtPriority 2 42 0 138 1 52 56 88 152 536 168 200 584 392 560 592 779 167 551 451 213 837
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 42 2
cert_row_4 1 2 5 6 7 8 968 200 3
cert_row_4 2 1 2 3 4 6 188 52 1
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 0 7 2 1
cert_heightProof 4
cert_coverFacet 0 570
cert_cover_5 0 0 0 2 3 4 42 570 2
cert_coverFacet 1 170
cert_cover_2 1 2 0 4 6 42 170 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 188
cert_cover_5 3 2 1 2 3 4 52 188 1
cert_coverFacet 4 628
cert_cover_5 4 3 1 3 4 5 52 628 3
cert_coverFacet 5 216
cert_cover_2 5 3 2 5 6 88 216 3
cert_coverFacet 6 600
cert_cover_2 6 3 2 5 8 88 600 3
cert_coverFacet 7 968
cert_cover_5 7 1 2 5 6 7 200 968 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0801

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m14e10q1_0803.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0803

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 173, 421, 665, 617, 817, 454, 714, 626, 338, 658, 108, 204, 372, 165, 41, 137, 521, 145, 273, 529, 289, 545, 385, 82, 146, 274, 530, 194, 322, 578, 386, 642, 44, 76, 140, 100, 292, 196, 324, 388, 104, 200, 584, 648, 112, 304, 560, 336, 656, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_173, vertices_421, vertices_665, vertices_617, vertices_817, vertices_454, vertices_714, vertices_626, vertices_338, vertices_658, vertices_108, vertices_204, vertices_372] (by decide +kernel)
  polygons := literalFinset [vertices_165, vertices_41, vertices_137, vertices_521, vertices_145, vertices_273, vertices_529, vertices_289, vertices_545, vertices_385, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_44, vertices_76, vertices_140, vertices_100, vertices_292, vertices_196, vertices_324, vertices_388, vertices_104, vertices_200, vertices_584, vertices_648, vertices_112, vertices_304, vertices_560, vertices_336, vertices_656, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_173), (false, vertices_421), (false, vertices_665), (false, vertices_617), (false, vertices_817), (true, vertices_82), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_76), (true, vertices_100), (true, vertices_196), (true, vertices_324), (true, vertices_200), (true, vertices_112), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 14 else
  if p.val = (false, vertices_173) then 16 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_665) then 19 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_817) then 22 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_336) then 12 else
  0
cert_priority
cert_nodeAtPriority_12 82 1 530 2 194 322 578 642 76 100 196 324 200 112 336 403 173 421 665 617 817
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 194 1
cert_row_4 1 0 1 5 6 7 454 194 1
cert_row_4 2 0 3 4 5 8 626 82 2
cert_row_4 3 1 3 4 5 7 372 100 1
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 1 0 1 5 6 194 454 1
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 194 714 1
cert_coverFacet 2 626
cert_cover_5 2 2 0 3 4 5 82 626 2
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 204
cert_cover_2 6 2 1 5 6 76 204 3
cert_coverFacet 7 372
cert_cover_5 7 3 1 3 4 5 100 372 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0803

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m14e10q1_0804.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0804

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 147, 675, 771, 837, 185, 625, 902, 410, 316, 172, 396, 372, 740, 19, 131, 259, 515, 49, 81, 145, 161, 545, 321, 577, 769, 146, 274, 386, 642, 770, 44, 140, 268, 308, 100, 164, 324, 580, 388, 644, 772, 56, 152, 280, 168, 392, 112, 336, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_147, vertices_675, vertices_771, vertices_837, vertices_185, vertices_625, vertices_902, vertices_410, vertices_316, vertices_172, vertices_396, vertices_372, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_49, vertices_81, vertices_145, vertices_161, vertices_545, vertices_321, vertices_577, vertices_769, vertices_146, vertices_274, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_268, vertices_308, vertices_100, vertices_164, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_392, vertices_112, vertices_336, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_147), (false, vertices_675), (false, vertices_771), (false, vertices_837), (false, vertices_185), (false, vertices_625), (true, vertices_386), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_308), (true, vertices_100), (true, vertices_164), (true, vertices_388), (true, vertices_644), (true, vertices_280), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 13 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_185) then 19 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_308) then 17 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_392) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_308), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
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
cert_row_4 0 0 2 3 6 7 410 146 1
cert_row_2 1 1 3 4 7 308
cert_row_4 2 0 1 6 7 8 902 386 1
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 2 0 1 6 7 386 902 1
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 6 146 410 1
cert_coverFacet 2 316
cert_cover_5 2 1 1 2 3 4 44 316 2
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 396
cert_cover_2 4 2 1 6 7 140 396 3
cert_coverFacet 5 372
cert_cover_5 5 1 1 3 4 5 308 372 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 100 740 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0804

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m14e10q1_0805.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0805

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 301, 557, 665, 457, 433, 614, 714, 114, 466, 658, 332, 588, 372, 45, 137, 265, 521, 49, 145, 529, 289, 545, 385, 50, 82, 146, 530, 98, 546, 194, 578, 642, 76, 268, 524, 100, 292, 548, 324, 580, 200, 328, 584, 648, 112, 304, 336, 400, 656, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_301, vertices_557, vertices_665, vertices_457, vertices_433, vertices_614, vertices_714, vertices_114, vertices_466, vertices_658, vertices_332, vertices_588, vertices_372] (by decide +kernel)
  polygons := literalFinset [vertices_45, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_529, vertices_289, vertices_545, vertices_385, vertices_50, vertices_82, vertices_146, vertices_530, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_76, vertices_268, vertices_524, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_200, vertices_328, vertices_584, vertices_648, vertices_112, vertices_304, vertices_336, vertices_400, vertices_656, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_301), (false, vertices_557), (false, vertices_665), (false, vertices_457), (false, vertices_433), (true, vertices_82), (true, vertices_146), (true, vertices_98), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_76), (true, vertices_100), (true, vertices_324), (true, vertices_580), (true, vertices_584), (true, vertices_112), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 14 else
  if p.val = (false, vertices_301) then 16 else
  if p.val = (false, vertices_557) then 17 else
  if p.val = (false, vertices_665) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_336) then 12 else
  0
cert_priority
cert_nodeAtPriority_12 82 1 146 2 98 194 578 642 76 100 324 580 584 112 336 563 301 557 665 457 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 194 1
cert_row_4 1 0 1 4 5 8 614 98 1
cert_row_4 2 0 3 5 6 7 466 82 3
cert_row_4 3 1 3 4 5 7 372 100 1
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 1 0 1 4 5 98 614 1
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 194 714 1
cert_coverFacet 2 114
cert_cover_2 2 3 0 4 5 50 114 3
cert_coverFacet 3 466
cert_cover_5 3 2 0 3 5 6 82 466 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 588
cert_cover_2 6 2 1 5 8 76 588 3
cert_coverFacet 7 372
cert_cover_5 7 3 1 3 4 5 100 372 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0805

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m14e10q1_0808.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0808

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 899, 589, 341, 681, 457, 278, 534, 426, 370, 690, 628, 360, 616, 771, 69, 261, 517, 73, 137, 521, 321, 385, 641, 22, 262, 518, 50, 274, 530, 162, 290, 386, 642, 84, 276, 532, 580, 104, 168, 296, 552, 328, 584, 392, 112, 560, 336, 352, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_899, vertices_589, vertices_341, vertices_681, vertices_457, vertices_278, vertices_534, vertices_426, vertices_370, vertices_690, vertices_628, vertices_360, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_771, vertices_69, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_321, vertices_385, vertices_641, vertices_22, vertices_262, vertices_518, vertices_50, vertices_274, vertices_530, vertices_162, vertices_290, vertices_386, vertices_642, vertices_84, vertices_276, vertices_532, vertices_580, vertices_104, vertices_168, vertices_296, vertices_552, vertices_328, vertices_584, vertices_392, vertices_112, vertices_560, vertices_336, vertices_352, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_899), (false, vertices_589), (false, vertices_341), (false, vertices_681), (false, vertices_457), (true, vertices_22), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_532), (true, vertices_104), (true, vertices_296), (true, vertices_112), (true, vertices_560), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 19 => Sum.inl 2
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
cert_row_4 0 0 2 4 6 7 426 162 1
cert_row_4 1 0 3 4 5 7 370 50 3
cert_row_4 2 0 3 4 6 8 690 50 3
cert_row_4 3 1 3 4 5 8 628 84 2
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 426
cert_cover_5 2 0 0 2 4 6 162 426 1
cert_coverFacet 3 370
cert_cover_5 3 1 0 3 4 5 50 370 3
cert_coverFacet 4 690
cert_cover_5 4 2 0 3 4 6 50 690 3
cert_coverFacet 5 628
cert_cover_5 5 3 1 3 4 5 84 628 2
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0808

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2523 : Certifies 2523 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0751.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2524 : Certifies 2524 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0753.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2525 : Certifies 2525 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0754.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2526 : Certifies 2526 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0758.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2527 : Certifies 2527 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0759.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2528 : Certifies 2528 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0761.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2529 : Certifies 2529 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0762.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2530 : Certifies 2530 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0764.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2531 : Certifies 2531 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0765.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2532 : Certifies 2532 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0766.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2533 : Certifies 2533 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0770.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2534 : Certifies 2534 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0771.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2535 : Certifies 2535 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0772.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2536 : Certifies 2536 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0773.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2537 : Certifies 2537 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0778.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2538 : Certifies 2538 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0779.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2539 : Certifies 2539 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0783.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2540 : Certifies 2540 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0788.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2541 : Certifies 2541 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0790.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2542 : Certifies 2542 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0794.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2543 : Certifies 2543 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0795.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2544 : Certifies 2544 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0796.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2545 : Certifies 2545 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0797.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2546 : Certifies 2546 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0798.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2547 : Certifies 2547 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0799.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2548 : Certifies 2548 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0801.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2549 : Certifies 2549 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0803.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2550 : Certifies 2550 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0804.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2551 : Certifies 2551 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0805.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2552 : Certifies 2552 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0808.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B083 (j : Fin 30) :
    Certifies (2523 + j.val) := by
  fin_cases j
  · exact projection_2523
  · exact projection_2524
  · exact projection_2525
  · exact projection_2526
  · exact projection_2527
  · exact projection_2528
  · exact projection_2529
  · exact projection_2530
  · exact projection_2531
  · exact projection_2532
  · exact projection_2533
  · exact projection_2534
  · exact projection_2535
  · exact projection_2536
  · exact projection_2537
  · exact projection_2538
  · exact projection_2539
  · exact projection_2540
  · exact projection_2541
  · exact projection_2542
  · exact projection_2543
  · exact projection_2544
  · exact projection_2545
  · exact projection_2546
  · exact projection_2547
  · exact projection_2548
  · exact projection_2549
  · exact projection_2550
  · exact projection_2551
  · exact projection_2552

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
