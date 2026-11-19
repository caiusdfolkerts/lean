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
/- Source: ProjectionCertificates/R_m14e10q1_0643.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0643

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 301, 205, 837, 665, 281, 785, 614, 122, 218, 690, 108, 820, 312, 13, 69, 261, 25, 137, 265, 273, 529, 193, 577, 641, 769, 90, 50, 146, 98, 546, 194, 578, 642, 44, 76, 100, 292, 548, 580, 772, 56, 152, 280, 104, 296, 200, 304, 560, 656, 784]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_301, vertices_205, vertices_837, vertices_665, vertices_281, vertices_785, vertices_614, vertices_122, vertices_218, vertices_690, vertices_108, vertices_820, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_25, vertices_137, vertices_265, vertices_273, vertices_529, vertices_193, vertices_577, vertices_641, vertices_769, vertices_90, vertices_50, vertices_146, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_44, vertices_76, vertices_100, vertices_292, vertices_548, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_104, vertices_296, vertices_200, vertices_304, vertices_560, vertices_656, vertices_784] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_301), (false, vertices_205), (false, vertices_837), (false, vertices_665), (false, vertices_281), (false, vertices_785), (true, vertices_90), (true, vertices_50), (true, vertices_146), (true, vertices_98), (true, vertices_546), (true, vertices_100), (true, vertices_548), (true, vertices_56), (true, vertices_104), (true, vertices_304), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 13 else
  if p.val = (false, vertices_301) then 16 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_785) then 1 else
  if p.val = (true, vertices_90) then 14 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_560) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 4 5 8 614 98 1
cert_row_4 2 0 3 4 6 8 690 50 3
cert_row_4 3 1 3 4 7 8 820 292 1
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 1 0 1 4 5 98 614 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 4 90 122 3
cert_coverFacet 2 218
cert_cover_5 2 0 0 2 3 6 90 218 3
cert_coverFacet 3 690
cert_cover_5 3 2 0 3 4 6 50 690 3
cert_coverFacet 4 108
cert_cover_2 4 2 1 4 5 44 108 3
cert_coverFacet 5 820
cert_cover_5 5 3 1 3 4 7 292 820 1
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0643

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m14e10q1_0644.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0644

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [199, 263, 779, 659, 109, 301, 713, 390, 818, 402, 436, 740, 872, 688, 7, 131, 259, 515, 45, 69, 261, 73, 265, 521, 193, 641, 134, 262, 146, 274, 530, 386, 770, 100, 164, 292, 196, 388, 104, 296, 584, 776, 176, 304, 560, 400, 656, 608, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_199, vertices_263, vertices_779, vertices_659, vertices_109, vertices_301, vertices_713, vertices_390, vertices_818, vertices_402, vertices_436, vertices_740, vertices_872, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_131, vertices_259, vertices_515, vertices_45, vertices_69, vertices_261, vertices_73, vertices_265, vertices_521, vertices_193, vertices_641, vertices_134, vertices_262, vertices_146, vertices_274, vertices_530, vertices_386, vertices_770, vertices_100, vertices_164, vertices_292, vertices_196, vertices_388, vertices_104, vertices_296, vertices_584, vertices_776, vertices_176, vertices_304, vertices_560, vertices_400, vertices_656, vertices_608, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_199), (false, vertices_263), (false, vertices_779), (false, vertices_659), (false, vertices_109), (false, vertices_301), (false, vertices_713), (true, vertices_274), (true, vertices_386), (true, vertices_164), (true, vertices_388), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_400), (true, vertices_608), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_109) then 17 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
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
cert_row_4 0 0 3 4 7 8 818 274 2
cert_row_4 1 1 3 4 6 7 436 164 1
cert_row_4 2 1 4 5 6 8 740 100 3
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 390
cert_cover_2 0 1 0 6 7 134 390 3
cert_coverFacet 1 818
cert_cover_5 1 0 0 3 4 7 274 818 2
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 436
cert_cover_5 3 1 1 3 4 6 164 436 1
cert_coverFacet 4 740
cert_cover_5 4 2 1 4 5 6 100 740 3
cert_coverFacet 5 872
cert_cover_5 5 3 2 4 5 7 104 872 3
cert_coverFacet 6 688
cert_cover_2 6 4 3 6 8 176 688 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0644

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m14e10q1_0646.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0646

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 341, 421, 709, 601, 657, 678, 570, 346, 362, 658, 418, 620, 356, 69, 133, 261, 81, 145, 273, 529, 577, 385, 641, 26, 42, 330, 146, 274, 530, 162, 290, 546, 386, 642, 100, 164, 292, 548, 324, 580, 644, 88, 536, 104, 552, 584, 336, 656, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_341, vertices_421, vertices_709, vertices_601, vertices_657, vertices_678, vertices_570, vertices_346, vertices_362, vertices_658, vertices_418, vertices_620, vertices_356] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_81, vertices_145, vertices_273, vertices_529, vertices_577, vertices_385, vertices_641, vertices_26, vertices_42, vertices_330, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_100, vertices_164, vertices_292, vertices_548, vertices_324, vertices_580, vertices_644, vertices_88, vertices_536, vertices_104, vertices_552, vertices_584, vertices_336, vertices_656, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_341), (false, vertices_421), (false, vertices_709), (false, vertices_601), (false, vertices_657), (true, vertices_26), (true, vertices_42), (true, vertices_330), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_100), (true, vertices_548), (true, vertices_104), (true, vertices_552), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 14 else
  if p.val = (false, vertices_341) then 17 else
  if p.val = (false, vertices_421) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_330) then 15 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_330), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 7 330
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 1 2 4 5 8 620 100 1
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 570
cert_cover_5 1 2 0 2 3 4 26 570 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 5 26 346 3
cert_coverFacet 3 362
cert_cover_5 3 0 0 2 4 5 42 362 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 100 620 1
cert_coverFacet 7 356
cert_cover_2 7 4 1 5 7 100 356 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0646

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m14e10q1_0647.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0647

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 677, 569, 369, 721, 417, 558, 398, 710, 602, 330, 428, 312, 344, 49, 81, 529, 161, 289, 545, 193, 321, 385, 641, 14, 134, 518, 74, 266, 522, 194, 322, 578, 386, 44, 396, 164, 548, 644, 56, 88, 280, 536, 296, 552, 328, 304, 336, 592, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_677, vertices_569, vertices_369, vertices_721, vertices_417, vertices_558, vertices_398, vertices_710, vertices_602, vertices_330, vertices_428, vertices_312, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_529, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_14, vertices_134, vertices_518, vertices_74, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_44, vertices_396, vertices_164, vertices_548, vertices_644, vertices_56, vertices_88, vertices_280, vertices_536, vertices_296, vertices_552, vertices_328, vertices_304, vertices_336, vertices_592, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_677), (false, vertices_569), (false, vertices_369), (false, vertices_721), (false, vertices_417), (true, vertices_14), (true, vertices_134), (true, vertices_518), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_578), (true, vertices_44), (true, vertices_396), (true, vertices_88), (true, vertices_280), (true, vertices_296), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_396) then 17 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_328) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 1 2 4 8 558 14 3
cert_row_4 2 0 1 5 6 8 710 134 2
cert_row_4 3 0 2 3 5 8 602 74 2
cert_rows
cert_pivot_2 7 4 1 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 14 558 3
cert_coverFacet 1 398
cert_cover_5 1 0 0 1 2 6 14 398 3
cert_coverFacet 2 710
cert_cover_5 2 2 0 1 5 6 134 710 2
cert_coverFacet 3 602
cert_cover_5 3 3 0 2 3 5 74 602 2
cert_coverFacet 4 330
cert_cover_2 4 2 0 5 7 74 330 3
cert_coverFacet 5 428
cert_cover_5 5 0 1 2 4 6 44 428 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0647

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m14e10q1_0649.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0649

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 213, 357, 165, 809, 961, 158, 174, 570, 722, 92, 300, 844, 600, 37, 69, 133, 161, 289, 545, 193, 321, 641, 769, 142, 26, 42, 146, 530, 162, 546, 642, 28, 44, 76, 268, 84, 148, 164, 292, 324, 88, 536, 296, 552, 584, 776, 208, 592, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_213, vertices_357, vertices_165, vertices_809, vertices_961, vertices_158, vertices_174, vertices_570, vertices_722, vertices_92, vertices_300, vertices_844, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_133, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_769, vertices_142, vertices_26, vertices_42, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_28, vertices_44, vertices_76, vertices_268, vertices_84, vertices_148, vertices_164, vertices_292, vertices_324, vertices_88, vertices_536, vertices_296, vertices_552, vertices_584, vertices_776, vertices_208, vertices_592, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_213), (false, vertices_357), (false, vertices_165), (false, vertices_809), (false, vertices_961), (true, vertices_142), (true, vertices_26), (true, vertices_42), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_88), (true, vertices_536), (true, vertices_584), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_357) then 18 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_142) then 15 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_592) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_142), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 26 3
cert_row_4 1 0 3 5 6 8 722 146 2
cert_row_2 2 0 1 2 6 142
cert_row_4 3 1 2 5 7 8 844 76 3
cert_rows
cert_pivot_2 4 3 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 2 0 1 2 3 142 158 3
cert_coverFacet 1 174
cert_cover_5 1 2 0 1 2 4 142 174 3
cert_coverFacet 2 570
cert_cover_5 2 0 0 2 3 4 26 570 3
cert_coverFacet 3 722
cert_cover_5 3 1 0 3 5 6 146 722 2
cert_coverFacet 4 92
cert_cover_2 4 2 1 3 5 28 92 3
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 844
cert_cover_5 6 3 1 2 5 7 76 844 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0649

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m14e10q1_0651.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0651

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 789, 89, 409, 233, 961, 94, 110, 566, 738, 284, 300, 804, 936, 25, 73, 137, 81, 273, 529, 193, 577, 385, 769, 78, 22, 38, 82, 530, 98, 546, 578, 28, 44, 268, 276, 532, 292, 548, 772, 88, 280, 104, 168, 296, 392, 224, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_789, vertices_89, vertices_409, vertices_233, vertices_961, vertices_94, vertices_110, vertices_566, vertices_738, vertices_284, vertices_300, vertices_804, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_137, vertices_81, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_769, vertices_78, vertices_22, vertices_38, vertices_82, vertices_530, vertices_98, vertices_546, vertices_578, vertices_28, vertices_44, vertices_268, vertices_276, vertices_532, vertices_292, vertices_548, vertices_772, vertices_88, vertices_280, vertices_104, vertices_168, vertices_296, vertices_392, vertices_224, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_789), (false, vertices_89), (false, vertices_409), (false, vertices_233), (false, vertices_961), (true, vertices_78), (true, vertices_22), (true, vertices_38), (true, vertices_98), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_292), (true, vertices_548), (true, vertices_296), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_89) then 0 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (false, vertices_961) then 24 else
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
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_800) then 12 else
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
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 22 3
cert_row_2 1 0 1 2 5 78
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 2 4 6 7 8 936 168 3
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
cert_coverFacet 7 936
cert_cover_5 7 3 2 4 6 7 168 936 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0651

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m14e10q1_0653.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0653

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 677, 569, 369, 721, 417, 558, 398, 710, 346, 586, 428, 312, 600, 49, 81, 529, 161, 289, 545, 193, 321, 385, 641, 14, 134, 518, 74, 266, 522, 194, 322, 578, 386, 44, 396, 164, 548, 644, 56, 88, 280, 536, 296, 552, 584, 304, 336, 592, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_677, vertices_569, vertices_369, vertices_721, vertices_417, vertices_558, vertices_398, vertices_710, vertices_346, vertices_586, vertices_428, vertices_312, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_529, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_14, vertices_134, vertices_518, vertices_74, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_44, vertices_396, vertices_164, vertices_548, vertices_644, vertices_56, vertices_88, vertices_280, vertices_536, vertices_296, vertices_552, vertices_584, vertices_304, vertices_336, vertices_592, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_677), (false, vertices_569), (false, vertices_369), (false, vertices_721), (false, vertices_417), (true, vertices_14), (true, vertices_134), (true, vertices_518), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_578), (true, vertices_44), (true, vertices_396), (true, vertices_88), (true, vertices_280), (true, vertices_296), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_396) then 17 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_584) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 14 3
cert_row_4 1 0 1 5 6 8 710 134 2
cert_row_2 2 1 2 6 7 396
cert_row_4 3 0 2 3 5 7 346 74 2
cert_rows
cert_pivot_2 4 8 1 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 14 558 3
cert_coverFacet 1 398
cert_cover_5 1 2 0 1 2 6 14 398 3
cert_coverFacet 2 710
cert_cover_5 2 1 0 1 5 6 134 710 2
cert_coverFacet 3 346
cert_cover_5 3 3 0 2 3 5 74 346 2
cert_coverFacet 4 586
cert_cover_2 4 2 0 5 8 74 586 3
cert_coverFacet 5 428
cert_cover_5 5 2 1 2 4 6 44 428 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0653

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m14e10q1_0655.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0655

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 453, 569, 433, 721, 353, 558, 334, 710, 362, 780, 916, 312, 792, 49, 145, 529, 97, 289, 545, 193, 321, 577, 385, 14, 70, 518, 42, 330, 98, 546, 578, 268, 524, 196, 324, 388, 644, 772, 56, 280, 536, 296, 552, 776, 304, 400, 656, 784, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_453, vertices_569, vertices_433, vertices_721, vertices_353, vertices_558, vertices_334, vertices_710, vertices_362, vertices_780, vertices_916, vertices_312, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_14, vertices_70, vertices_518, vertices_42, vertices_330, vertices_98, vertices_546, vertices_578, vertices_268, vertices_524, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_56, vertices_280, vertices_536, vertices_296, vertices_552, vertices_776, vertices_304, vertices_400, vertices_656, vertices_784, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_453), (false, vertices_569), (false, vertices_433), (false, vertices_721), (false, vertices_353), (true, vertices_14), (true, vertices_70), (true, vertices_518), (true, vertices_42), (true, vertices_330), (true, vertices_268), (true, vertices_524), (true, vertices_644), (true, vertices_772), (true, vertices_280), (true, vertices_296), (true, vertices_776), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 14 else
  if p.val = (false, vertices_453) then 17 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (false, vertices_353) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_330) then 15 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_784) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_330), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
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
cert_row_4 0 0 1 2 4 8 558 14 3
cert_row_2 1 0 2 5 7 330
cert_row_4 2 0 1 5 6 8 710 70 3
cert_row_4 3 1 3 6 7 8 916 388 1
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 14 558 3
cert_coverFacet 1 334
cert_cover_5 1 1 0 1 2 5 14 334 3
cert_coverFacet 2 710
cert_cover_5 2 2 0 1 5 6 70 710 3
cert_coverFacet 3 362
cert_cover_5 3 1 0 2 4 5 42 362 3
cert_coverFacet 4 780
cert_cover_2 4 2 1 7 8 268 780 3
cert_coverFacet 5 916
cert_cover_5 5 3 1 3 6 7 388 916 1
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0655

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m14e10q1_0658.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0658

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 93, 269, 661, 361, 849, 174, 302, 646, 690, 866, 156, 632, 184, 13, 21, 261, 517, 73, 265, 81, 529, 321, 769, 46, 134, 262, 518, 162, 290, 546, 642, 770, 28, 140, 268, 148, 644, 56, 88, 152, 104, 168, 296, 176, 560, 592, 656, 352, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_93, vertices_269, vertices_661, vertices_361, vertices_849, vertices_174, vertices_302, vertices_646, vertices_690, vertices_866, vertices_156, vertices_632, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_261, vertices_517, vertices_73, vertices_265, vertices_81, vertices_529, vertices_321, vertices_769, vertices_46, vertices_134, vertices_262, vertices_518, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_28, vertices_140, vertices_268, vertices_148, vertices_644, vertices_56, vertices_88, vertices_152, vertices_104, vertices_168, vertices_296, vertices_176, vertices_560, vertices_592, vertices_656, vertices_352, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_93), (false, vertices_269), (false, vertices_661), (false, vertices_361), (false, vertices_849), (true, vertices_46), (true, vertices_134), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_140), (true, vertices_56), (true, vertices_152), (true, vertices_168), (true, vertices_176), (true, vertices_560), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (true, vertices_46) then 15 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
cert_nodeAtPriority_17 269 134 162 290 546 642 140 56 152 168 176 560 608 775 46 93 661 361 849
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 3 4 6 8 690 162 1
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 0 0 1 2 6 46 174 3
cert_coverFacet 1 302
cert_cover_5 1 0 0 1 2 7 46 302 3
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 690
cert_cover_5 3 1 0 3 4 6 162 690 1
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 290 866 2
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 632
cert_cover_5 6 3 2 3 4 5 56 632 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0658

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m14e10q1_0659.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0659

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 141, 269, 309, 213, 809, 689, 398, 454, 842, 722, 116, 868, 624, 13, 21, 133, 261, 137, 265, 521, 49, 145, 289, 545, 641, 390, 138, 266, 522, 194, 322, 578, 642, 140, 268, 52, 84, 100, 292, 196, 324, 776, 112, 560, 208, 592, 656, 608, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_141, vertices_269, vertices_309, vertices_213, vertices_809, vertices_689, vertices_398, vertices_454, vertices_842, vertices_722, vertices_116, vertices_868, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_133, vertices_261, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_289, vertices_545, vertices_641, vertices_390, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_642, vertices_140, vertices_268, vertices_52, vertices_84, vertices_100, vertices_292, vertices_196, vertices_324, vertices_776, vertices_112, vertices_560, vertices_208, vertices_592, vertices_656, vertices_608, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_141), (false, vertices_269), (false, vertices_309), (false, vertices_213), (false, vertices_809), (false, vertices_689), (true, vertices_390), (true, vertices_266), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_100), (true, vertices_324), (true, vertices_112), (true, vertices_592), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 13 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_269) then 1 else
  if p.val = (false, vertices_309) then 16 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_809) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_390) then 14 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
cert_nodeAtPriority_67 0 141 1 269 266 194 322 578 100 324 112 592 608 832 651 390 309 213 809 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 266 2
cert_row_4 1 0 3 5 6 8 722 194 1
cert_row_2 2 0 1 6 7 390
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 2 0 1 2 6 390 398 2
cert_coverFacet 1 454
cert_cover_5 1 2 0 1 5 6 390 454 2
cert_coverFacet 2 842
cert_cover_5 2 0 0 2 5 7 266 842 2
cert_coverFacet 3 722
cert_cover_5 3 1 0 3 5 6 194 722 1
cert_coverFacet 4 116
cert_cover_2 4 3 1 4 5 52 116 3
cert_coverFacet 5 868
cert_cover_5 5 3 1 4 5 7 100 868 3
cert_coverFacet 6 624
cert_cover_2 6 4 3 5 8 112 624 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0659

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m14e10q1_0660.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0660

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 403, 707, 453, 617, 305, 353, 902, 786, 572, 348, 716, 788, 376, 19, 131, 515, 49, 273, 97, 289, 545, 193, 321, 577, 385, 274, 530, 386, 642, 770, 28, 76, 524, 276, 532, 196, 324, 388, 644, 772, 56, 344, 104, 552, 584, 304, 560, 784, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_403, vertices_707, vertices_453, vertices_617, vertices_305, vertices_353, vertices_902, vertices_786, vertices_572, vertices_348, vertices_716, vertices_788, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_515, vertices_49, vertices_273, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_524, vertices_276, vertices_532, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_56, vertices_344, vertices_104, vertices_552, vertices_584, vertices_304, vertices_560, vertices_784, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_403), (false, vertices_707), (false, vertices_453), (false, vertices_617), (false, vertices_305), (false, vertices_353), (true, vertices_770), (true, vertices_28), (true, vertices_76), (true, vertices_524), (true, vertices_276), (true, vertices_532), (true, vertices_644), (true, vertices_772), (true, vertices_56), (true, vertices_344), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 13 else
  if p.val = (false, vertices_403) then 14 else
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_453) then 17 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (false, vertices_353) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_344) then 20 else
  if p.val = (true, vertices_784) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_344), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_2 1 2 3 5 7 344
cert_row_4 2 1 2 3 4 8 572 28 3
cert_row_4 3 1 2 5 6 8 716 76 3
cert_rows
cert_pivot_2 0 7 3 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 786
cert_cover_2 1 3 0 7 8 274 786 3
cert_coverFacet 2 572
cert_cover_5 2 2 1 2 3 4 28 572 3
cert_coverFacet 3 348
cert_cover_5 3 1 1 2 3 5 28 348 3
cert_coverFacet 4 716
cert_cover_5 4 3 1 2 5 6 76 716 3
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 376
cert_cover_5 6 1 2 3 4 5 56 376 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0660

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m14e10q1_0668.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0668

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 535, 395, 835, 613, 453, 154, 538, 810, 572, 244, 184, 424, 992, 23, 131, 259, 515, 69, 133, 517, 321, 577, 385, 26, 138, 266, 522, 146, 530, 770, 52, 148, 532, 100, 548, 196, 56, 152, 536, 168, 296, 552, 392, 176, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_535, vertices_395, vertices_835, vertices_613, vertices_453, vertices_154, vertices_538, vertices_810, vertices_572, vertices_244, vertices_184, vertices_424, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_131, vertices_259, vertices_515, vertices_69, vertices_133, vertices_517, vertices_321, vertices_577, vertices_385, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_770, vertices_52, vertices_148, vertices_532, vertices_100, vertices_548, vertices_196, vertices_56, vertices_152, vertices_536, vertices_168, vertices_296, vertices_552, vertices_392, vertices_176, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_535), (false, vertices_395), (false, vertices_835), (false, vertices_613), (false, vertices_453), (true, vertices_26), (true, vertices_522), (true, vertices_52), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_176), (true, vertices_224), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 13 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 16 else
  if p.val = (false, vertices_535) then 17 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_56) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
cert_nodeAtPriority 2 26 0 522 1 52 56 152 536 168 296 552 176 224 416 800 395 151 535 835 613 453
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 266 2
cert_row_4 1 1 2 3 4 8 572 52 1
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 2 1 4
cert_heightProof 4
cert_coverFacet 0 154
cert_cover_2 0 2 0 3 6 26 154 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 810
cert_cover_5 2 0 0 2 4 7 266 810 2
cert_coverFacet 3 572
cert_cover_5 3 1 1 2 3 4 52 572 1
cert_coverFacet 4 244
cert_cover_5 4 2 1 3 4 5 52 244 3
cert_coverFacet 5 184
cert_cover_2 5 3 2 4 6 56 184 3
cert_coverFacet 6 424
cert_cover_2 6 4 2 6 7 168 424 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0668

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m14e10q1_0671.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0671

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 157, 557, 709, 313, 913, 590, 58, 90, 554, 370, 962, 220, 464, 13, 133, 517, 25, 41, 145, 273, 289, 545, 641, 769, 26, 42, 74, 522, 50, 82, 290, 546, 322, 578, 770, 156, 76, 524, 196, 580, 56, 88, 552, 304, 208, 336, 400, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_157, vertices_557, vertices_709, vertices_313, vertices_913, vertices_590, vertices_58, vertices_90, vertices_554, vertices_370, vertices_962, vertices_220, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_25, vertices_41, vertices_145, vertices_273, vertices_289, vertices_545, vertices_641, vertices_769, vertices_26, vertices_42, vertices_74, vertices_522, vertices_50, vertices_82, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_156, vertices_76, vertices_524, vertices_196, vertices_580, vertices_56, vertices_88, vertices_552, vertices_304, vertices_208, vertices_336, vertices_400, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_157), (false, vertices_557), (false, vertices_709), (false, vertices_313), (false, vertices_913), (true, vertices_26), (true, vertices_42), (true, vertices_74), (true, vertices_522), (true, vertices_50), (true, vertices_82), (true, vertices_322), (true, vertices_578), (true, vertices_76), (true, vertices_88), (true, vertices_208), (true, vertices_336), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_157) then 16 else
  if p.val = (false, vertices_557) then 17 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_313) then 20 else
  if p.val = (false, vertices_913) then 22 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
cert_priority
cert_nodeAtPriority_11 26 42 74 522 50 82 322 578 76 88 208 336 448 803 157 557 709 313 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 7 370 50 3
cert_row_2 1 1 2 3 6 156
cert_row_4 2 0 1 2 5 8 590 74 1
cert_row_4 3 0 5 6 7 8 962 322 2
cert_rows
cert_pivot_2 4 3 1 0
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 2 0 1 2 5 74 590 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 90
cert_cover_2 2 2 0 3 5 26 90 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 370
cert_cover_5 4 0 0 3 4 5 50 370 3
cert_coverFacet 5 962
cert_cover_5 5 3 0 5 6 7 322 962 2
cert_coverFacet 6 220
cert_cover_5 6 1 1 2 3 5 156 220 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0671

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m14e10q1_0672.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0672

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [211, 803, 579, 387, 613, 409, 369, 710, 906, 188, 684, 116, 212, 824, 67, 131, 259, 515, 81, 145, 273, 97, 289, 545, 577, 385, 194, 578, 386, 642, 770, 172, 52, 84, 148, 100, 548, 196, 580, 644, 56, 152, 280, 552, 392, 648, 776, 112, 304, 208, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_803, vertices_579, vertices_387, vertices_613, vertices_409, vertices_369, vertices_710, vertices_906, vertices_188, vertices_684, vertices_116, vertices_212, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_81, vertices_145, vertices_273, vertices_97, vertices_289, vertices_545, vertices_577, vertices_385, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_172, vertices_52, vertices_84, vertices_148, vertices_100, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_152, vertices_280, vertices_552, vertices_392, vertices_648, vertices_776, vertices_112, vertices_304, vertices_208, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_803), (false, vertices_579), (false, vertices_387), (false, vertices_613), (false, vertices_409), (false, vertices_369), (true, vertices_642), (true, vertices_172), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_644), (true, vertices_56), (true, vertices_552), (true, vertices_648), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 13 else
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_579) then 0 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_613) then 16 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_172) then 17 else
  if p.val = (true, vertices_52) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_776) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_579), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_172), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
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
cert_row_4 0 0 1 5 6 8 710 194 1
cert_row_2 1 1 2 4 6 172
cert_row_4 2 0 2 6 7 8 906 386 1
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 5 1 0 2
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 0 0 1 5 6 194 710 1
cert_coverFacet 1 906
cert_cover_5 1 2 0 2 6 7 386 906 1
cert_coverFacet 2 188
cert_cover_5 2 1 1 2 3 4 172 188 2
cert_coverFacet 3 684
cert_cover_5 3 1 1 2 4 8 172 684 3
cert_coverFacet 4 116
cert_cover_2 4 3 1 4 5 52 116 3
cert_coverFacet 5 212
cert_cover_2 5 3 1 5 6 84 212 3
cert_coverFacet 6 824
cert_cover_5 6 3 2 3 4 7 56 824 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0672

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m14e10q1_0674.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0674

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 403, 227, 613, 793, 929, 206, 590, 154, 538, 412, 812, 228, 420, 19, 67, 131, 273, 529, 97, 161, 545, 577, 385, 769, 78, 26, 138, 522, 146, 530, 194, 578, 140, 268, 524, 100, 164, 292, 548, 196, 580, 388, 152, 280, 536, 776, 400, 224, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_403, vertices_227, vertices_613, vertices_793, vertices_929, vertices_206, vertices_590, vertices_154, vertices_538, vertices_412, vertices_812, vertices_228, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_131, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_577, vertices_385, vertices_769, vertices_78, vertices_26, vertices_138, vertices_522, vertices_146, vertices_530, vertices_194, vertices_578, vertices_140, vertices_268, vertices_524, vertices_100, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_152, vertices_280, vertices_536, vertices_776, vertices_400, vertices_224, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_403), (false, vertices_227), (false, vertices_613), (false, vertices_793), (false, vertices_929), (true, vertices_78), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_164), (true, vertices_292), (true, vertices_196), (true, vertices_388), (true, vertices_152)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_227) then 17 else
  if p.val = (false, vertices_613) then 12 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (false, vertices_929) then 22 else
  if p.val = (true, vertices_78) then 13 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_152) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
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
cert_row_2 0 0 1 2 5 78
cert_row_4 1 1 2 3 6 7 412 140 2
cert_row_4 2 1 2 4 7 8 812 268 2
cert_rows_3
cert_pivot_3 3 0 1
cert_heightProof 3
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 6 78 206 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 412
cert_cover_5 4 1 1 2 3 6 140 412 2
cert_coverFacet 5 812
cert_cover_5 5 2 1 2 4 7 268 812 2
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0674

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m14e10q1_0675.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0675

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 341, 661, 613, 713, 449, 310, 566, 618, 298, 906, 658, 364, 456, 21, 69, 517, 145, 273, 193, 321, 577, 385, 641, 54, 42, 266, 522, 146, 274, 530, 290, 546, 386, 642, 276, 532, 100, 292, 548, 324, 104, 296, 200, 328, 584, 392, 648, 656, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_341, vertices_661, vertices_613, vertices_713, vertices_449, vertices_310, vertices_566, vertices_618, vertices_298, vertices_906, vertices_658, vertices_364, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_517, vertices_145, vertices_273, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_54, vertices_42, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_324, vertices_104, vertices_296, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_656, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_341), (false, vertices_661), (false, vertices_613), (false, vertices_713), (false, vertices_449), (true, vertices_54), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_292), (true, vertices_104), (true, vertices_296), (true, vertices_328), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 14 else
  if p.val = (false, vertices_341) then 17 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_54) then 15 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_392) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 0 2 6 7 8 906 266 2
cert_row_4 2 0 2 4 5 8 618 42 3
cert_row_4 3 1 2 4 5 7 364 100 1
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 7 54 310 3
cert_coverFacet 1 566
cert_cover_5 1 0 0 1 3 8 54 566 3
cert_coverFacet 2 618
cert_cover_5 2 2 0 2 4 5 42 618 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 906
cert_cover_5 4 1 0 2 6 7 266 906 2
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 364
cert_cover_5 6 3 1 2 4 5 100 364 1
cert_coverFacet 7 456
cert_cover_2 7 5 2 6 7 200 456 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0675

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m14e10q1_0677.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0677

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [211, 339, 781, 309, 533, 665, 457, 806, 842, 178, 306, 738, 692, 712, 83, 21, 261, 517, 137, 265, 521, 145, 273, 529, 193, 321, 50, 146, 274, 162, 290, 546, 194, 322, 578, 770, 52, 532, 292, 548, 772, 200, 328, 584, 648, 776, 176, 304, 656, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_339, vertices_781, vertices_309, vertices_533, vertices_665, vertices_457, vertices_806, vertices_842, vertices_178, vertices_306, vertices_738, vertices_692, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_83, vertices_21, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_770, vertices_52, vertices_532, vertices_292, vertices_548, vertices_772, vertices_200, vertices_328, vertices_584, vertices_648, vertices_776, vertices_176, vertices_304, vertices_656, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_339), (false, vertices_781), (false, vertices_309), (false, vertices_533), (false, vertices_665), (false, vertices_457), (true, vertices_50), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_578), (true, vertices_770), (true, vertices_548), (true, vertices_584), (true, vertices_176), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 13 else
  if p.val = (false, vertices_339) then 14 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_309) then 17 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_665) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_704) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 322 1
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 842
cert_cover_5 1 0 0 2 5 7 322 842 1
cert_coverFacet 2 178
cert_cover_2 2 3 0 4 6 50 178 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 162 738 2
cert_coverFacet 5 692
cert_cover_5 5 3 1 3 4 6 52 692 3
cert_coverFacet 6 712
cert_cover_2 6 5 2 6 8 200 712 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0677

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m14e10q1_0680.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0680

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 653, 601, 409, 369, 705, 398, 294, 550, 710, 626, 354, 316, 572, 25, 137, 521, 81, 273, 193, 321, 577, 385, 641, 38, 134, 262, 518, 98, 290, 546, 194, 322, 578, 386, 60, 140, 268, 524, 292, 548, 644, 280, 536, 392, 112, 304, 560, 592, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_653, vertices_601, vertices_409, vertices_369, vertices_705, vertices_398, vertices_294, vertices_550, vertices_710, vertices_626, vertices_354, vertices_316, vertices_572] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_521, vertices_81, vertices_273, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_38, vertices_134, vertices_262, vertices_518, vertices_98, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_60, vertices_140, vertices_268, vertices_524, vertices_292, vertices_548, vertices_644, vertices_280, vertices_536, vertices_392, vertices_112, vertices_304, vertices_560, vertices_592, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_653), (false, vertices_601), (false, vertices_409), (false, vertices_369), (false, vertices_705), (true, vertices_38), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_578), (true, vertices_60), (true, vertices_268), (true, vertices_292), (true, vertices_548), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_60) then 17 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_560) then 12 else
  0
cert_priority
cert_nodeAtPriority_2 0 705 1 38 2 134 3 262 518 98 290 546 578 268 292 548 560 451 653 60 601 409 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 1 5 6 8 710 134 2
cert_row_4 3 0 3 4 5 8 626 98 1
cert_rows
cert_pivot_2 7 2 1 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 294
cert_cover_2 1 1 0 4 7 38 294 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 710
cert_cover_5 3 2 0 1 5 6 134 710 2
cert_coverFacet 4 626
cert_cover_5 4 3 0 3 4 5 98 626 1
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 316
cert_cover_5 6 1 1 2 3 7 60 316 3
cert_coverFacet 7 572
cert_cover_5 7 1 1 2 3 8 60 572 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0680

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m14e10q1_0681.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0681

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 677, 185, 345, 809, 657, 662, 806, 198, 326, 218, 338, 428, 460, 25, 41, 265, 145, 273, 529, 161, 545, 641, 769, 70, 134, 262, 518, 82, 146, 274, 530, 194, 322, 770, 396, 164, 292, 548, 196, 324, 644, 88, 152, 168, 296, 200, 328, 336, 656, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_677, vertices_185, vertices_345, vertices_809, vertices_657, vertices_662, vertices_806, vertices_198, vertices_326, vertices_218, vertices_338, vertices_428, vertices_460] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_145, vertices_273, vertices_529, vertices_161, vertices_545, vertices_641, vertices_769, vertices_70, vertices_134, vertices_262, vertices_518, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_770, vertices_396, vertices_164, vertices_292, vertices_548, vertices_196, vertices_324, vertices_644, vertices_88, vertices_152, vertices_168, vertices_296, vertices_200, vertices_328, vertices_336, vertices_656, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_677), (false, vertices_185), (false, vertices_345), (false, vertices_809), (false, vertices_657), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_322), (true, vertices_396), (true, vertices_292), (true, vertices_196), (true, vertices_324), (true, vertices_200)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_185) then 19 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_396) then 17 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_200) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 262 2
cert_row_2 1 1 2 6 7 396
cert_row_4 2 0 1 3 6 8 662 134 2
cert_row_4 3 0 2 3 5 6 218 82 1
cert_rows
cert_pivot_2 4 7 1 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 2 0 1 3 6 134 662 2
cert_coverFacet 1 806
cert_cover_5 1 0 0 1 4 7 262 806 2
cert_coverFacet 2 198
cert_cover_2 2 1 0 5 6 70 198 3
cert_coverFacet 3 326
cert_cover_2 3 1 0 5 7 70 326 3
cert_coverFacet 4 218
cert_cover_5 4 3 0 2 3 5 82 218 1
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 428
cert_cover_5 6 1 1 2 4 6 396 428 2
cert_coverFacet 7 460
cert_cover_5 7 1 1 2 5 6 396 460 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0681

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m14e10q1_0682.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0682

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 661, 313, 681, 457, 401, 214, 534, 614, 362, 306, 466, 716, 616, 41, 137, 265, 49, 145, 273, 529, 545, 385, 641, 22, 70, 518, 50, 210, 274, 530, 98, 290, 546, 322, 148, 532, 196, 580, 644, 104, 296, 552, 200, 328, 584, 648, 304, 400, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_661, vertices_313, vertices_681, vertices_457, vertices_401, vertices_214, vertices_534, vertices_614, vertices_362, vertices_306, vertices_466, vertices_716, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_265, vertices_49, vertices_145, vertices_273, vertices_529, vertices_545, vertices_385, vertices_641, vertices_22, vertices_70, vertices_518, vertices_50, vertices_210, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_148, vertices_532, vertices_196, vertices_580, vertices_644, vertices_104, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_648, vertices_304, vertices_400, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_661), (false, vertices_313), (false, vertices_681), (false, vertices_457), (false, vertices_401), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_210), (true, vertices_274), (true, vertices_98), (true, vertices_290), (true, vertices_322), (true, vertices_196), (true, vertices_580), (true, vertices_104), (true, vertices_584), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 14 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_313) then 19 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_210) then 15 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
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
cert_row_2 0 0 3 5 6 210
cert_row_4 1 0 2 4 5 7 362 98 1
cert_row_4 2 0 1 4 5 8 614 70 2
cert_row_4 3 1 2 5 6 8 716 196 1
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 614
cert_cover_5 2 2 0 1 4 5 70 614 2
cert_coverFacet 3 362
cert_cover_5 3 1 0 2 4 5 98 362 1
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 466
cert_cover_5 5 0 0 3 5 7 210 466 3
cert_coverFacet 6 716
cert_cover_5 6 3 1 2 5 6 196 716 1
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0682

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m14e10q1_0685.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0685

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 789, 357, 709, 233, 801, 662, 154, 282, 362, 170, 818, 412, 460, 69, 261, 517, 97, 161, 289, 545, 193, 641, 769, 26, 42, 138, 266, 146, 274, 530, 162, 290, 546, 642, 396, 148, 276, 532, 196, 324, 644, 152, 280, 104, 168, 200, 328, 784, 352, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_789, vertices_357, vertices_709, vertices_233, vertices_801, vertices_662, vertices_154, vertices_282, vertices_362, vertices_170, vertices_818, vertices_412, vertices_460] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_641, vertices_769, vertices_26, vertices_42, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_396, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_644, vertices_152, vertices_280, vertices_104, vertices_168, vertices_200, vertices_328, vertices_784, vertices_352, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_789), (false, vertices_357), (false, vertices_709), (false, vertices_233), (false, vertices_801), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_396), (true, vertices_148), (true, vertices_152), (true, vertices_280), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 18 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_233) then 16 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_290) then 8 else
  if p.val = (true, vertices_396) then 17 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_328) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 7 362 42 3
cert_row_2 1 1 2 6 7 396
cert_row_4 2 0 1 3 6 8 662 146 1
cert_row_4 3 0 3 4 7 8 818 274 2
cert_rows
cert_pivot_2 5 2 1 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 2 0 1 3 6 146 662 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 362
cert_cover_5 3 0 0 2 4 5 42 362 3
cert_coverFacet 4 170
cert_cover_2 4 2 0 4 6 42 170 3
cert_coverFacet 5 818
cert_cover_5 5 3 0 3 4 7 274 818 2
cert_coverFacet 6 412
cert_cover_5 6 1 1 2 3 6 396 412 2
cert_coverFacet 7 460
cert_cover_5 7 1 1 2 5 6 396 460 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0685

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m14e10q1_0686.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0686

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 597, 409, 233, 841, 209, 118, 534, 678, 906, 242, 402, 620, 680, 73, 137, 265, 81, 145, 273, 529, 193, 577, 769, 22, 38, 518, 114, 146, 274, 530, 162, 386, 642, 770, 84, 532, 100, 548, 580, 104, 168, 552, 584, 392, 648, 776, 208, 400, 224, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_597, vertices_409, vertices_233, vertices_841, vertices_209, vertices_118, vertices_534, vertices_678, vertices_906, vertices_242, vertices_402, vertices_620, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_81, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_769, vertices_22, vertices_38, vertices_518, vertices_114, vertices_146, vertices_274, vertices_530, vertices_162, vertices_386, vertices_642, vertices_770, vertices_84, vertices_532, vertices_100, vertices_548, vertices_580, vertices_104, vertices_168, vertices_552, vertices_584, vertices_392, vertices_648, vertices_776, vertices_208, vertices_400, vertices_224, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_597), (false, vertices_409), (false, vertices_233), (false, vertices_841), (false, vertices_209), (true, vertices_22), (true, vertices_38), (true, vertices_518), (true, vertices_114), (true, vertices_146), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_100), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_209) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_114) then 15 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_114), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 5 114
cert_row_4 1 0 2 6 7 8 906 386 1
cert_row_4 2 0 1 4 6 8 678 38 3
cert_row_4 3 1 2 4 5 8 620 100 1
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 0 0 1 3 4 22 118 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 678
cert_cover_5 2 2 0 1 4 6 38 678 3
cert_coverFacet 3 906
cert_cover_5 3 1 0 2 6 7 386 906 1
cert_coverFacet 4 242
cert_cover_5 4 0 0 3 4 6 114 242 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 100 620 1
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0686

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m14e10q1_0687.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0687

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 709, 313, 681, 201, 865, 94, 662, 838, 282, 818, 220, 184, 688, 41, 73, 137, 265, 289, 545, 193, 321, 577, 641, 22, 70, 518, 26, 74, 266, 274, 530, 322, 770, 92, 148, 196, 580, 644, 56, 152, 280, 168, 200, 176, 304, 560, 656, 672, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_709, vertices_313, vertices_681, vertices_201, vertices_865, vertices_94, vertices_662, vertices_838, vertices_282, vertices_818, vertices_220, vertices_184, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_137, vertices_265, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_22, vertices_70, vertices_518, vertices_26, vertices_74, vertices_266, vertices_274, vertices_530, vertices_322, vertices_770, vertices_92, vertices_148, vertices_196, vertices_580, vertices_644, vertices_56, vertices_152, vertices_280, vertices_168, vertices_200, vertices_176, vertices_304, vertices_560, vertices_656, vertices_672, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_709), (false, vertices_313), (false, vertices_681), (false, vertices_201), (false, vertices_865), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_26), (true, vertices_274), (true, vertices_530), (true, vertices_770), (true, vertices_92), (true, vertices_148), (true, vertices_152), (true, vertices_176), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_709) then 16 else
  if p.val = (false, vertices_313) then 19 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (false, vertices_865) then 23 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_92) then 17 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_656) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 5 92
cert_row_4 1 0 1 3 6 8 662 22 3
cert_row_4 2 0 1 5 7 8 838 70 3
cert_row_4 3 0 3 4 7 8 818 274 2
cert_rows
cert_pivot_2 2 6 1 0
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 22 94 2
cert_coverFacet 1 662
cert_cover_5 1 1 0 1 3 6 22 662 3
cert_coverFacet 2 838
cert_cover_5 2 2 0 1 5 7 70 838 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 818
cert_cover_5 4 3 0 3 4 7 274 818 2
cert_coverFacet 5 220
cert_cover_5 5 0 1 2 3 6 92 220 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0687

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m14e10q1_0688.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0688

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 789, 677, 569, 217, 233, 401, 838, 646, 618, 466, 226, 674, 856, 133, 261, 517, 25, 41, 201, 145, 273, 529, 161, 545, 385, 134, 262, 518, 98, 162, 546, 194, 322, 578, 386, 642, 644, 772, 88, 536, 104, 552, 584, 208, 336, 400, 784, 224, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_789, vertices_677, vertices_569, vertices_217, vertices_233, vertices_401, vertices_838, vertices_646, vertices_618, vertices_466, vertices_226, vertices_674, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_41, vertices_201, vertices_145, vertices_273, vertices_529, vertices_161, vertices_545, vertices_385, vertices_134, vertices_262, vertices_518, vertices_98, vertices_162, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_644, vertices_772, vertices_88, vertices_536, vertices_104, vertices_552, vertices_584, vertices_208, vertices_336, vertices_400, vertices_784, vertices_224, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_789), (false, vertices_677), (false, vertices_569), (false, vertices_217), (false, vertices_233), (false, vertices_401), (true, vertices_518), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_584), (true, vertices_336), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_569) then 18 else
  if p.val = (false, vertices_217) then 19 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 7 8 838 262 2
cert_row_4 1 0 2 4 5 8 618 98 1
cert_row_4 2 0 3 5 6 7 466 194 1
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 0 0 1 5 7 262 838 2
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 618
cert_cover_5 2 1 0 2 4 5 98 618 1
cert_coverFacet 3 466
cert_cover_5 3 2 0 3 5 6 194 466 1
cert_coverFacet 4 226
cert_cover_2 4 4 0 5 6 98 226 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 856
cert_cover_5 6 3 2 3 5 7 88 856 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0688

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m14e10q1_0689.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0689

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 661, 361, 305, 465, 737, 110, 270, 406, 534, 614, 314, 332, 964, 49, 145, 273, 529, 97, 289, 545, 193, 321, 641, 14, 22, 102, 262, 518, 42, 266, 50, 274, 530, 546, 76, 268, 148, 532, 324, 580, 388, 644, 104, 296, 328, 304, 400, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_661, vertices_361, vertices_305, vertices_465, vertices_737, vertices_110, vertices_270, vertices_406, vertices_534, vertices_614, vertices_314, vertices_332, vertices_964] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_14, vertices_22, vertices_102, vertices_262, vertices_518, vertices_42, vertices_266, vertices_50, vertices_274, vertices_530, vertices_546, vertices_76, vertices_268, vertices_148, vertices_532, vertices_324, vertices_580, vertices_388, vertices_644, vertices_104, vertices_296, vertices_328, vertices_304, vertices_400, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_661), (false, vertices_361), (false, vertices_305), (false, vertices_465), (false, vertices_737), (true, vertices_14), (true, vertices_22), (true, vertices_102), (true, vertices_262), (true, vertices_518), (true, vertices_42), (true, vertices_266), (true, vertices_274), (true, vertices_76), (true, vertices_268), (true, vertices_324), (true, vertices_580), (true, vertices_388)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 14 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (false, vertices_465) then 21 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_102) then 15 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_274) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_388) then 12 else
  0
cert_priority
cert_nodeAtPriority_49 305 14 22 262 518 42 266 274 76 268 324 580 388 563 102 661 361 465 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 7 314 42 2
cert_row_2 1 0 1 4 5 102
cert_row_4 2 0 1 3 6 7 406 22 3
cert_row_4 3 1 5 6 7 8 964 324 2
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 406
cert_cover_5 2 2 0 1 3 6 22 406 3
cert_coverFacet 3 534
cert_cover_2 3 1 0 3 8 22 534 3
cert_coverFacet 4 614
cert_cover_5 4 1 0 1 4 8 102 614 3
cert_coverFacet 5 314
cert_cover_5 5 0 0 2 3 4 42 314 2
cert_coverFacet 6 332
cert_cover_2 6 2 1 5 7 76 332 3
cert_coverFacet 7 964
cert_cover_5 7 3 1 5 6 7 324 964 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0689

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m14e10q1_0690.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0690

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 557, 345, 233, 777, 625, 782, 182, 566, 390, 402, 172, 460, 496, 41, 73, 265, 521, 81, 273, 529, 97, 545, 769, 54, 134, 262, 518, 146, 274, 530, 386, 770, 44, 140, 268, 524, 164, 548, 388, 168, 200, 328, 776, 112, 176, 560, 336, 400, 224, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_557, vertices_345, vertices_233, vertices_777, vertices_625, vertices_782, vertices_182, vertices_566, vertices_390, vertices_402, vertices_172, vertices_460, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_521, vertices_81, vertices_273, vertices_529, vertices_97, vertices_545, vertices_769, vertices_54, vertices_134, vertices_262, vertices_518, vertices_146, vertices_274, vertices_530, vertices_386, vertices_770, vertices_44, vertices_140, vertices_268, vertices_524, vertices_164, vertices_548, vertices_388, vertices_168, vertices_200, vertices_328, vertices_776, vertices_112, vertices_176, vertices_560, vertices_336, vertices_400, vertices_224, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_557), (false, vertices_345), (false, vertices_233), (false, vertices_777), (false, vertices_625), (true, vertices_54), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_146), (true, vertices_386), (true, vertices_140), (true, vertices_268), (true, vertices_164), (true, vertices_388), (true, vertices_176), (true, vertices_400), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_557) then 17 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (true, vertices_54) then 15 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
cert_priority
cert_nodeAtPriority_37 777 134 262 518 146 386 140 268 164 388 176 400 448 787 54 557 345 233 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 262 2
cert_row_2 1 0 1 3 4 54
cert_row_4 2 1 2 5 6 7 460 140 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 8 0 1 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 262 782 2
cert_coverFacet 1 182
cert_cover_5 1 1 0 1 3 6 54 182 3
cert_coverFacet 2 566
cert_cover_5 2 1 0 1 3 8 54 566 3
cert_coverFacet 3 390
cert_cover_2 3 1 0 6 7 134 390 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 172
cert_cover_2 5 2 1 4 6 44 172 3
cert_coverFacet 6 460
cert_cover_5 6 2 1 2 5 6 140 460 2
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0690

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m14e10q1_0692.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0692

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 787, 611, 157, 281, 201, 721, 806, 354, 284, 364, 684, 916, 744, 67, 259, 515, 25, 73, 137, 265, 145, 273, 529, 193, 577, 98, 290, 546, 322, 770, 28, 44, 140, 268, 148, 276, 292, 548, 644, 772, 280, 104, 680, 200, 328, 656, 784, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_787, vertices_611, vertices_157, vertices_281, vertices_201, vertices_721, vertices_806, vertices_354, vertices_284, vertices_364, vertices_684, vertices_916, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_25, vertices_73, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_98, vertices_290, vertices_546, vertices_322, vertices_770, vertices_28, vertices_44, vertices_140, vertices_268, vertices_148, vertices_276, vertices_292, vertices_548, vertices_644, vertices_772, vertices_280, vertices_104, vertices_680, vertices_200, vertices_328, vertices_656, vertices_784, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_787), (false, vertices_611), (false, vertices_157), (false, vertices_281), (false, vertices_201), (false, vertices_721), (true, vertices_290), (true, vertices_44), (true, vertices_268), (true, vertices_276), (true, vertices_292), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_104), (true, vertices_680), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_611) then 15 else
  if p.val = (false, vertices_157) then 17 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (false, vertices_721) then 21 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_680) then 19 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_680), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_4 1 1 2 4 5 7 364 44 3
cert_row_2 2 2 4 6 8 680
cert_row_4 3 1 3 6 7 8 916 148 3
cert_rows
cert_pivot_2 0 5 2 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 354
cert_cover_2 1 4 0 5 7 98 354 3
cert_coverFacet 2 284
cert_cover_2 2 2 1 3 7 28 284 3
cert_coverFacet 3 364
cert_cover_5 3 1 1 2 4 5 44 364 3
cert_coverFacet 4 684
cert_cover_5 4 2 1 2 4 6 44 684 3
cert_coverFacet 5 916
cert_cover_5 5 3 1 3 6 7 148 916 3
cert_coverFacet 6 744
cert_cover_5 6 2 2 4 5 6 104 744 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0692

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m14e10q1_0694.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0694

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 309, 613, 453, 681, 417, 790, 838, 186, 538, 650, 466, 572, 432, 37, 69, 261, 161, 289, 545, 193, 577, 385, 641, 774, 26, 138, 522, 146, 274, 530, 194, 322, 578, 642, 52, 276, 532, 548, 324, 580, 56, 536, 168, 552, 648, 176, 304, 400, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_309, vertices_613, vertices_453, vertices_681, vertices_417, vertices_790, vertices_838, vertices_186, vertices_538, vertices_650, vertices_466, vertices_572, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_261, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_774, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_52, vertices_276, vertices_532, vertices_548, vertices_324, vertices_580, vertices_56, vertices_536, vertices_168, vertices_552, vertices_648, vertices_176, vertices_304, vertices_400, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_309), (false, vertices_613), (false, vertices_453), (false, vertices_681), (false, vertices_417), (true, vertices_774), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_322), (true, vertices_532), (true, vertices_56), (true, vertices_536), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_309) then 17 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_774) then 15 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 20 => Sum.inl 2
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
cert_row_4 0 0 3 5 6 7 466 146 2
cert_row_2 1 0 1 7 8 774
cert_row_4 2 0 2 3 4 6 186 26 3
cert_row_4 3 1 2 3 4 8 572 52 1
cert_rows
cert_pivot_2 5 7 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 774 790 2
cert_coverFacet 1 838
cert_cover_5 1 1 0 1 5 7 774 838 2
cert_coverFacet 2 186
cert_cover_5 2 2 0 2 3 4 26 186 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 466
cert_cover_5 5 0 0 3 5 6 146 466 2
cert_coverFacet 6 572
cert_cover_5 6 3 1 2 3 4 52 572 1
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0694

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m14e10q1_0695.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0695

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 333, 141, 613, 165, 793, 681, 358, 422, 666, 402, 786, 738, 412, 13, 37, 69, 133, 137, 265, 521, 161, 545, 321, 577, 769, 294, 146, 274, 530, 98, 162, 322, 578, 386, 642, 770, 140, 268, 100, 164, 324, 388, 152, 280, 536, 648, 400, 784, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_333, vertices_141, vertices_613, vertices_165, vertices_793, vertices_681, vertices_358, vertices_422, vertices_666, vertices_402, vertices_786, vertices_738, vertices_412] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_133, vertices_137, vertices_265, vertices_521, vertices_161, vertices_545, vertices_321, vertices_577, vertices_769, vertices_294, vertices_146, vertices_274, vertices_530, vertices_98, vertices_162, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_140, vertices_268, vertices_100, vertices_164, vertices_324, vertices_388, vertices_152, vertices_280, vertices_536, vertices_648, vertices_400, vertices_784, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_333), (false, vertices_141), (false, vertices_613), (false, vertices_165), (false, vertices_793), (false, vertices_681), (true, vertices_294), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_388), (true, vertices_152), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 13 else
  if p.val = (false, vertices_333) then 16 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_165) then 1 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (true, vertices_294) then 14 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_400) then 11 else
  0
cert_priority
cert_nodeAtPriority_10 0 141 1 165 146 274 530 98 162 386 642 388 152 400 835 294 333 613 793 681
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 6 8 738 98 3
cert_row_2 1 0 1 4 7 294
cert_row_4 2 0 2 3 6 8 666 146 1
cert_row_4 3 1 2 3 6 7 412 140 2
cert_rows
cert_pivot_2 5 4 0 1
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 1 0 1 4 5 294 358 3
cert_coverFacet 1 422
cert_cover_5 1 1 0 1 4 6 294 422 3
cert_coverFacet 2 666
cert_cover_5 2 2 0 2 3 6 146 666 1
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 738
cert_cover_5 5 0 0 4 5 6 98 738 3
cert_coverFacet 6 412
cert_cover_5 6 3 1 2 3 6 140 412 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0695

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m14e10q1_0696.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0696

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 589, 233, 777, 721, 929, 542, 110, 118, 778, 306, 914, 596, 496, 41, 73, 265, 521, 161, 289, 193, 577, 641, 769, 14, 22, 102, 42, 266, 522, 50, 274, 530, 290, 770, 76, 524, 84, 532, 580, 104, 776, 112, 304, 208, 592, 400, 656, 224, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_589, vertices_233, vertices_777, vertices_721, vertices_929, vertices_542, vertices_110, vertices_118, vertices_778, vertices_306, vertices_914, vertices_596, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_193, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_102, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_290, vertices_770, vertices_76, vertices_524, vertices_84, vertices_532, vertices_580, vertices_104, vertices_776, vertices_112, vertices_304, vertices_208, vertices_592, vertices_400, vertices_656, vertices_224, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_589), (false, vertices_233), (false, vertices_777), (false, vertices_721), (false, vertices_929), (true, vertices_14), (true, vertices_22), (true, vertices_102), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_770), (true, vertices_84), (true, vertices_532), (true, vertices_112), (true, vertices_304), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 14 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_721) then 21 else
  if p.val = (false, vertices_929) then 23 else
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
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
cert_priority
cert_nodeAtPriority_49 777 14 22 522 50 274 530 770 84 532 112 304 400 299 102 589 233 721 929
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 14 3
cert_row_2 1 0 1 4 5 102
cert_row_4 2 0 3 6 7 8 914 274 2
cert_row_4 3 3 4 5 6 7 496 112 3
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
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0696

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2463 : Certifies 2463 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0643.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2464 : Certifies 2464 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0644.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2465 : Certifies 2465 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0646.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2466 : Certifies 2466 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0647.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2467 : Certifies 2467 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0649.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2468 : Certifies 2468 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0651.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2469 : Certifies 2469 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0653.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2470 : Certifies 2470 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0655.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2471 : Certifies 2471 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0658.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2472 : Certifies 2472 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0659.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2473 : Certifies 2473 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0660.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2474 : Certifies 2474 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0668.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2475 : Certifies 2475 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0671.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2476 : Certifies 2476 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0672.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2477 : Certifies 2477 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0674.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2478 : Certifies 2478 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0675.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2479 : Certifies 2479 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0677.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2480 : Certifies 2480 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0680.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2481 : Certifies 2481 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0681.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2482 : Certifies 2482 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0682.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2483 : Certifies 2483 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0685.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2484 : Certifies 2484 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0686.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2485 : Certifies 2485 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0687.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2486 : Certifies 2486 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0688.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2487 : Certifies 2487 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0689.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2488 : Certifies 2488 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0690.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2489 : Certifies 2489 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0692.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2490 : Certifies 2490 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0694.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2491 : Certifies 2491 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0695.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2492 : Certifies 2492 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0696.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B081 (j : Fin 30) :
    Certifies (2463 + j.val) := by
  fin_cases j
  · exact projection_2463
  · exact projection_2464
  · exact projection_2465
  · exact projection_2466
  · exact projection_2467
  · exact projection_2468
  · exact projection_2469
  · exact projection_2470
  · exact projection_2471
  · exact projection_2472
  · exact projection_2473
  · exact projection_2474
  · exact projection_2475
  · exact projection_2476
  · exact projection_2477
  · exact projection_2478
  · exact projection_2479
  · exact projection_2480
  · exact projection_2481
  · exact projection_2482
  · exact projection_2483
  · exact projection_2484
  · exact projection_2485
  · exact projection_2486
  · exact projection_2487
  · exact projection_2488
  · exact projection_2489
  · exact projection_2490
  · exact projection_2491
  · exact projection_2492

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
