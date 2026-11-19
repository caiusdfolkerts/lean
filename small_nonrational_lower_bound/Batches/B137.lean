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
/- Source: ProjectionCertificates/R_m16e10q1_0254.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0254

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 677, 453, 345, 713, 777, 558, 182, 406, 122, 538, 786, 792, 616, 496, 736, 133, 261, 517, 73, 265, 521, 193, 321, 641, 769, 150, 38, 262, 518, 26, 42, 522, 50, 274, 530, 770, 164, 548, 388, 88, 280, 536, 104, 552, 584, 776, 112, 176, 336, 400, 784, 224, 608, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_677, vertices_453, vertices_345, vertices_713, vertices_777, vertices_558, vertices_182, vertices_406, vertices_122, vertices_538, vertices_786, vertices_792, vertices_616, vertices_496, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_193, vertices_321, vertices_641, vertices_769, vertices_150, vertices_38, vertices_262, vertices_518, vertices_26, vertices_42, vertices_522, vertices_50, vertices_274, vertices_530, vertices_770, vertices_164, vertices_548, vertices_388, vertices_88, vertices_280, vertices_536, vertices_104, vertices_552, vertices_584, vertices_776, vertices_112, vertices_176, vertices_336, vertices_400, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_677), (false, vertices_453), (false, vertices_345), (false, vertices_713), (false, vertices_777), (true, vertices_150), (true, vertices_38), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_536), (true, vertices_104), (true, vertices_552), (true, vertices_112), (true, vertices_176), (true, vertices_400), (true, vertices_784), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 18 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_345) then 24 else
  if p.val = (false, vertices_713) then 25 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (true, vertices_150) then 19 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_608) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_150), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
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
cert_row_4 0 0 1 2 4 8 558 38 2
cert_row_2 1 0 1 3 6 150
cert_row_4 2 0 2 3 4 5 122 26 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 8 1 0 3
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 38 558 2
cert_coverFacet 1 182
cert_cover_5 1 1 0 1 3 4 150 182 3
cert_coverFacet 2 406
cert_cover_5 2 1 0 1 3 7 150 406 3
cert_coverFacet 3 122
cert_cover_5 3 2 0 2 3 4 26 122 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 792
cert_cover_2 6 3 2 7 8 280 792 3
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coverFacet 9 736
cert_cover_2 9 5 4 6 8 224 736 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0254

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0255.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0255

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 333, 309, 677, 709, 849, 206, 154, 538, 842, 178, 738, 396, 420, 440, 792, 37, 69, 645, 261, 49, 273, 529, 545, 321, 577, 26, 74, 138, 522, 50, 146, 530, 162, 546, 194, 578, 76, 140, 268, 164, 292, 196, 388, 152, 280, 536, 328, 392, 776, 176, 304, 784, 416, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_333, vertices_309, vertices_677, vertices_709, vertices_849, vertices_206, vertices_154, vertices_538, vertices_842, vertices_178, vertices_738, vertices_396, vertices_420, vertices_440, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_645, vertices_261, vertices_49, vertices_273, vertices_529, vertices_545, vertices_321, vertices_577, vertices_26, vertices_74, vertices_138, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_546, vertices_194, vertices_578, vertices_76, vertices_140, vertices_268, vertices_164, vertices_292, vertices_196, vertices_388, vertices_152, vertices_280, vertices_536, vertices_328, vertices_392, vertices_776, vertices_176, vertices_304, vertices_784, vertices_416, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_333), (false, vertices_309), (false, vertices_677), (false, vertices_709), (false, vertices_849), (true, vertices_26), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_162), (true, vertices_194), (true, vertices_578), (true, vertices_140), (true, vertices_388), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_392), (true, vertices_776), (true, vertices_176), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 19 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 18 else
  if p.val = (false, vertices_333) then 20 else
  if p.val = (false, vertices_309) then 22 else
  if p.val = (false, vertices_677) then 23 else
  if p.val = (false, vertices_709) then 24 else
  if p.val = (false, vertices_849) then 26 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_776) then 14 else
  if p.val = (true, vertices_176) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 74 1
cert_row_4 1 2 3 4 6 7 440 152 2
cert_row_4 2 0 2 5 7 8 842 74 3
cert_row_4 3 0 4 5 6 8 738 162 2
cert_rows
cert_pivot_2 1 3 2 0
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 74 206 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 842
cert_cover_5 3 2 0 2 5 7 74 842 3
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 738
cert_cover_5 5 3 0 4 5 6 162 738 2
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coverFacet 8 440
cert_cover_5 8 1 2 3 4 6 152 440 2
cert_coverFacet 9 792
cert_cover_2 9 3 2 7 8 280 792 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0255

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0256.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0256

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 405, 613, 453, 233, 689, 286, 774, 538, 682, 298, 866, 836, 472, 664, 360, 21, 69, 389, 517, 145, 529, 97, 161, 545, 193, 22, 262, 518, 26, 42, 266, 522, 530, 290, 546, 770, 276, 324, 580, 772, 152, 280, 536, 104, 168, 296, 200, 328, 648, 400, 656, 352, 608, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_405, vertices_613, vertices_453, vertices_233, vertices_689, vertices_286, vertices_774, vertices_538, vertices_682, vertices_298, vertices_866, vertices_836, vertices_472, vertices_664, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_389, vertices_517, vertices_145, vertices_529, vertices_97, vertices_161, vertices_545, vertices_193, vertices_22, vertices_262, vertices_518, vertices_26, vertices_42, vertices_266, vertices_522, vertices_530, vertices_290, vertices_546, vertices_770, vertices_276, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_296, vertices_200, vertices_328, vertices_648, vertices_400, vertices_656, vertices_352, vertices_608, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_405), (false, vertices_613), (false, vertices_453), (false, vertices_233), (false, vertices_689), (true, vertices_262), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_772), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_296), (true, vertices_328), (true, vertices_648), (true, vertices_352), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 18 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_233) then 24 else
  if p.val = (false, vertices_689) then 26 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_352) then 15 else
  if p.val = (true, vertices_832) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 7 286 22 2
cert_row_4 1 2 3 5 6 7 472 152 2
cert_row_4 2 0 2 4 6 8 682 42 3
cert_row_4 3 0 4 5 7 8 866 290 2
cert_rows
cert_pivot_2 1 3 2 0
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 22 286 2
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 682
cert_cover_5 3 2 0 2 4 6 42 682 3
cert_coverFacet 4 298
cert_cover_2 4 2 0 4 7 42 298 3
cert_coverFacet 5 866
cert_cover_5 5 3 0 4 5 7 290 866 2
cert_coverFacet 6 836
cert_cover_2 6 5 1 7 8 324 836 3
cert_coverFacet 7 472
cert_cover_5 7 1 2 3 5 6 152 472 2
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coverFacet 9 360
cert_cover_2 9 4 2 5 7 104 360 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0256

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0257.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0257

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [211, 301, 597, 789, 229, 433, 782, 154, 282, 650, 850, 738, 620, 408, 424, 680, 533, 37, 69, 261, 81, 145, 273, 161, 289, 193, 26, 138, 266, 522, 82, 146, 274, 194, 578, 642, 770, 44, 268, 524, 100, 580, 772, 152, 280, 168, 296, 552, 392, 648, 592, 400, 784, 224, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_301, vertices_597, vertices_789, vertices_229, vertices_433, vertices_782, vertices_154, vertices_282, vertices_650, vertices_850, vertices_738, vertices_620, vertices_408, vertices_424, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_533, vertices_37, vertices_69, vertices_261, vertices_81, vertices_145, vertices_273, vertices_161, vertices_289, vertices_193, vertices_26, vertices_138, vertices_266, vertices_522, vertices_82, vertices_146, vertices_274, vertices_194, vertices_578, vertices_642, vertices_770, vertices_44, vertices_268, vertices_524, vertices_100, vertices_580, vertices_772, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_592, vertices_400, vertices_784, vertices_224, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_301), (false, vertices_597), (false, vertices_789), (false, vertices_229), (false, vertices_433), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_524), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_552), (true, vertices_392), (true, vertices_648), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 19 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 18 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_597) then 22 else
  if p.val = (false, vertices_789) then 23 else
  if p.val = (false, vertices_229) then 24 else
  if p.val = (false, vertices_433) then 26 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_608) then 15 else
  if p.val = (true, vertices_672) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 7 8 850 82 3
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 1 2 4 5 8 620 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 850
cert_cover_5 4 0 0 3 5 7 82 850 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 194 738 1
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 44 620 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coverFacet 9 680
cert_cover_2 9 4 2 6 8 168 680 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0257

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0258.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0258

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 779, 227, 675, 117, 805, 666, 458, 60, 412, 556, 780, 340, 568, 752, 464, 163, 67, 259, 515, 37, 69, 261, 97, 545, 769, 138, 266, 522, 194, 322, 642, 28, 44, 268, 524, 52, 84, 276, 548, 324, 772, 56, 152, 536, 552, 392, 776, 112, 560, 208, 336, 400, 656, 224, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_779, vertices_227, vertices_675, vertices_117, vertices_805, vertices_666, vertices_458, vertices_60, vertices_412, vertices_556, vertices_780, vertices_340, vertices_568, vertices_752, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_163, vertices_67, vertices_259, vertices_515, vertices_37, vertices_69, vertices_261, vertices_97, vertices_545, vertices_769, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_642, vertices_28, vertices_44, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_548, vertices_324, vertices_772, vertices_56, vertices_152, vertices_536, vertices_552, vertices_392, vertices_776, vertices_112, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_224, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_779), (false, vertices_227), (false, vertices_675), (false, vertices_117), (false, vertices_805), (true, vertices_138), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_552), (true, vertices_392), (true, vertices_560), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_656), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 21 17 25 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 18 else
  if p.val = (false, vertices_779) then 22 else
  if p.val = (false, vertices_227) then 23 else
  if p.val = (false, vertices_675) then 24 else
  if p.val = (false, vertices_117) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_28) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_656) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inl 0
  | 22 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 25 => Sum.inl 2
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 6 7 412 28 3
cert_row_4 1 0 2 5 6 7 458 138 2
cert_row_4 2 0 2 3 6 8 666 138 2
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 1 7 0 3
cert_heightProof 4
cert_coverFacet 0 666
cert_cover_5 0 2 0 2 3 6 138 666 2
cert_coverFacet 1 458
cert_cover_5 1 1 0 2 5 6 138 458 2
cert_coverFacet 2 60
cert_cover_2 2 2 1 3 4 28 60 3
cert_coverFacet 3 412
cert_cover_5 3 0 1 2 3 6 28 412 3
cert_coverFacet 4 556
cert_cover_2 4 2 1 4 8 44 556 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 112 752 3
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0258

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0259.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0259

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 563, 355, 345, 601, 433, 654, 198, 226, 674, 412, 780, 484, 836, 696, 840, 35, 67, 515, 89, 49, 273, 529, 289, 321, 577, 70, 134, 518, 98, 162, 546, 194, 642, 140, 268, 524, 196, 324, 580, 388, 772, 152, 280, 536, 328, 584, 648, 776, 176, 560, 400, 224, 352, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_563, vertices_355, vertices_345, vertices_601, vertices_433, vertices_654, vertices_198, vertices_226, vertices_674, vertices_412, vertices_780, vertices_484, vertices_836, vertices_696, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_515, vertices_89, vertices_49, vertices_273, vertices_529, vertices_289, vertices_321, vertices_577, vertices_70, vertices_134, vertices_518, vertices_98, vertices_162, vertices_546, vertices_194, vertices_642, vertices_140, vertices_268, vertices_524, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_152, vertices_280, vertices_536, vertices_328, vertices_584, vertices_648, vertices_776, vertices_176, vertices_560, vertices_400, vertices_224, vertices_352, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_563), (false, vertices_355), (false, vertices_345), (false, vertices_601), (false, vertices_433), (true, vertices_134), (true, vertices_162), (true, vertices_194), (true, vertices_642), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_772), (true, vertices_152), (true, vertices_648), (true, vertices_776), (true, vertices_224), (true, vertices_672), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 18 else
  if p.val = (false, vertices_563) then 19 else
  if p.val = (false, vertices_355) then 20 else
  if p.val = (false, vertices_345) then 23 else
  if p.val = (false, vertices_601) then 24 else
  if p.val = (false, vertices_433) then 26 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_672) then 15 else
  if p.val = (true, vertices_832) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 134 2
cert_row_4 1 1 4 5 6 7 484 196 1
cert_row_4 2 1 2 3 6 7 412 140 2
cert_row_4 3 2 3 4 6 8 696 152 2
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 134 654 2
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 226
cert_cover_2 2 4 0 5 6 98 226 3
cert_coverFacet 3 674
cert_cover_2 3 4 0 6 8 162 674 3
cert_coverFacet 4 412
cert_cover_5 4 2 1 2 3 6 140 412 2
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 484
cert_cover_5 6 1 1 4 5 6 196 484 1
cert_coverFacet 7 836
cert_cover_2 7 5 1 7 8 324 836 3
cert_coverFacet 8 696
cert_cover_5 8 3 2 3 4 6 152 696 2
cert_coverFacet 9 840
cert_cover_2 9 5 2 7 8 328 840 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0259

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0260.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0260

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 781, 565, 421, 369, 833, 174, 558, 218, 842, 658, 674, 460, 432, 688, 464, 37, 261, 517, 49, 81, 529, 289, 321, 577, 769, 46, 74, 138, 522, 82, 146, 530, 162, 546, 578, 642, 140, 268, 524, 164, 548, 388, 200, 328, 776, 176, 304, 560, 208, 336, 400, 656, 416, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_781, vertices_565, vertices_421, vertices_369, vertices_833, vertices_174, vertices_558, vertices_218, vertices_842, vertices_658, vertices_674, vertices_460, vertices_432, vertices_688, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_49, vertices_81, vertices_529, vertices_289, vertices_321, vertices_577, vertices_769, vertices_46, vertices_74, vertices_138, vertices_522, vertices_82, vertices_146, vertices_530, vertices_162, vertices_546, vertices_578, vertices_642, vertices_140, vertices_268, vertices_524, vertices_164, vertices_548, vertices_388, vertices_200, vertices_328, vertices_776, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_416, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_781), (false, vertices_565), (false, vertices_421), (false, vertices_369), (false, vertices_833), (true, vertices_46), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_162), (true, vertices_546), (true, vertices_642), (true, vertices_140), (true, vertices_200), (true, vertices_328), (true, vertices_176), (true, vertices_208), (true, vertices_400), (true, vertices_656), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 18 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_565) then 22 else
  if p.val = (false, vertices_421) then 23 else
  if p.val = (false, vertices_369) then 26 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_46) then 19 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_672) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
cert_nodeAtPriority_45 833 74 138 522 146 162 546 642 140 200 328 176 208 400 656 672 448 595 46 781 565 421 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 2 3 5 6 218 74 2
cert_row_4 2 0 2 5 7 8 842 74 3
cert_row_4 3 1 2 5 6 7 460 140 2
cert_rows
cert_pivot_2 4 3 0 1
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 0 0 1 2 6 46 174 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 8 46 558 3
cert_coverFacet 2 218
cert_cover_5 2 1 0 2 3 5 74 218 2
cert_coverFacet 3 842
cert_cover_5 3 2 0 2 5 7 74 842 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 460
cert_cover_5 6 3 1 2 5 6 140 460 2
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0260

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0261.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0261

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 163, 803, 333, 713, 849, 673, 182, 626, 402, 786, 412, 620, 684, 116, 340, 35, 131, 259, 73, 137, 265, 161, 545, 321, 577, 641, 769, 50, 146, 274, 530, 162, 546, 386, 770, 556, 76, 140, 268, 52, 84, 148, 276, 100, 164, 324, 584, 392, 648, 112, 336, 592, 400, 784, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_163, vertices_803, vertices_333, vertices_713, vertices_849, vertices_673, vertices_182, vertices_626, vertices_402, vertices_786, vertices_412, vertices_620, vertices_684, vertices_116, vertices_340] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_73, vertices_137, vertices_265, vertices_161, vertices_545, vertices_321, vertices_577, vertices_641, vertices_769, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_386, vertices_770, vertices_556, vertices_76, vertices_140, vertices_268, vertices_52, vertices_84, vertices_148, vertices_276, vertices_100, vertices_164, vertices_324, vertices_584, vertices_392, vertices_648, vertices_112, vertices_336, vertices_592, vertices_400, vertices_784, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_163), (false, vertices_803), (false, vertices_333), (false, vertices_713), (false, vertices_849), (false, vertices_673), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_556), (true, vertices_140), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_100), (true, vertices_164), (true, vertices_112), (true, vertices_400), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 17 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_333) then 20 else
  if p.val = (false, vertices_713) then 23 else
  if p.val = (false, vertices_849) then 25 else
  if p.val = (false, vertices_673) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_556) then 21 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_164) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_608) then 15 else
  0
cert_priority
cert_nodeAtPriority_61 0 163 1 673 50 146 274 530 140 52 84 148 276 100 164 112 400 608 395 803 333 556 713 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 8 626 50 3
cert_row_2 1 1 2 4 8 556
cert_row_4 2 0 1 3 4 6 182 50 1
cert_row_4 3 1 2 3 6 7 412 140 2
cert_rows
cert_pivot_2 5 8 0 1
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 2 0 1 3 4 50 182 1
cert_coverFacet 1 626
cert_cover_5 1 0 0 3 4 5 50 626 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 412
cert_cover_5 4 3 1 2 3 6 140 412 2
cert_coverFacet 5 620
cert_cover_5 5 1 1 2 4 5 556 620 3
cert_coverFacet 6 684
cert_cover_5 6 1 1 2 4 6 556 684 3
cert_coverFacet 7 116
cert_cover_2 7 3 1 4 5 52 116 3
cert_coverFacet 8 340
cert_cover_2 8 3 1 5 7 84 340 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0261

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0262.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0262

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 93, 309, 325, 537, 457, 913, 422, 234, 618, 818, 898, 628, 228, 452, 600, 21, 69, 261, 25, 73, 137, 521, 273, 529, 321, 385, 641, 106, 138, 522, 162, 290, 546, 386, 642, 770, 52, 84, 100, 164, 292, 196, 324, 388, 88, 536, 200, 584, 304, 560, 592, 784, 224, 608, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_93, vertices_309, vertices_325, vertices_537, vertices_457, vertices_913, vertices_422, vertices_234, vertices_618, vertices_818, vertices_898, vertices_628, vertices_228, vertices_452, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_261, vertices_25, vertices_73, vertices_137, vertices_521, vertices_273, vertices_529, vertices_321, vertices_385, vertices_641, vertices_106, vertices_138, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_100, vertices_164, vertices_292, vertices_196, vertices_324, vertices_388, vertices_88, vertices_536, vertices_200, vertices_584, vertices_304, vertices_560, vertices_592, vertices_784, vertices_224, vertices_608, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_93), (false, vertices_309), (false, vertices_325), (false, vertices_537), (false, vertices_457), (false, vertices_913), (true, vertices_106), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_770), (true, vertices_100), (true, vertices_164), (true, vertices_196), (true, vertices_388), (true, vertices_584), (true, vertices_560), (true, vertices_592), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 17 else
  if p.val = (false, vertices_93) then 20 else
  if p.val = (false, vertices_309) then 21 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (false, vertices_913) then 25 else
  if p.val = (true, vertices_106) then 18 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_608) then 15 else
  0
cert_priority
cert_nodeAtPriority_50 1 325 0 537 162 290 546 386 770 100 164 196 388 584 560 592 224 608 651 106 93 309 457 913
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 1 4 6 7 422 162 1
cert_row_4 2 0 3 4 7 8 818 290 1
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 1 0 1 4 6 162 422 1
cert_coverFacet 1 234
cert_cover_5 1 0 0 2 4 6 106 234 3
cert_coverFacet 2 618
cert_cover_5 2 0 0 2 4 8 106 618 3
cert_coverFacet 3 818
cert_cover_5 3 2 0 3 4 7 290 818 1
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 628
cert_cover_5 5 3 1 3 4 5 52 628 3
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 452
cert_cover_2 7 5 1 6 7 196 452 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0262

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0263.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0263

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 661, 837, 345, 625, 401, 654, 358, 614, 570, 170, 418, 120, 408, 664, 488, 133, 261, 517, 81, 145, 273, 529, 321, 577, 385, 102, 134, 262, 518, 42, 138, 522, 162, 290, 546, 386, 324, 580, 644, 56, 88, 152, 280, 536, 104, 168, 328, 392, 648, 112, 560, 400, 656, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_661, vertices_837, vertices_345, vertices_625, vertices_401, vertices_654, vertices_358, vertices_614, vertices_570, vertices_170, vertices_418, vertices_120, vertices_408, vertices_664, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_273, vertices_529, vertices_321, vertices_577, vertices_385, vertices_102, vertices_134, vertices_262, vertices_518, vertices_42, vertices_138, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_324, vertices_580, vertices_644, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_328, vertices_392, vertices_648, vertices_112, vertices_560, vertices_400, vertices_656, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_661), (false, vertices_837), (false, vertices_345), (false, vertices_625), (false, vertices_401), (true, vertices_102), (true, vertices_518), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_104), (true, vertices_168), (true, vertices_392), (true, vertices_648), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 18 else
  if p.val = (false, vertices_661) then 21 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (false, vertices_345) then 24 else
  if p.val = (false, vertices_625) then 26 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (true, vertices_102) then 19 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_352) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
cert_nodeAtPriority_14 401 518 42 138 522 162 290 546 56 152 536 104 168 392 648 352 416 391 102 661 837 345 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 42 2
cert_row_4 1 0 1 2 6 8 654 134 2
cert_row_2 2 0 1 4 5 102
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 3 8 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 134 654 2
cert_coverFacet 1 358
cert_cover_5 1 2 0 1 4 7 102 358 3
cert_coverFacet 2 614
cert_cover_5 2 2 0 1 4 8 102 614 3
cert_coverFacet 3 570
cert_cover_5 3 0 0 2 3 4 42 570 2
cert_coverFacet 4 170
cert_cover_2 4 2 0 4 6 42 170 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coverFacet 9 488
cert_cover_5 9 3 2 4 5 6 104 488 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0263

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0264.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0264

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 93, 541, 357, 901, 625, 654, 570, 154, 178, 482, 898, 332, 396, 472, 240, 29, 69, 261, 517, 81, 529, 97, 289, 545, 769, 26, 138, 522, 50, 146, 162, 290, 546, 386, 642, 770, 76, 140, 268, 524, 324, 388, 644, 88, 152, 536, 328, 392, 112, 176, 560, 208, 224, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_93, vertices_541, vertices_357, vertices_901, vertices_625, vertices_654, vertices_570, vertices_154, vertices_178, vertices_482, vertices_898, vertices_332, vertices_396, vertices_472, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_69, vertices_261, vertices_517, vertices_81, vertices_529, vertices_97, vertices_289, vertices_545, vertices_769, vertices_26, vertices_138, vertices_522, vertices_50, vertices_146, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_268, vertices_524, vertices_324, vertices_388, vertices_644, vertices_88, vertices_152, vertices_536, vertices_328, vertices_392, vertices_112, vertices_176, vertices_560, vertices_208, vertices_224, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_93), (false, vertices_541), (false, vertices_357), (false, vertices_901), (false, vertices_625), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_140), (true, vertices_268), (true, vertices_152), (true, vertices_328), (true, vertices_392), (true, vertices_176), (true, vertices_208), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 22 19 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_93) then 20 else
  if p.val = (false, vertices_541) then 21 else
  if p.val = (false, vertices_357) then 23 else
  if p.val = (false, vertices_901) then 24 else
  if p.val = (false, vertices_625) then 26 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_4 1 0 2 3 4 8 570 26 3
cert_row_4 2 0 4 5 6 7 482 162 2
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 570
cert_cover_5 1 1 0 2 3 4 26 570 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 482
cert_cover_5 4 2 0 4 5 6 162 482 2
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 332
cert_cover_2 6 2 1 5 7 76 332 3
cert_coverFacet 7 396
cert_cover_2 7 2 1 6 7 140 396 3
cert_coverFacet 8 472
cert_cover_5 8 3 2 3 5 6 88 472 3
cert_coverFacet 9 240
cert_cover_2 9 4 3 5 6 112 240 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0264

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0265.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0265

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 203, 675, 771, 789, 581, 617, 169, 914, 450, 124, 348, 692, 612, 440, 456, 67, 131, 259, 515, 69, 261, 517, 41, 73, 137, 161, 545, 577, 769, 194, 322, 386, 642, 770, 92, 52, 276, 532, 100, 548, 324, 580, 56, 280, 104, 168, 200, 328, 392, 176, 400, 656, 784, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_203, vertices_675, vertices_771, vertices_789, vertices_581, vertices_617, vertices_169, vertices_914, vertices_450, vertices_124, vertices_348, vertices_692, vertices_612, vertices_440, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_69, vertices_261, vertices_517, vertices_41, vertices_73, vertices_137, vertices_161, vertices_545, vertices_577, vertices_769, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_92, vertices_52, vertices_276, vertices_532, vertices_100, vertices_548, vertices_324, vertices_580, vertices_56, vertices_280, vertices_104, vertices_168, vertices_200, vertices_328, vertices_392, vertices_176, vertices_400, vertices_656, vertices_784, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_203), (false, vertices_675), (false, vertices_771), (false, vertices_789), (false, vertices_581), (false, vertices_617), (false, vertices_169), (true, vertices_386), (true, vertices_92), (true, vertices_52), (true, vertices_100), (true, vertices_548), (true, vertices_56), (true, vertices_280), (true, vertices_328), (true, vertices_392), (true, vertices_176), (true, vertices_400), (true, vertices_656), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 16 else
  if p.val = (false, vertices_203) then 17 else
  if p.val = (false, vertices_675) then 18 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_581) then 1 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_169) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_92) then 21 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 22 => Sum.inl 2
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
cert_row_2 0 1 2 3 5 92
cert_row_4 1 0 3 6 7 8 914 386 1
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 914
cert_cover_5 0 1 0 3 6 7 386 914 1
cert_coverFacet 1 450
cert_cover_2 1 5 0 6 7 194 450 3
cert_coverFacet 2 124
cert_cover_5 2 0 1 2 3 4 92 124 3
cert_coverFacet 3 348
cert_cover_5 3 0 1 2 3 7 92 348 3
cert_coverFacet 4 692
cert_cover_5 4 2 1 3 4 6 52 692 3
cert_coverFacet 5 612
cert_cover_2 5 4 1 5 8 100 612 3
cert_coverFacet 6 440
cert_cover_5 6 3 2 3 4 6 56 440 3
cert_coverFacet 7 456
cert_cover_2 7 5 2 6 7 200 456 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0265

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0266.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0266

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 397, 357, 709, 777, 849, 614, 678, 122, 794, 170, 594, 436, 184, 408, 368, 69, 133, 261, 137, 265, 521, 321, 577, 641, 769, 550, 26, 42, 138, 522, 82, 530, 98, 162, 578, 642, 100, 164, 292, 580, 388, 644, 56, 152, 280, 168, 392, 776, 112, 176, 304, 336, 592, 400, 784, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_397, vertices_357, vertices_709, vertices_777, vertices_849, vertices_614, vertices_678, vertices_122, vertices_794, vertices_170, vertices_594, vertices_436, vertices_184, vertices_408, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_137, vertices_265, vertices_521, vertices_321, vertices_577, vertices_641, vertices_769, vertices_550, vertices_26, vertices_42, vertices_138, vertices_522, vertices_82, vertices_530, vertices_98, vertices_162, vertices_578, vertices_642, vertices_100, vertices_164, vertices_292, vertices_580, vertices_388, vertices_644, vertices_56, vertices_152, vertices_280, vertices_168, vertices_392, vertices_776, vertices_112, vertices_176, vertices_304, vertices_336, vertices_592, vertices_400, vertices_784, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_397), (false, vertices_357), (false, vertices_709), (false, vertices_777), (false, vertices_849), (true, vertices_550), (true, vertices_26), (true, vertices_42), (true, vertices_82), (true, vertices_530), (true, vertices_98), (true, vertices_162), (true, vertices_578), (true, vertices_164), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_397) then 21 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_709) then 23 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_849) then 26 else
  if p.val = (true, vertices_550) then 19 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_304) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
cert_nodeAtPriority_45 777 26 42 82 530 98 162 578 164 56 152 280 168 112 176 304 400 651 550 397 357 709 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 5 122 26 3
cert_row_4 1 0 2 3 7 8 794 26 3
cert_row_2 2 0 1 4 8 550
cert_row_4 3 1 3 4 6 7 436 164 1
cert_rows
cert_pivot_2 5 2 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 2 0 1 4 5 550 614 3
cert_coverFacet 1 678
cert_cover_5 1 2 0 1 4 6 550 678 3
cert_coverFacet 2 122
cert_cover_5 2 0 0 2 3 4 26 122 3
cert_coverFacet 3 794
cert_cover_5 3 1 0 2 3 7 26 794 3
cert_coverFacet 4 170
cert_cover_2 4 2 0 4 6 42 170 3
cert_coverFacet 5 594
cert_cover_2 5 3 0 5 8 82 594 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 164 436 1
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 368
cert_cover_2 9 4 3 5 7 112 368 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0266

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0267.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0267

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 357, 165, 709, 809, 689, 94, 334, 570, 778, 722, 156, 396, 212, 420, 440, 37, 69, 133, 161, 289, 545, 321, 577, 641, 769, 78, 26, 266, 522, 82, 530, 322, 578, 770, 28, 140, 268, 84, 148, 164, 292, 196, 324, 388, 56, 152, 296, 552, 392, 776, 176, 560, 208, 656, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_357, vertices_165, vertices_709, vertices_809, vertices_689, vertices_94, vertices_334, vertices_570, vertices_778, vertices_722, vertices_156, vertices_396, vertices_212, vertices_420, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_133, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_641, vertices_769, vertices_78, vertices_26, vertices_266, vertices_522, vertices_82, vertices_530, vertices_322, vertices_578, vertices_770, vertices_28, vertices_140, vertices_268, vertices_84, vertices_148, vertices_164, vertices_292, vertices_196, vertices_324, vertices_388, vertices_56, vertices_152, vertices_296, vertices_552, vertices_392, vertices_776, vertices_176, vertices_560, vertices_208, vertices_656, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_357), (false, vertices_165), (false, vertices_709), (false, vertices_809), (false, vertices_689), (true, vertices_78), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_82), (true, vertices_530), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_84), (true, vertices_148), (true, vertices_388), (true, vertices_56), (true, vertices_152), (true, vertices_392), (true, vertices_208), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_809) then 24 else
  if p.val = (false, vertices_689) then 26 else
  if p.val = (true, vertices_78) then 19 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
cert_nodeAtPriority_14 165 26 266 522 82 530 28 140 268 84 148 388 56 152 392 208 416 835 78 357 709 809 689
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 3 5 6 8 722 82 3
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 78 94 3
cert_coverFacet 1 334
cert_cover_5 1 0 0 1 2 7 78 334 3
cert_coverFacet 2 570
cert_cover_5 2 2 0 2 3 4 26 570 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 722
cert_cover_5 4 1 0 3 5 6 82 722 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coverFacet 8 420
cert_cover_2 8 4 1 6 7 164 420 3
cert_coverFacet 9 440
cert_cover_5 9 3 2 3 4 6 56 440 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0267

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0268.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0268

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 781, 57, 409, 617, 369, 398, 230, 614, 774, 466, 652, 692, 568, 664, 240, 25, 41, 265, 521, 49, 273, 97, 321, 577, 769, 102, 134, 262, 518, 194, 322, 578, 386, 770, 140, 268, 524, 164, 548, 644, 772, 56, 152, 536, 552, 392, 648, 112, 176, 560, 208, 336, 400, 656, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_781, vertices_57, vertices_409, vertices_617, vertices_369, vertices_398, vertices_230, vertices_614, vertices_774, vertices_466, vertices_652, vertices_692, vertices_568, vertices_664, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_521, vertices_49, vertices_273, vertices_97, vertices_321, vertices_577, vertices_769, vertices_102, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_140, vertices_268, vertices_524, vertices_164, vertices_548, vertices_644, vertices_772, vertices_56, vertices_152, vertices_536, vertices_552, vertices_392, vertices_648, vertices_112, vertices_176, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_781), (false, vertices_57), (false, vertices_409), (false, vertices_617), (false, vertices_369), (true, vertices_102), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_194), (true, vertices_386), (true, vertices_140), (true, vertices_164), (true, vertices_548), (true, vertices_644), (true, vertices_536), (true, vertices_648), (true, vertices_176), (true, vertices_560), (true, vertices_208), (true, vertices_656), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_409) then 23 else
  if p.val = (false, vertices_617) then 24 else
  if p.val = (false, vertices_369) then 26 else
  if p.val = (true, vertices_102) then 19 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_656) then 15 else
  if p.val = (true, vertices_224) then 16 else
  0
cert_priority
cert_nodeAtPriority_33 57 134 262 518 194 386 140 164 548 644 536 648 176 560 208 656 224 835 102 781 409 617 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_4 1 0 3 5 6 7 466 194 1
cert_row_2 2 0 1 4 5 102
cert_row_4 3 1 3 4 6 8 692 164 1
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 230
cert_cover_5 1 2 0 1 4 6 102 230 3
cert_coverFacet 2 614
cert_cover_5 2 2 0 1 4 8 102 614 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 466
cert_cover_5 4 1 0 3 5 6 194 466 1
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 164 692 1
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coverFacet 9 240
cert_cover_2 9 4 3 5 6 112 240 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0268

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0269.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0269

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 333, 709, 773, 817, 481, 590, 58, 218, 554, 434, 706, 572, 284, 788, 472, 69, 261, 517, 161, 289, 545, 193, 321, 641, 769, 26, 42, 74, 522, 50, 146, 162, 546, 194, 578, 642, 28, 76, 268, 524, 276, 532, 580, 772, 56, 216, 280, 552, 328, 304, 560, 400, 784, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_333, vertices_709, vertices_773, vertices_817, vertices_481, vertices_590, vertices_58, vertices_218, vertices_554, vertices_434, vertices_706, vertices_572, vertices_284, vertices_788, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_769, vertices_26, vertices_42, vertices_74, vertices_522, vertices_50, vertices_146, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_76, vertices_268, vertices_524, vertices_276, vertices_532, vertices_580, vertices_772, vertices_56, vertices_216, vertices_280, vertices_552, vertices_328, vertices_304, vertices_560, vertices_400, vertices_784, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_333), (false, vertices_709), (false, vertices_773), (false, vertices_817), (false, vertices_481), (true, vertices_26), (true, vertices_42), (true, vertices_74), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_194), (true, vertices_578), (true, vertices_28), (true, vertices_524), (true, vertices_276), (true, vertices_532), (true, vertices_56), (true, vertices_216), (true, vertices_280), (true, vertices_552), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 18 else
  if p.val = (false, vertices_333) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_817) then 25 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_56) then 13 else
  if p.val = (true, vertices_216) then 23 else
  if p.val = (true, vertices_280) then 14 else
  if p.val = (true, vertices_552) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
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
cert_row_4 0 0 3 4 6 7 434 50 3
cert_row_2 1 2 3 5 6 216
cert_row_4 2 0 1 2 5 8 590 74 1
cert_row_4 3 1 2 3 4 8 572 28 3
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 2 0 1 2 5 74 590 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 218
cert_cover_5 2 1 0 2 3 5 26 218 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 434
cert_cover_5 4 0 0 3 4 6 50 434 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 572
cert_cover_5 6 3 1 2 3 4 28 572 3
cert_coverFacet 7 284
cert_cover_2 7 2 1 3 7 28 284 3
cert_coverFacet 8 788
cert_cover_2 8 3 1 7 8 276 788 3
cert_coverFacet 9 472
cert_cover_5 9 1 2 3 5 7 216 472 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0269

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0270.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0270

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 781, 121, 281, 817, 737, 270, 526, 406, 678, 458, 706, 244, 308, 804, 472, 25, 73, 265, 521, 49, 273, 97, 545, 577, 769, 14, 134, 262, 518, 74, 266, 522, 194, 578, 386, 642, 268, 524, 52, 148, 276, 164, 292, 548, 772, 88, 280, 456, 112, 304, 208, 400, 224, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_781, vertices_121, vertices_281, vertices_817, vertices_737, vertices_270, vertices_526, vertices_406, vertices_678, vertices_458, vertices_706, vertices_244, vertices_308, vertices_804, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_521, vertices_49, vertices_273, vertices_97, vertices_545, vertices_577, vertices_769, vertices_14, vertices_134, vertices_262, vertices_518, vertices_74, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_642, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_164, vertices_292, vertices_548, vertices_772, vertices_88, vertices_280, vertices_456, vertices_112, vertices_304, vertices_208, vertices_400, vertices_224, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_781), (false, vertices_121), (false, vertices_281), (false, vertices_817), (false, vertices_737), (true, vertices_14), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_456), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 21 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 18 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_121) then 22 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_817) then 25 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_164) then 12 else
  if p.val = (true, vertices_292) then 13 else
  if p.val = (true, vertices_548) then 14 else
  if p.val = (true, vertices_456) then 23 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 23 => Sum.inr ⟨(true, vertices_456), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 5 6 7 456
cert_row_4 1 0 1 3 6 7 406 134 2
cert_row_4 2 0 1 4 6 8 678 134 2
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 406
cert_cover_5 2 1 0 1 3 6 134 406 2
cert_coverFacet 3 678
cert_cover_5 3 2 0 1 4 6 134 678 2
cert_coverFacet 4 458
cert_cover_5 4 0 0 2 5 6 74 458 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 244
cert_cover_5 6 3 1 3 4 5 52 244 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coverFacet 8 804
cert_cover_2 8 4 1 7 8 292 804 3
cert_coverFacet 9 472
cert_cover_5 9 0 2 3 5 6 88 472 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0270

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0271.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0271

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 789, 345, 625, 481, 897, 158, 110, 614, 646, 426, 604, 404, 900, 408, 360, 81, 273, 529, 97, 161, 545, 321, 385, 641, 769, 14, 102, 134, 518, 42, 138, 162, 546, 642, 28, 76, 148, 276, 532, 580, 388, 644, 772, 88, 152, 280, 104, 296, 328, 392, 592, 400, 352, 608, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_789, vertices_345, vertices_625, vertices_481, vertices_897, vertices_158, vertices_110, vertices_614, vertices_646, vertices_426, vertices_604, vertices_404, vertices_900, vertices_408, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_102, vertices_134, vertices_518, vertices_42, vertices_138, vertices_162, vertices_546, vertices_642, vertices_28, vertices_76, vertices_148, vertices_276, vertices_532, vertices_580, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_104, vertices_296, vertices_328, vertices_392, vertices_592, vertices_400, vertices_352, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_789), (false, vertices_345), (false, vertices_625), (false, vertices_481), (false, vertices_897), (true, vertices_14), (true, vertices_102), (true, vertices_134), (true, vertices_518), (true, vertices_42), (true, vertices_138), (true, vertices_28), (true, vertices_76), (true, vertices_148), (true, vertices_580), (true, vertices_388), (true, vertices_644), (true, vertices_152), (true, vertices_104), (true, vertices_296), (true, vertices_392), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 18 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_345) then 23 else
  if p.val = (false, vertices_625) then 25 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_102) then 19 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_104) then 13 else
  if p.val = (true, vertices_296) then 14 else
  if p.val = (true, vertices_392) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
cert_nodeAtPriority_66 897 14 134 518 42 138 28 76 148 580 388 644 152 104 296 392 400 675 102 789 345 625 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 42 3
cert_row_2 1 0 1 4 5 102
cert_row_4 2 0 1 2 3 6 158 14 3
cert_row_4 3 1 2 3 5 8 604 28 3
cert_rows
cert_pivot_2 7 4 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 2 0 1 2 3 14 158 3
cert_coverFacet 1 110
cert_cover_5 1 1 0 1 2 4 14 110 3
cert_coverFacet 2 614
cert_cover_5 2 1 0 1 4 8 102 614 3
cert_coverFacet 3 646
cert_cover_2 3 1 0 6 8 134 646 3
cert_coverFacet 4 426
cert_cover_5 4 0 0 2 4 6 42 426 3
cert_coverFacet 5 604
cert_cover_5 5 3 1 2 3 5 28 604 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 900
cert_cover_2 7 6 1 7 8 388 900 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 360
cert_cover_2 9 4 2 5 7 104 360 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0271

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0272.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0272

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 157, 269, 805, 709, 233, 297, 598, 794, 466, 482, 802, 540, 780, 212, 440, 13, 133, 261, 517, 41, 137, 265, 97, 289, 545, 193, 577, 82, 274, 530, 98, 290, 546, 450, 578, 770, 28, 268, 524, 84, 148, 532, 196, 580, 772, 152, 280, 536, 168, 296, 776, 208, 400, 224, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_157, vertices_269, vertices_805, vertices_709, vertices_233, vertices_297, vertices_598, vertices_794, vertices_466, vertices_482, vertices_802, vertices_540, vertices_780, vertices_212, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_517, vertices_41, vertices_137, vertices_265, vertices_97, vertices_289, vertices_545, vertices_193, vertices_577, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_450, vertices_578, vertices_770, vertices_28, vertices_268, vertices_524, vertices_84, vertices_148, vertices_532, vertices_196, vertices_580, vertices_772, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_776, vertices_208, vertices_400, vertices_224, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_157), (false, vertices_269), (false, vertices_805), (false, vertices_709), (false, vertices_233), (false, vertices_297), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_450), (true, vertices_770), (true, vertices_524), (true, vertices_84), (true, vertices_532), (true, vertices_280), (true, vertices_536), (true, vertices_776), (true, vertices_208), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_157) then 20 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_233) then 24 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_450) then 18 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
cert_nodeAtPriority_5 0 269 1 297 82 274 530 290 770 524 84 532 280 536 776 208 400 416 611 450 157 805 709 233
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 82 1
cert_row_2 1 0 5 6 7 450
cert_row_4 2 0 2 3 7 8 794 274 1
cert_row_4 3 2 3 4 6 7 440 152 2
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 82 598 1
cert_coverFacet 1 794
cert_cover_5 1 2 0 2 3 7 274 794 1
cert_coverFacet 2 466
cert_cover_5 2 1 0 3 5 6 82 466 3
cert_coverFacet 3 482
cert_cover_5 3 1 0 4 5 6 98 482 3
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coverFacet 8 440
cert_cover_5 8 3 2 3 4 6 152 440 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0272

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0273.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0273

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 781, 565, 293, 617, 393, 481, 662, 122, 570, 650, 466, 372, 404, 900, 904, 37, 261, 517, 73, 137, 265, 521, 97, 289, 545, 193, 385, 58, 74, 138, 522, 82, 146, 530, 194, 642, 52, 148, 276, 532, 292, 388, 644, 772, 104, 552, 392, 648, 776, 112, 560, 336, 400, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_781, vertices_565, vertices_293, vertices_617, vertices_393, vertices_481, vertices_662, vertices_122, vertices_570, vertices_650, vertices_466, vertices_372, vertices_404, vertices_900, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_521, vertices_97, vertices_289, vertices_545, vertices_193, vertices_385, vertices_58, vertices_74, vertices_138, vertices_522, vertices_82, vertices_146, vertices_530, vertices_194, vertices_642, vertices_52, vertices_148, vertices_276, vertices_532, vertices_292, vertices_388, vertices_644, vertices_772, vertices_104, vertices_552, vertices_392, vertices_648, vertices_776, vertices_112, vertices_560, vertices_336, vertices_400, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_781), (false, vertices_565), (false, vertices_293), (false, vertices_617), (false, vertices_393), (false, vertices_481), (true, vertices_58), (true, vertices_522), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_642), (true, vertices_148), (true, vertices_276), (true, vertices_388), (true, vertices_644), (true, vertices_648), (true, vertices_112), (true, vertices_336), (true, vertices_400), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 17 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_565) then 21 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_393) then 1 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_58) then 18 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 1 293 0 393 522 82 146 530 642 148 276 388 644 648 112 336 400 896 203 58 781 565 617 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 4 58
cert_row_4 1 0 1 3 6 8 662 146 1
cert_row_4 2 0 3 5 6 7 466 82 3
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 146 662 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 5 58 122 3
cert_coverFacet 2 570
cert_cover_5 2 0 0 2 3 8 58 570 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 466
cert_cover_5 4 2 0 3 5 6 82 466 3
cert_coverFacet 5 372
cert_cover_5 5 3 1 3 4 5 52 372 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 900
cert_cover_2 7 6 1 7 8 388 900 3
cert_coverFacet 8 904
cert_cover_2 8 6 2 7 8 392 904 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0273

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0274.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0274

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 651, 355, 451, 205, 525, 117, 914, 802, 92, 284, 812, 308, 728, 792, 496, 35, 323, 131, 515, 13, 37, 69, 517, 137, 521, 97, 193, 290, 546, 386, 642, 770, 28, 76, 268, 524, 52, 84, 276, 292, 548, 88, 280, 536, 200, 648, 776, 112, 304, 208, 400, 656, 784, 352, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_651, vertices_355, vertices_451, vertices_205, vertices_525, vertices_117, vertices_914, vertices_802, vertices_92, vertices_284, vertices_812, vertices_308, vertices_728, vertices_792, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_323, vertices_131, vertices_515, vertices_13, vertices_37, vertices_69, vertices_517, vertices_137, vertices_521, vertices_97, vertices_193, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_292, vertices_548, vertices_88, vertices_280, vertices_536, vertices_200, vertices_648, vertices_776, vertices_112, vertices_304, vertices_208, vertices_400, vertices_656, vertices_784, vertices_352, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_651), (false, vertices_355), (false, vertices_451), (false, vertices_205), (false, vertices_525), (false, vertices_117), (true, vertices_770), (true, vertices_28), (true, vertices_268), (true, vertices_276), (true, vertices_292), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_776), (true, vertices_304), (true, vertices_208), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 20 16 24 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 17 else
  if p.val = (false, vertices_651) then 21 else
  if p.val = (false, vertices_355) then 22 else
  if p.val = (false, vertices_451) then 23 else
  if p.val = (false, vertices_205) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_117) then 19 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 20 => Sum.inl 0
  | 21 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 24 => Sum.inl 2
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 6 7 8 914 386 1
cert_row_4 1 1 2 4 7 8 812 268 2
cert_row_4 2 2 3 5 6 8 728 88 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 914
cert_cover_5 0 0 0 3 6 7 386 914 1
cert_coverFacet 1 802
cert_cover_2 1 4 0 7 8 290 802 3
cert_coverFacet 2 92
cert_cover_2 2 2 1 3 5 28 92 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 812
cert_cover_5 4 1 1 2 4 7 268 812 2
cert_coverFacet 5 308
cert_cover_2 5 3 1 4 7 52 308 3
cert_coverFacet 6 728
cert_cover_5 6 2 2 3 5 6 88 728 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0274

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0275.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0275

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 213, 357, 677, 809, 705, 94, 334, 570, 778, 722, 156, 396, 420, 440, 688, 37, 69, 133, 289, 545, 193, 321, 577, 641, 769, 78, 26, 266, 522, 82, 530, 322, 578, 770, 28, 140, 268, 84, 148, 164, 292, 324, 388, 56, 152, 296, 552, 392, 776, 176, 560, 208, 656, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_213, vertices_357, vertices_677, vertices_809, vertices_705, vertices_94, vertices_334, vertices_570, vertices_778, vertices_722, vertices_156, vertices_396, vertices_420, vertices_440, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_133, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_78, vertices_26, vertices_266, vertices_522, vertices_82, vertices_530, vertices_322, vertices_578, vertices_770, vertices_28, vertices_140, vertices_268, vertices_84, vertices_148, vertices_164, vertices_292, vertices_324, vertices_388, vertices_56, vertices_152, vertices_296, vertices_552, vertices_392, vertices_776, vertices_176, vertices_560, vertices_208, vertices_656, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_213), (false, vertices_357), (false, vertices_677), (false, vertices_809), (false, vertices_705), (true, vertices_78), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_82), (true, vertices_530), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_388), (true, vertices_56), (true, vertices_152), (true, vertices_392), (true, vertices_176), (true, vertices_560), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_213) then 21 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_677) then 23 else
  if p.val = (false, vertices_809) then 25 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_78) then 19 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_656) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
cert_nodeAtPriority_63 705 26 266 522 82 530 28 140 268 388 56 152 392 176 560 656 416 835 78 213 357 677 809
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 3 5 6 8 722 82 3
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 78 94 3
cert_coverFacet 1 334
cert_cover_5 1 0 0 1 2 7 78 334 3
cert_coverFacet 2 570
cert_cover_5 2 2 0 2 3 4 26 570 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 722
cert_cover_5 4 1 0 3 5 6 82 722 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coverFacet 8 440
cert_cover_5 8 3 2 3 4 6 56 440 3
cert_coverFacet 9 688
cert_cover_2 9 4 3 6 8 176 688 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0275

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0276.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0276

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 781, 345, 617, 241, 305, 398, 230, 614, 774, 434, 652, 724, 600, 408, 664, 73, 265, 521, 49, 81, 273, 97, 289, 545, 769, 102, 134, 262, 518, 162, 290, 546, 386, 770, 140, 268, 524, 196, 580, 644, 772, 88, 152, 280, 536, 584, 392, 648, 176, 304, 208, 592, 400, 656, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_781, vertices_345, vertices_617, vertices_241, vertices_305, vertices_398, vertices_230, vertices_614, vertices_774, vertices_434, vertices_652, vertices_724, vertices_600, vertices_408, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_49, vertices_81, vertices_273, vertices_97, vertices_289, vertices_545, vertices_769, vertices_102, vertices_134, vertices_262, vertices_518, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_140, vertices_268, vertices_524, vertices_196, vertices_580, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_536, vertices_584, vertices_392, vertices_648, vertices_176, vertices_304, vertices_208, vertices_592, vertices_400, vertices_656, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_781), (false, vertices_345), (false, vertices_617), (false, vertices_241), (false, vertices_305), (true, vertices_102), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_162), (true, vertices_386), (true, vertices_140), (true, vertices_196), (true, vertices_580), (true, vertices_644), (true, vertices_152), (true, vertices_536), (true, vertices_392), (true, vertices_648), (true, vertices_592), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_345) then 23 else
  if p.val = (false, vertices_617) then 24 else
  if p.val = (false, vertices_241) then 26 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (true, vertices_102) then 19 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_656) then 16 else
  0
cert_priority
cert_nodeAtPriority_33 305 134 262 518 162 386 140 196 580 644 152 536 392 648 592 400 656 803 102 781 345 617 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_4 1 0 3 4 6 7 434 162 1
cert_row_2 2 0 1 4 5 102
cert_row_4 3 1 3 5 6 8 724 196 1
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 230
cert_cover_5 1 2 0 1 4 6 102 230 3
cert_coverFacet 2 614
cert_cover_5 2 2 0 1 4 8 102 614 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 434
cert_cover_5 4 1 0 3 4 6 162 434 1
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 196 724 1
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 664
cert_cover_2 9 3 2 6 8 152 664 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0276

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0277.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0277

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 589, 397, 181, 533, 329, 913, 422, 362, 242, 722, 898, 60, 540, 300, 632, 13, 21, 133, 517, 73, 265, 145, 529, 321, 577, 385, 769, 210, 98, 162, 290, 322, 578, 386, 642, 770, 28, 44, 268, 524, 52, 532, 164, 292, 388, 56, 536, 104, 296, 328, 584, 112, 176, 592, 656, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_589, vertices_397, vertices_181, vertices_533, vertices_329, vertices_913, vertices_422, vertices_362, vertices_242, vertices_722, vertices_898, vertices_60, vertices_540, vertices_300, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_133, vertices_517, vertices_73, vertices_265, vertices_145, vertices_529, vertices_321, vertices_577, vertices_385, vertices_769, vertices_210, vertices_98, vertices_162, vertices_290, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_524, vertices_52, vertices_532, vertices_164, vertices_292, vertices_388, vertices_56, vertices_536, vertices_104, vertices_296, vertices_328, vertices_584, vertices_112, vertices_176, vertices_592, vertices_656, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_589), (false, vertices_397), (false, vertices_181), (false, vertices_533), (false, vertices_329), (false, vertices_913), (true, vertices_210), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_642), (true, vertices_28), (true, vertices_44), (true, vertices_292), (true, vertices_56), (true, vertices_536), (true, vertices_104), (true, vertices_296), (true, vertices_112), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_589) then 20 else
  if p.val = (false, vertices_397) then 21 else
  if p.val = (false, vertices_181) then 22 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (false, vertices_913) then 25 else
  if p.val = (true, vertices_210) then 18 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_112) then 14 else
  if p.val = (true, vertices_592) then 15 else
  0
cert_priority
cert_nodeAtPriority_21 0 533 1 329 98 162 290 386 642 28 44 292 56 536 104 296 112 592 835 210 589 397 181 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 7 422 162 1
cert_row_2 1 0 3 5 6 210
cert_row_4 2 0 2 4 5 7 362 98 1
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 162 422 1
cert_coverFacet 1 362
cert_cover_5 1 2 0 2 4 5 98 362 1
cert_coverFacet 2 242
cert_cover_5 2 1 0 3 4 5 210 242 2
cert_coverFacet 3 722
cert_cover_5 3 1 0 3 5 8 210 722 3
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 300
cert_cover_2 7 2 1 4 7 44 300 3
cert_coverFacet 8 632
cert_cover_5 8 3 2 3 4 5 56 632 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0277

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0278.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0278

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 565, 277, 357, 233, 553, 841, 406, 218, 602, 482, 834, 684, 660, 420, 664, 21, 37, 261, 41, 73, 521, 273, 529, 97, 545, 321, 769, 90, 146, 274, 530, 194, 322, 578, 386, 770, 148, 276, 532, 164, 292, 548, 388, 644, 152, 536, 168, 552, 200, 584, 648, 656, 224, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_565, vertices_277, vertices_357, vertices_233, vertices_553, vertices_841, vertices_406, vertices_218, vertices_602, vertices_482, vertices_834, vertices_684, vertices_660, vertices_420, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_261, vertices_41, vertices_73, vertices_521, vertices_273, vertices_529, vertices_97, vertices_545, vertices_321, vertices_769, vertices_90, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_152, vertices_536, vertices_168, vertices_552, vertices_200, vertices_584, vertices_648, vertices_656, vertices_224, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_565), (false, vertices_277), (false, vertices_357), (false, vertices_233), (false, vertices_553), (false, vertices_841), (true, vertices_90), (true, vertices_146), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_148), (true, vertices_164), (true, vertices_388), (true, vertices_644), (true, vertices_152), (true, vertices_536), (true, vertices_648), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 17 else
  if p.val = (false, vertices_565) then 20 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_841) then 24 else
  if p.val = (true, vertices_90) then 18 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
cert_nodeAtPriority_39 0 277 1 553 146 194 322 578 386 148 164 388 644 152 536 648 656 416 787 90 565 357 233 841
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 6 8 684 164 1
cert_row_2 1 0 2 3 5 90
cert_row_4 2 0 1 3 6 7 406 146 1
cert_row_4 3 0 4 5 6 7 482 194 1
cert_rows
cert_pivot_2 8 2 1 0
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 2 0 1 3 6 146 406 1
cert_coverFacet 1 218
cert_cover_5 1 1 0 2 3 6 90 218 3
cert_coverFacet 2 602
cert_cover_5 2 1 0 2 3 8 90 602 3
cert_coverFacet 3 482
cert_cover_5 3 3 0 4 5 6 194 482 1
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 684
cert_cover_5 5 0 1 2 4 6 164 684 1
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0278

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0279.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0279

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 307, 163, 707, 205, 421, 581, 794, 562, 674, 604, 396, 780, 376, 488, 752, 35, 131, 259, 515, 69, 133, 261, 517, 161, 289, 193, 577, 50, 274, 530, 162, 546, 642, 770, 76, 140, 268, 524, 580, 388, 772, 88, 280, 536, 360, 200, 392, 776, 112, 304, 560, 592, 224, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_307, vertices_163, vertices_707, vertices_205, vertices_421, vertices_581, vertices_794, vertices_562, vertices_674, vertices_604, vertices_396, vertices_780, vertices_376, vertices_488, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_69, vertices_133, vertices_261, vertices_517, vertices_161, vertices_289, vertices_193, vertices_577, vertices_50, vertices_274, vertices_530, vertices_162, vertices_546, vertices_642, vertices_770, vertices_76, vertices_140, vertices_268, vertices_524, vertices_580, vertices_388, vertices_772, vertices_88, vertices_280, vertices_536, vertices_360, vertices_200, vertices_392, vertices_776, vertices_112, vertices_304, vertices_560, vertices_592, vertices_224, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_307), (false, vertices_163), (false, vertices_707), (false, vertices_205), (false, vertices_421), (false, vertices_581), (true, vertices_530), (true, vertices_546), (true, vertices_268), (true, vertices_524), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_360), (true, vertices_392), (true, vertices_776), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_307) then 18 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_707) then 19 else
  if p.val = (false, vertices_205) then 21 else
  if p.val = (false, vertices_421) then 22 else
  if p.val = (false, vertices_581) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_360) then 24 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(true, vertices_360), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 7 8 794 274 1
cert_row_2 1 2 4 5 7 360
cert_row_4 2 1 2 3 5 8 604 76 2
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 7 1 3
cert_heightProof 4
cert_coverFacet 0 794
cert_cover_5 0 0 0 2 3 7 274 794 1
cert_coverFacet 1 562
cert_cover_2 1 3 0 4 8 50 562 3
cert_coverFacet 2 674
cert_cover_2 2 4 0 6 8 162 674 3
cert_coverFacet 3 604
cert_cover_5 3 2 1 2 3 5 76 604 2
cert_coverFacet 4 396
cert_cover_2 4 2 1 6 7 140 396 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 376
cert_cover_5 6 1 2 3 4 5 88 376 2
cert_coverFacet 7 488
cert_cover_5 7 1 2 4 5 6 360 488 3
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 112 752 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0279

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0280.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0280

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 555, 403, 163, 341, 533, 689, 234, 394, 778, 364, 812, 724, 612, 472, 736, 35, 131, 259, 515, 21, 261, 517, 145, 273, 529, 161, 545, 42, 138, 266, 522, 162, 386, 770, 300, 84, 532, 100, 548, 324, 580, 772, 104, 552, 200, 328, 392, 776, 208, 336, 400, 656, 224, 608, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_555, vertices_403, vertices_163, vertices_341, vertices_533, vertices_689, vertices_234, vertices_394, vertices_778, vertices_364, vertices_812, vertices_724, vertices_612, vertices_472, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_21, vertices_261, vertices_517, vertices_145, vertices_273, vertices_529, vertices_161, vertices_545, vertices_42, vertices_138, vertices_266, vertices_522, vertices_162, vertices_386, vertices_770, vertices_300, vertices_84, vertices_532, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_104, vertices_552, vertices_200, vertices_328, vertices_392, vertices_776, vertices_208, vertices_336, vertices_400, vertices_656, vertices_224, vertices_608, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_555), (false, vertices_403), (false, vertices_163), (false, vertices_341), (false, vertices_533), (false, vertices_689), (true, vertices_138), (true, vertices_266), (true, vertices_300), (true, vertices_100), (true, vertices_548), (true, vertices_580), (true, vertices_104), (true, vertices_200), (true, vertices_328), (true, vertices_392), (true, vertices_776), (true, vertices_208), (true, vertices_224), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_555) then 18 else
  if p.val = (false, vertices_403) then 19 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_341) then 21 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_689) then 25 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_300) then 22 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_608) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_300), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 6 234 42 3
cert_row_2 1 1 2 4 7 300
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 2 3 5 6 7 472 200 1
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 234
cert_cover_5 0 0 0 2 4 5 42 234 3
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 364
cert_cover_5 3 1 1 2 4 5 300 364 3
cert_coverFacet 4 812
cert_cover_5 4 1 1 2 4 8 300 812 3
cert_coverFacet 5 724
cert_cover_5 5 2 1 3 5 6 84 724 3
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 200 472 1
cert_coverFacet 8 736
cert_cover_2 8 5 4 6 8 224 736 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0280

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0281.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0281

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 179, 403, 611, 841, 481, 278, 534, 570, 668, 236, 332, 780, 468, 184, 616, 147, 35, 259, 515, 97, 161, 321, 577, 385, 769, 22, 262, 518, 50, 274, 530, 546, 76, 140, 268, 524, 148, 276, 532, 196, 324, 772, 56, 152, 536, 104, 168, 552, 328, 584, 776, 176, 400, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_179, vertices_403, vertices_611, vertices_841, vertices_481, vertices_278, vertices_534, vertices_570, vertices_668, vertices_236, vertices_332, vertices_780, vertices_468, vertices_184, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_147, vertices_35, vertices_259, vertices_515, vertices_97, vertices_161, vertices_321, vertices_577, vertices_385, vertices_769, vertices_22, vertices_262, vertices_518, vertices_50, vertices_274, vertices_530, vertices_546, vertices_76, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_772, vertices_56, vertices_152, vertices_536, vertices_104, vertices_168, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_400, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_179), (false, vertices_403), (false, vertices_611), (false, vertices_841), (false, vertices_481), (true, vertices_22), (true, vertices_530), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_196), (true, vertices_324), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_104), (true, vertices_168), (true, vertices_552)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 17 23 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 18 else
  if p.val = (false, vertices_179) then 20 else
  if p.val = (false, vertices_403) then 21 else
  if p.val = (false, vertices_611) then 22 else
  if p.val = (false, vertices_841) then 24 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_104) then 14 else
  if p.val = (true, vertices_168) then 15 else
  if p.val = (true, vertices_552) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
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
cert_row_4 0 0 2 3 4 8 570 50 1
cert_row_4 1 1 2 3 6 8 668 140 2
cert_row_4 2 1 2 4 5 6 236 76 2
cert_row_4 3 1 3 5 6 7 468 148 2
cert_rows
cert_pivot_2 0 8 2 1
cert_heightProof 4
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 570
cert_cover_5 2 0 0 2 3 4 50 570 1
cert_coverFacet 3 668
cert_cover_5 3 1 1 2 3 6 140 668 2
cert_coverFacet 4 236
cert_cover_5 4 2 1 2 4 5 76 236 2
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 468
cert_cover_5 7 3 1 3 5 6 148 468 2
cert_coverFacet 8 184
cert_cover_2 8 3 2 4 6 56 184 3
cert_coverFacet 9 616
cert_cover_2 9 4 2 5 8 104 616 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0281

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0282.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0282

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 419, 707, 117, 293, 581, 233, 410, 666, 786, 60, 284, 428, 852, 632, 712, 131, 259, 515, 37, 69, 261, 517, 97, 161, 289, 193, 577, 154, 274, 530, 386, 642, 770, 28, 44, 268, 52, 84, 276, 292, 580, 772, 56, 280, 536, 104, 168, 200, 584, 392, 648, 112, 592, 784, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_419, vertices_707, vertices_117, vertices_293, vertices_581, vertices_233, vertices_410, vertices_666, vertices_786, vertices_60, vertices_284, vertices_428, vertices_852, vertices_632, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_37, vertices_69, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_193, vertices_577, vertices_154, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_52, vertices_84, vertices_276, vertices_292, vertices_580, vertices_772, vertices_56, vertices_280, vertices_536, vertices_104, vertices_168, vertices_200, vertices_584, vertices_392, vertices_648, vertices_112, vertices_592, vertices_784, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_419), (false, vertices_707), (false, vertices_117), (false, vertices_293), (false, vertices_581), (false, vertices_233), (true, vertices_154), (true, vertices_274), (true, vertices_530), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_276), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_584), (true, vertices_392), (true, vertices_648), (true, vertices_592), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 22 16 19 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_419) then 23 else
  if p.val = (false, vertices_707) then 24 else
  if p.val = (false, vertices_117) then 18 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_581) then 1 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (true, vertices_154) then 21 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 22 => Sum.inl 0
  | 23 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 1 3 5 7 8 852 84 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 410
cert_cover_5 0 0 0 2 3 7 154 410 3
cert_coverFacet 1 666
cert_cover_5 1 0 0 2 3 8 154 666 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 428
cert_cover_5 5 1 1 2 4 6 44 428 3
cert_coverFacet 6 852
cert_cover_5 6 2 1 3 5 7 84 852 3
cert_coverFacet 7 632
cert_cover_5 7 3 2 3 4 5 56 632 3
cert_coverFacet 8 712
cert_cover_2 8 5 2 6 8 200 712 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0282

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0283.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0283

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [59, 283, 803, 397, 681, 961, 614, 114, 466, 834, 124, 284, 556, 652, 724, 404, 27, 35, 259, 41, 137, 265, 545, 385, 641, 769, 50, 82, 274, 98, 546, 322, 578, 770, 28, 44, 140, 268, 524, 84, 148, 276, 100, 548, 580, 388, 644, 56, 280, 552, 648, 112, 208, 400, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_59, vertices_283, vertices_803, vertices_397, vertices_681, vertices_961, vertices_614, vertices_114, vertices_466, vertices_834, vertices_124, vertices_284, vertices_556, vertices_652, vertices_724, vertices_404] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_35, vertices_259, vertices_41, vertices_137, vertices_265, vertices_545, vertices_385, vertices_641, vertices_769, vertices_50, vertices_82, vertices_274, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_44, vertices_140, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_100, vertices_548, vertices_580, vertices_388, vertices_644, vertices_56, vertices_280, vertices_552, vertices_648, vertices_112, vertices_208, vertices_400, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_59), (false, vertices_283), (false, vertices_803), (false, vertices_397), (false, vertices_681), (false, vertices_961), (true, vertices_82), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_28), (true, vertices_44), (true, vertices_524), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_100), (true, vertices_548), (true, vertices_580), (true, vertices_644), (true, vertices_112), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 23 25 26 27 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_59) then 18 else
  if p.val = (false, vertices_283) then 19 else
  if p.val = (false, vertices_803) then 20 else
  if p.val = (false, vertices_397) then 22 else
  if p.val = (false, vertices_681) then 24 else
  if p.val = (false, vertices_961) then 28 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_580) then 12 else
  if p.val = (true, vertices_644) then 13 else
  if p.val = (true, vertices_112) then 14 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 7 466 82 3
cert_row_4 1 0 1 4 5 8 614 98 1
cert_row_4 2 1 2 3 4 5 124 28 3
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 7 0 2 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 1 0 1 4 5 98 614 1
cert_coverFacet 1 114
cert_cover_2 1 3 0 4 5 50 114 3
cert_coverFacet 2 466
cert_cover_5 2 0 0 3 5 6 82 466 3
cert_coverFacet 3 834
cert_cover_2 3 5 0 7 8 322 834 3
cert_coverFacet 4 124
cert_cover_5 4 2 1 2 3 4 28 124 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 724
cert_cover_5 8 3 1 3 5 6 84 724 3
cert_coverFacet 9 404
cert_cover_2 9 3 1 6 7 148 404 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0283

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_4143 : Certifies 4143 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0254.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4144 : Certifies 4144 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0255.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4145 : Certifies 4145 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0256.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4146 : Certifies 4146 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0257.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4147 : Certifies 4147 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0258.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4148 : Certifies 4148 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0259.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4149 : Certifies 4149 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0260.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4150 : Certifies 4150 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0261.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4151 : Certifies 4151 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0262.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4152 : Certifies 4152 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0263.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4153 : Certifies 4153 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0264.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4154 : Certifies 4154 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0265.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4155 : Certifies 4155 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0266.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4156 : Certifies 4156 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0267.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4157 : Certifies 4157 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0268.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4158 : Certifies 4158 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0269.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4159 : Certifies 4159 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0270.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4160 : Certifies 4160 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0271.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4161 : Certifies 4161 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0272.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4162 : Certifies 4162 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0273.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4163 : Certifies 4163 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0274.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4164 : Certifies 4164 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0275.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4165 : Certifies 4165 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0276.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4166 : Certifies 4166 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0277.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4167 : Certifies 4167 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0278.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4168 : Certifies 4168 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0279.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4169 : Certifies 4169 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0280.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4170 : Certifies 4170 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0281.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4171 : Certifies 4171 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0282.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4172 : Certifies 4172 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0283.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B137 (j : Fin 30) :
    Certifies (4143 + j.val) := by
  fin_cases j
  · exact projection_4143
  · exact projection_4144
  · exact projection_4145
  · exact projection_4146
  · exact projection_4147
  · exact projection_4148
  · exact projection_4149
  · exact projection_4150
  · exact projection_4151
  · exact projection_4152
  · exact projection_4153
  · exact projection_4154
  · exact projection_4155
  · exact projection_4156
  · exact projection_4157
  · exact projection_4158
  · exact projection_4159
  · exact projection_4160
  · exact projection_4161
  · exact projection_4162
  · exact projection_4163
  · exact projection_4164
  · exact projection_4165
  · exact projection_4166
  · exact projection_4167
  · exact projection_4168
  · exact projection_4169
  · exact projection_4170
  · exact projection_4171
  · exact projection_4172

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
