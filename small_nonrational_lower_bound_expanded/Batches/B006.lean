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
/- Source: ProjectionCertificates/R_m13e11q2_0016.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0016

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 109, 397, 789, 613, 713, 566, 362, 458, 306, 786, 738, 316, 13, 101, 261, 517, 73, 137, 577, 385, 641, 769, 330, 50, 274, 530, 98, 290, 546, 194, 386, 642, 770, 44, 268, 52, 276, 532, 548, 104, 296, 200, 392, 304, 784, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_109, vertices_397, vertices_789, vertices_613, vertices_713, vertices_566, vertices_362, vertices_458, vertices_306, vertices_786, vertices_738, vertices_316] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_101, vertices_261, vertices_517, vertices_73, vertices_137, vertices_577, vertices_385, vertices_641, vertices_769, vertices_330, vertices_50, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_194, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_52, vertices_276, vertices_532, vertices_548, vertices_104, vertices_296, vertices_200, vertices_392, vertices_304, vertices_784, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_109), (false, vertices_397), (false, vertices_789), (false, vertices_613), (false, vertices_713), (true, vertices_330), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_194), (true, vertices_52), (true, vertices_296), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 16 13 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 11 else
  if p.val = (false, vertices_109) then 17 else
  if p.val = (false, vertices_397) then 14 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_713) then 15 else
  if p.val = (true, vertices_330) then 12 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_304) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_330), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 6 8 738 98 3
cert_row_2 1 0 2 5 7 330
cert_row_4 2 0 1 3 4 8 566 50 1
cert_row_4 3 1 2 3 4 7 316 44 2
cert_rows
cert_pivot_2 6 5 0 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 2 0 1 3 4 50 566 1
cert_coverFacet 1 362
cert_cover_5 1 1 0 2 4 5 330 362 2
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 6 330 458 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 738
cert_cover_5 5 0 0 4 5 6 98 738 3
cert_coverFacet 6 316
cert_cover_5 6 3 1 2 3 4 44 316 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0016

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m13e11q2_0017.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0017

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [87, 535, 653, 453, 849, 929, 558, 206, 234, 114, 818, 680, 496, 23, 69, 133, 517, 81, 529, 321, 385, 641, 769, 14, 70, 518, 42, 202, 50, 82, 530, 98, 546, 140, 524, 196, 168, 552, 648, 112, 304, 336, 784, 224, 416, 672, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_87, vertices_535, vertices_653, vertices_453, vertices_849, vertices_929, vertices_558, vertices_206, vertices_234, vertices_114, vertices_818, vertices_680, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_69, vertices_133, vertices_517, vertices_81, vertices_529, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_70, vertices_518, vertices_42, vertices_202, vertices_50, vertices_82, vertices_530, vertices_98, vertices_546, vertices_140, vertices_524, vertices_196, vertices_168, vertices_552, vertices_648, vertices_112, vertices_304, vertices_336, vertices_784, vertices_224, vertices_416, vertices_672, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_87), (false, vertices_535), (false, vertices_653), (false, vertices_453), (false, vertices_849), (false, vertices_929), (true, vertices_14), (true, vertices_42), (true, vertices_202), (true, vertices_50), (true, vertices_98), (true, vertices_546), (true, vertices_168), (true, vertices_552), (true, vertices_112), (true, vertices_304), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 14 17 18 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_87) then 11 else
  if p.val = (false, vertices_535) then 12 else
  if p.val = (false, vertices_653) then 15 else
  if p.val = (false, vertices_453) then 16 else
  if p.val = (false, vertices_849) then 19 else
  if p.val = (false, vertices_929) then 21 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_202) then 13 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_224) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_87), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 14 3
cert_row_2 1 0 2 5 6 202
cert_row_4 2 0 3 4 7 8 818 50 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 14 558 3
cert_coverFacet 1 206
cert_cover_5 1 1 0 1 2 5 14 206 3
cert_coverFacet 2 234
cert_cover_5 2 1 0 2 4 5 42 234 3
cert_coverFacet 3 114
cert_cover_2 3 3 0 4 5 50 114 3
cert_coverFacet 4 818
cert_cover_5 4 2 0 3 4 7 50 818 3
cert_coverFacet 5 680
cert_cover_2 5 4 2 6 8 168 680 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0017

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m13e11q2_0018.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0018

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 787, 901, 601, 457, 737, 302, 678, 774, 122, 626, 484, 360, 275, 25, 73, 265, 529, 193, 577, 385, 641, 769, 38, 262, 518, 26, 42, 266, 114, 530, 546, 770, 164, 292, 388, 644, 772, 88, 104, 296, 328, 592, 224, 352, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_787, vertices_901, vertices_601, vertices_457, vertices_737, vertices_302, vertices_678, vertices_774, vertices_122, vertices_626, vertices_484, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_275, vertices_25, vertices_73, vertices_265, vertices_529, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_38, vertices_262, vertices_518, vertices_26, vertices_42, vertices_266, vertices_114, vertices_530, vertices_546, vertices_770, vertices_164, vertices_292, vertices_388, vertices_644, vertices_772, vertices_88, vertices_104, vertices_296, vertices_328, vertices_592, vertices_224, vertices_352, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_787), (false, vertices_901), (false, vertices_601), (false, vertices_457), (false, vertices_737), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_42), (true, vertices_114), (true, vertices_546), (true, vertices_164), (true, vertices_292), (true, vertices_104), (true, vertices_296), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 10 12 21 15 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 19 else
  if p.val = (false, vertices_787) then 20 else
  if p.val = (false, vertices_901) then 11 else
  if p.val = (false, vertices_601) then 13 else
  if p.val = (false, vertices_457) then 14 else
  if p.val = (false, vertices_737) then 16 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_114) then 17 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_352) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 15 => Sum.inl 4
  | 16 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_114), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 5 114
cert_row_4 1 0 1 2 4 7 302 38 2
cert_row_4 2 0 1 4 6 8 678 38 3
cert_row_4 3 1 4 5 6 7 484 164 2
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 1 0 1 2 4 38 302 2
cert_coverFacet 1 678
cert_cover_5 1 2 0 1 4 6 38 678 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 122
cert_cover_5 3 0 0 2 3 4 26 122 3
cert_coverFacet 4 626
cert_cover_5 4 0 0 3 4 8 114 626 3
cert_coverFacet 5 484
cert_cover_5 5 3 1 4 5 6 164 484 2
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0018

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m13e11q2_0020.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0020

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [59, 331, 179, 899, 837, 601, 657, 230, 454, 106, 620, 932, 696, 11, 51, 131, 259, 25, 73, 145, 529, 321, 577, 641, 769, 198, 42, 74, 98, 162, 322, 386, 100, 164, 548, 324, 580, 388, 772, 56, 536, 104, 552, 584, 176, 656, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_59, vertices_331, vertices_179, vertices_899, vertices_837, vertices_601, vertices_657, vertices_230, vertices_454, vertices_106, vertices_620, vertices_932, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_51, vertices_131, vertices_259, vertices_25, vertices_73, vertices_145, vertices_529, vertices_321, vertices_577, vertices_641, vertices_769, vertices_198, vertices_42, vertices_74, vertices_98, vertices_162, vertices_322, vertices_386, vertices_100, vertices_164, vertices_548, vertices_324, vertices_580, vertices_388, vertices_772, vertices_56, vertices_536, vertices_104, vertices_552, vertices_584, vertices_176, vertices_656, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_59), (false, vertices_331), (false, vertices_179), (false, vertices_899), (false, vertices_837), (false, vertices_601), (false, vertices_657), (true, vertices_198), (true, vertices_98), (true, vertices_100), (true, vertices_164), (true, vertices_548), (true, vertices_388), (true, vertices_104), (true, vertices_552), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 9 12 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_59) then 16 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_179) then 17 else
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_837) then 10 else
  if p.val = (false, vertices_601) then 14 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_198) then 11 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_672) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_198), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_4 1 1 2 4 5 8 620 100 1
cert_row_4 2 1 4 6 7 8 932 164 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 0 0 1 4 5 198 230 2
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 7 198 454 3
cert_coverFacet 2 106
cert_cover_2 2 2 0 4 5 42 106 3
cert_coverFacet 3 620
cert_cover_5 3 1 1 2 4 5 100 620 1
cert_coverFacet 4 932
cert_cover_5 4 2 1 4 6 7 164 932 3
cert_coverFacet 5 696
cert_cover_5 5 3 2 3 4 6 56 696 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0020

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m13e11q2_0022.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0022

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [39, 391, 555, 787, 109, 205, 905, 118, 342, 562, 964, 744, 880, 7, 35, 259, 515, 77, 37, 133, 41, 137, 521, 385, 769, 86, 38, 262, 50, 274, 530, 546, 100, 196, 324, 388, 104, 552, 200, 648, 112, 560, 336, 784, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_39, vertices_391, vertices_555, vertices_787, vertices_109, vertices_205, vertices_905, vertices_118, vertices_342, vertices_562, vertices_964, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_35, vertices_259, vertices_515, vertices_77, vertices_37, vertices_133, vertices_41, vertices_137, vertices_521, vertices_385, vertices_769, vertices_86, vertices_38, vertices_262, vertices_50, vertices_274, vertices_530, vertices_546, vertices_100, vertices_196, vertices_324, vertices_388, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_39), (false, vertices_391), (false, vertices_555), (false, vertices_787), (false, vertices_109), (false, vertices_205), (false, vertices_905), (true, vertices_86), (true, vertices_50), (true, vertices_324), (true, vertices_112), (true, vertices_560), (true, vertices_336), (true, vertices_608), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 9 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_39) then 0 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_555) then 14 else
  if p.val = (false, vertices_787) then 10 else
  if p.val = (false, vertices_109) then 16 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_905) then 19 else
  if p.val = (true, vertices_86) then 11 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_324) then 2 else
  if p.val = (true, vertices_112) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_336) then 5 else
  if p.val = (true, vertices_608) then 6 else
  if p.val = (true, vertices_704) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_39), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 3
  | 10 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 1 5 6 7 8 964 196 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 0 0 1 3 4 86 118 3
cert_coverFacet 1 342
cert_cover_5 1 0 0 1 3 7 86 342 3
cert_coverFacet 2 562
cert_cover_2 2 3 0 4 8 50 562 3
cert_coverFacet 3 964
cert_cover_5 3 1 1 5 6 7 196 964 3
cert_coverFacet 4 744
cert_cover_5 4 2 2 4 5 6 104 744 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0022

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m13e11q2_0024.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0024

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 91, 283, 99, 781, 677, 617, 434, 722, 738, 916, 420, 856, 27, 35, 67, 259, 37, 261, 517, 73, 265, 521, 97, 545, 82, 146, 274, 98, 162, 290, 706, 164, 292, 388, 644, 772, 88, 280, 584, 776, 592, 400, 656, 784, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_91, vertices_283, vertices_99, vertices_781, vertices_677, vertices_617, vertices_434, vertices_722, vertices_738, vertices_916, vertices_420, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_35, vertices_67, vertices_259, vertices_37, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_97, vertices_545, vertices_82, vertices_146, vertices_274, vertices_98, vertices_162, vertices_290, vertices_706, vertices_164, vertices_292, vertices_388, vertices_644, vertices_772, vertices_88, vertices_280, vertices_584, vertices_776, vertices_592, vertices_400, vertices_656, vertices_784, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_91), (false, vertices_283), (false, vertices_99), (false, vertices_781), (false, vertices_677), (false, vertices_617), (true, vertices_146), (true, vertices_162), (true, vertices_706), (true, vertices_388), (true, vertices_592), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 9 17 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 10 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_283) then 15 else
  if p.val = (false, vertices_99) then 0 else
  if p.val = (false, vertices_781) then 11 else
  if p.val = (false, vertices_677) then 12 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_706) then 16 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_592) then 4 else
  if p.val = (true, vertices_400) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_416) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_99), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_706), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 7 434 146 2
cert_row_2 1 0 5 6 8 706
cert_row_4 2 1 3 6 7 8 916 388 1
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 4 0 1 2
cert_heightProof 4
cert_coverFacet 0 434
cert_cover_5 0 0 0 3 4 6 146 434 2
cert_coverFacet 1 722
cert_cover_5 1 1 0 3 5 6 82 722 3
cert_coverFacet 2 738
cert_cover_5 2 1 0 4 5 6 98 738 3
cert_coverFacet 3 916
cert_cover_5 3 2 1 3 6 7 388 916 1
cert_coverFacet 4 420
cert_cover_2 4 4 1 6 7 164 420 3
cert_coverFacet 5 856
cert_cover_5 5 3 2 3 5 7 88 856 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0024

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m13e11q2_0025.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0025

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [91, 299, 563, 805, 217, 905, 657, 358, 458, 114, 244, 692, 964, 11, 19, 35, 89, 137, 265, 145, 529, 289, 545, 641, 769, 74, 266, 50, 82, 98, 290, 322, 180, 100, 292, 548, 196, 324, 644, 772, 200, 392, 112, 560, 208, 656, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_91, vertices_299, vertices_563, vertices_805, vertices_217, vertices_905, vertices_657, vertices_358, vertices_458, vertices_114, vertices_244, vertices_692, vertices_964] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_35, vertices_89, vertices_137, vertices_265, vertices_145, vertices_529, vertices_289, vertices_545, vertices_641, vertices_769, vertices_74, vertices_266, vertices_50, vertices_82, vertices_98, vertices_290, vertices_322, vertices_180, vertices_100, vertices_292, vertices_548, vertices_196, vertices_324, vertices_644, vertices_772, vertices_200, vertices_392, vertices_112, vertices_560, vertices_208, vertices_656, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_91), (false, vertices_299), (false, vertices_563), (false, vertices_805), (false, vertices_217), (false, vertices_905), (false, vertices_657), (true, vertices_98), (true, vertices_322), (true, vertices_180), (true, vertices_100), (true, vertices_196), (true, vertices_324), (true, vertices_644), (true, vertices_112), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_91) then 16 else
  if p.val = (false, vertices_299) then 10 else
  if p.val = (false, vertices_563) then 11 else
  if p.val = (false, vertices_805) then 13 else
  if p.val = (false, vertices_217) then 17 else
  if p.val = (false, vertices_905) then 18 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_180) then 14 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_448) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_180), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 4 6 180
cert_row_4 1 0 1 4 5 7 358 98 1
cert_row_4 2 0 2 5 6 7 458 74 3
cert_row_4 3 1 5 6 7 8 964 196 3
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 1 0 1 4 5 98 358 1
cert_coverFacet 1 458
cert_cover_5 1 2 0 2 5 6 74 458 3
cert_coverFacet 2 114
cert_cover_2 2 3 0 4 5 50 114 3
cert_coverFacet 3 244
cert_cover_5 3 0 1 3 4 5 180 244 3
cert_coverFacet 4 692
cert_cover_5 4 0 1 3 4 8 180 692 3
cert_coverFacet 5 964
cert_cover_5 5 3 1 5 6 7 196 964 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0025

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m13e11q2_0026.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0026

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 173, 557, 789, 453, 433, 838, 618, 242, 466, 786, 716, 232, 45, 133, 261, 517, 49, 273, 529, 161, 545, 385, 50, 210, 274, 530, 98, 546, 322, 578, 770, 140, 524, 196, 324, 580, 772, 104, 168, 552, 200, 584, 176, 400, 784, 224, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_173, vertices_557, vertices_789, vertices_453, vertices_433, vertices_838, vertices_618, vertices_242, vertices_466, vertices_786, vertices_716, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_45, vertices_133, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_161, vertices_545, vertices_385, vertices_50, vertices_210, vertices_274, vertices_530, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_140, vertices_524, vertices_196, vertices_324, vertices_580, vertices_772, vertices_104, vertices_168, vertices_552, vertices_200, vertices_584, vertices_176, vertices_400, vertices_784, vertices_224, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_173), (false, vertices_557), (false, vertices_789), (false, vertices_453), (false, vertices_433), (true, vertices_210), (true, vertices_274), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_580), (true, vertices_104), (true, vertices_200), (true, vertices_584), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 16 13 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 11 else
  if p.val = (false, vertices_173) then 14 else
  if p.val = (false, vertices_557) then 15 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (false, vertices_433) then 20 else
  if p.val = (true, vertices_210) then 12 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_224) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 6 210
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 2 4 5 8 618 98 1
cert_row_4 3 1 2 5 6 8 716 140 2
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 618
cert_cover_5 1 2 0 2 4 5 98 618 1
cert_coverFacet 2 242
cert_cover_5 2 0 0 3 4 5 50 242 3
cert_coverFacet 3 466
cert_cover_5 3 0 0 3 5 7 210 466 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 716
cert_cover_5 5 3 1 2 5 6 140 716 2
cert_coverFacet 6 232
cert_cover_2 6 4 2 5 6 104 232 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0026

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m13e11q2_0028.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0028

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 91, 163, 707, 341, 677, 837, 186, 458, 820, 440, 344, 992, 19, 35, 67, 131, 21, 37, 325, 517, 81, 161, 577, 641, 26, 74, 138, 50, 162, 194, 52, 276, 548, 772, 184, 88, 280, 328, 392, 304, 336, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_91, vertices_163, vertices_707, vertices_341, vertices_677, vertices_837, vertices_186, vertices_458, vertices_820, vertices_440, vertices_344, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_67, vertices_131, vertices_21, vertices_37, vertices_325, vertices_517, vertices_81, vertices_161, vertices_577, vertices_641, vertices_26, vertices_74, vertices_138, vertices_50, vertices_162, vertices_194, vertices_52, vertices_276, vertices_548, vertices_772, vertices_184, vertices_88, vertices_280, vertices_328, vertices_392, vertices_304, vertices_336, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_91), (false, vertices_163), (false, vertices_707), (false, vertices_341), (false, vertices_677), (false, vertices_837), (true, vertices_138), (true, vertices_184), (true, vertices_280), (true, vertices_328), (true, vertices_392), (true, vertices_304), (true, vertices_416), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 13 17 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 10 else
  if p.val = (false, vertices_91) then 11 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_707) then 12 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_677) then 15 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_184) then 18 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_328) then 3 else
  if p.val = (true, vertices_392) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_448) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(true, vertices_184), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 7 458 74 3
cert_row_2 1 2 3 4 6 184
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 2 1 4
cert_heightProof 4
cert_coverFacet 0 186
cert_cover_5 0 1 0 2 3 4 26 186 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 74 458 3
cert_coverFacet 2 820
cert_cover_5 2 2 1 3 4 7 52 820 3
cert_coverFacet 3 440
cert_cover_5 3 1 2 3 4 7 184 440 3
cert_coverFacet 4 344
cert_cover_2 4 3 2 5 7 88 344 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0028

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m13e11q2_0029.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0029

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 91, 531, 205, 789, 453, 369, 234, 682, 114, 818, 908, 992, 11, 19, 515, 13, 197, 261, 517, 73, 81, 273, 529, 321, 170, 74, 522, 50, 82, 530, 98, 546, 140, 524, 388, 772, 200, 648, 112, 304, 784, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_91, vertices_531, vertices_205, vertices_789, vertices_453, vertices_369, vertices_234, vertices_682, vertices_114, vertices_818, vertices_908, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_515, vertices_13, vertices_197, vertices_261, vertices_517, vertices_73, vertices_81, vertices_273, vertices_529, vertices_321, vertices_170, vertices_74, vertices_522, vertices_50, vertices_82, vertices_530, vertices_98, vertices_546, vertices_140, vertices_524, vertices_388, vertices_772, vertices_200, vertices_648, vertices_112, vertices_304, vertices_784, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_91), (false, vertices_531), (false, vertices_205), (false, vertices_789), (false, vertices_453), (false, vertices_369), (true, vertices_170), (true, vertices_50), (true, vertices_98), (true, vertices_546), (true, vertices_648), (true, vertices_224), (true, vertices_672), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 9 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 14 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_789) then 11 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (false, vertices_369) then 12 else
  if p.val = (true, vertices_170) then 15 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_224) then 5 else
  if p.val = (true, vertices_672) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 3
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_170), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 7 8 818 50 3
cert_row_2 1 0 2 4 6 170
cert_row_4 2 1 2 6 7 8 908 140 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 3 0 1 4
cert_heightProof 4
cert_coverFacet 0 234
cert_cover_5 0 1 0 2 4 5 170 234 3
cert_coverFacet 1 682
cert_cover_5 1 1 0 2 4 8 170 682 3
cert_coverFacet 2 114
cert_cover_2 2 3 0 4 5 50 114 3
cert_coverFacet 3 818
cert_cover_5 3 0 0 3 4 7 50 818 3
cert_coverFacet 4 908
cert_cover_5 4 2 1 2 6 7 140 908 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0029

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m13e11q2_0030.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0030

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 779, 595, 99, 181, 789, 241, 618, 426, 908, 724, 420, 744, 35, 67, 259, 515, 21, 37, 261, 177, 81, 529, 97, 769, 42, 266, 522, 98, 290, 578, 148, 532, 164, 292, 388, 644, 772, 616, 168, 392, 648, 776, 208, 592, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_779, vertices_595, vertices_99, vertices_181, vertices_789, vertices_241, vertices_618, vertices_426, vertices_908, vertices_724, vertices_420, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_259, vertices_515, vertices_21, vertices_37, vertices_261, vertices_177, vertices_81, vertices_529, vertices_97, vertices_769, vertices_42, vertices_266, vertices_522, vertices_98, vertices_290, vertices_578, vertices_148, vertices_532, vertices_164, vertices_292, vertices_388, vertices_644, vertices_772, vertices_616, vertices_168, vertices_392, vertices_648, vertices_776, vertices_208, vertices_592, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_779), (false, vertices_595), (false, vertices_99), (false, vertices_181), (false, vertices_789), (false, vertices_241), (true, vertices_42), (true, vertices_388), (true, vertices_644), (true, vertices_616), (true, vertices_168), (true, vertices_392), (true, vertices_648), (true, vertices_416), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 13 15 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 10 else
  if p.val = (false, vertices_779) then 11 else
  if p.val = (false, vertices_595) then 12 else
  if p.val = (false, vertices_99) then 0 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_789) then 14 else
  if p.val = (false, vertices_241) then 19 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_388) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_616) then 16 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_704) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_99), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(true, vertices_616), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 42 3
cert_row_2 1 2 4 5 8 616
cert_row_4 2 1 2 6 7 8 908 388 1
cert_row_4 3 1 3 5 6 8 724 148 2
cert_rows
cert_pivot_2 0 4 2 1
cert_heightProof 4
cert_coverFacet 0 618
cert_cover_5 0 1 0 2 4 5 42 618 3
cert_coverFacet 1 426
cert_cover_5 1 0 0 2 4 6 42 426 3
cert_coverFacet 2 908
cert_cover_5 2 2 1 2 6 7 388 908 1
cert_coverFacet 3 724
cert_cover_5 3 3 1 3 5 6 148 724 2
cert_coverFacet 4 420
cert_cover_2 4 4 1 6 7 164 420 3
cert_coverFacet 5 744
cert_cover_5 5 1 2 4 5 6 616 744 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0030

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m13e11q2_0032.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0032

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 535, 781, 421, 241, 913, 110, 526, 842, 114, 722, 364, 992, 23, 37, 261, 517, 49, 145, 529, 161, 385, 769, 14, 38, 518, 74, 522, 50, 82, 530, 98, 578, 108, 268, 524, 292, 328, 776, 112, 208, 656, 224, 352, 416, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_535, vertices_781, vertices_421, vertices_241, vertices_913, vertices_110, vertices_526, vertices_842, vertices_114, vertices_722, vertices_364, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_37, vertices_261, vertices_517, vertices_49, vertices_145, vertices_529, vertices_161, vertices_385, vertices_769, vertices_14, vertices_38, vertices_518, vertices_74, vertices_522, vertices_50, vertices_82, vertices_530, vertices_98, vertices_578, vertices_108, vertices_268, vertices_524, vertices_292, vertices_328, vertices_776, vertices_112, vertices_208, vertices_656, vertices_224, vertices_352, vertices_416, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_535), (false, vertices_781), (false, vertices_421), (false, vertices_241), (false, vertices_913), (true, vertices_14), (true, vertices_74), (true, vertices_522), (true, vertices_82), (true, vertices_98), (true, vertices_578), (true, vertices_108), (true, vertices_328), (true, vertices_352), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 11 else
  if p.val = (false, vertices_535) then 12 else
  if p.val = (false, vertices_781) then 14 else
  if p.val = (false, vertices_421) then 15 else
  if p.val = (false, vertices_241) then 19 else
  if p.val = (false, vertices_913) then 20 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_108) then 16 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_4 2 0 3 5 6 8 722 82 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 1 2 0 4
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 4 14 110 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 842
cert_cover_5 2 1 0 2 5 7 74 842 3
cert_coverFacet 3 114
cert_cover_2 3 3 0 4 5 50 114 3
cert_coverFacet 4 722
cert_cover_5 4 2 0 3 5 6 82 722 3
cert_coverFacet 5 364
cert_cover_5 5 0 1 2 4 7 108 364 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0032

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m13e11q2_0035.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0035

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 173, 405, 805, 665, 617, 214, 342, 714, 658, 866, 236, 356, 37, 133, 261, 41, 137, 521, 145, 273, 529, 545, 769, 86, 146, 274, 530, 194, 322, 578, 642, 770, 172, 148, 276, 100, 292, 196, 324, 104, 200, 584, 648, 656, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_173, vertices_405, vertices_805, vertices_665, vertices_617, vertices_214, vertices_342, vertices_714, vertices_658, vertices_866, vertices_236, vertices_356] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_41, vertices_137, vertices_521, vertices_145, vertices_273, vertices_529, vertices_545, vertices_769, vertices_86, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_172, vertices_148, vertices_276, vertices_100, vertices_292, vertices_196, vertices_324, vertices_104, vertices_200, vertices_584, vertices_648, vertices_656, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_173), (false, vertices_405), (false, vertices_805), (false, vertices_665), (false, vertices_617), (true, vertices_86), (true, vertices_146), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_100), (true, vertices_196), (true, vertices_324), (true, vertices_200), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 11 else
  if p.val = (false, vertices_173) then 14 else
  if p.val = (false, vertices_405) then 15 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_665) then 18 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (true, vertices_86) then 12 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_352) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_2 1 1 2 4 6 172
cert_row_4 2 0 2 5 6 8 714 194 1
cert_row_4 3 0 4 5 7 8 866 322 1
cert_rows
cert_pivot_2 3 1 2 0
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 6 86 214 3
cert_coverFacet 1 342
cert_cover_5 1 0 0 1 3 7 86 342 3
cert_coverFacet 2 714
cert_cover_5 2 2 0 2 5 6 194 714 1
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 866
cert_cover_5 4 3 0 4 5 7 322 866 1
cert_coverFacet 5 236
cert_cover_5 5 1 1 2 4 5 172 236 3
cert_coverFacet 6 356
cert_cover_2 6 4 1 5 7 100 356 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0035

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m13e11q2_0036.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0036

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 677, 409, 369, 721, 417, 558, 398, 422, 346, 602, 354, 668, 81, 145, 273, 97, 161, 289, 545, 577, 385, 641, 14, 38, 390, 90, 266, 522, 98, 290, 546, 322, 578, 140, 524, 164, 548, 644, 152, 280, 536, 392, 336, 592, 656, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_677, vertices_409, vertices_369, vertices_721, vertices_417, vertices_558, vertices_398, vertices_422, vertices_346, vertices_602, vertices_354, vertices_668] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_273, vertices_97, vertices_161, vertices_289, vertices_545, vertices_577, vertices_385, vertices_641, vertices_14, vertices_38, vertices_390, vertices_90, vertices_266, vertices_522, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_140, vertices_524, vertices_164, vertices_548, vertices_644, vertices_152, vertices_280, vertices_536, vertices_392, vertices_336, vertices_592, vertices_656, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_677), (false, vertices_409), (false, vertices_369), (false, vertices_721), (false, vertices_417), (true, vertices_14), (true, vertices_38), (true, vertices_390), (true, vertices_90), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_322), (true, vertices_140), (true, vertices_524), (true, vertices_536)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 16 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 14 else
  if p.val = (false, vertices_677) then 11 else
  if p.val = (false, vertices_409) then 17 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_390) then 12 else
  if p.val = (true, vertices_90) then 15 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_536) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_2 1 0 1 6 7 390
cert_row_4 2 0 1 2 4 8 558 14 3
cert_row_4 3 1 2 3 6 8 668 140 2
cert_rows
cert_pivot_2 5 7 0 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 2 0 1 2 4 14 558 3
cert_coverFacet 1 398
cert_cover_5 1 1 0 1 2 6 14 398 3
cert_coverFacet 2 422
cert_cover_5 2 1 0 1 4 6 38 422 3
cert_coverFacet 3 346
cert_cover_5 3 0 0 2 3 7 90 346 3
cert_coverFacet 4 602
cert_cover_5 4 0 0 2 3 8 90 602 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 668
cert_cover_5 6 3 1 2 3 6 140 668 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0036

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m13e11q2_0037.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0037

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 613, 313, 217, 841, 113, 118, 214, 678, 666, 794, 306, 716, 25, 73, 265, 49, 81, 97, 289, 545, 577, 769, 86, 38, 134, 538, 50, 146, 274, 290, 546, 642, 770, 100, 548, 196, 580, 644, 152, 280, 200, 584, 648, 776, 112, 304, 208]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_613, vertices_313, vertices_217, vertices_841, vertices_113, vertices_118, vertices_214, vertices_678, vertices_666, vertices_794, vertices_306, vertices_716] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_49, vertices_81, vertices_97, vertices_289, vertices_545, vertices_577, vertices_769, vertices_86, vertices_38, vertices_134, vertices_538, vertices_50, vertices_146, vertices_274, vertices_290, vertices_546, vertices_642, vertices_770, vertices_100, vertices_548, vertices_196, vertices_580, vertices_644, vertices_152, vertices_280, vertices_200, vertices_584, vertices_648, vertices_776, vertices_112, vertices_304, vertices_208] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_613), (false, vertices_313), (false, vertices_217), (false, vertices_841), (false, vertices_113), (true, vertices_86), (true, vertices_38), (true, vertices_134), (true, vertices_538), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_642), (true, vertices_196), (true, vertices_644), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 16 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_613) then 11 else
  if p.val = (false, vertices_313) then 17 else
  if p.val = (false, vertices_217) then 18 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (false, vertices_113) then 0 else
  if p.val = (true, vertices_86) then 12 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_538) then 15 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_648) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_538), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_4 1 1 2 5 6 8 716 196 1
cert_row_2 2 0 1 3 5 86
cert_row_2 3 0 2 3 8 538
cert_rows
cert_pivot_2 4 6 1 0
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 2 0 1 3 4 86 118 3
cert_coverFacet 1 214
cert_cover_5 1 2 0 1 3 6 86 214 3
cert_coverFacet 2 678
cert_cover_5 2 0 0 1 4 6 38 678 3
cert_coverFacet 3 666
cert_cover_5 3 3 0 2 3 6 538 666 3
cert_coverFacet 4 794
cert_cover_5 4 3 0 2 3 7 538 794 3
cert_coverFacet 5 306
cert_cover_2 5 3 0 4 7 50 306 3
cert_coverFacet 6 716
cert_cover_5 6 1 1 2 5 6 196 716 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0037

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m13e11q2_0038.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0038

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 397, 345, 153, 625, 961, 174, 566, 902, 186, 620, 844, 120, 25, 137, 265, 81, 145, 529, 321, 577, 385, 641, 38, 134, 518, 170, 50, 146, 530, 642, 44, 588, 140, 268, 548, 388, 772, 56, 88, 152, 104, 328, 112, 560, 608, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_397, vertices_345, vertices_153, vertices_625, vertices_961, vertices_174, vertices_566, vertices_902, vertices_186, vertices_620, vertices_844, vertices_120] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_81, vertices_145, vertices_529, vertices_321, vertices_577, vertices_385, vertices_641, vertices_38, vertices_134, vertices_518, vertices_170, vertices_50, vertices_146, vertices_530, vertices_642, vertices_44, vertices_588, vertices_140, vertices_268, vertices_548, vertices_388, vertices_772, vertices_56, vertices_88, vertices_152, vertices_104, vertices_328, vertices_112, vertices_560, vertices_608, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_397), (false, vertices_345), (false, vertices_153), (false, vertices_625), (false, vertices_961), (true, vertices_38), (true, vertices_134), (true, vertices_518), (true, vertices_170), (true, vertices_50), (true, vertices_44), (true, vertices_588), (true, vertices_548), (true, vertices_772), (true, vertices_56), (true, vertices_104)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 11 else
  if p.val = (false, vertices_397) then 14 else
  if p.val = (false, vertices_345) then 17 else
  if p.val = (false, vertices_153) then 0 else
  if p.val = (false, vertices_625) then 19 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_170) then 12 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_588) then 15 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_104) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_153), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_170), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_588), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 8 588
cert_row_2 1 0 2 4 6 170
cert_row_4 2 0 1 3 4 8 566 38 2
cert_row_4 3 0 1 6 7 8 902 134 3
cert_rows
cert_pivot_2 5 2 3 0
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 1 0 1 2 4 38 174 2
cert_coverFacet 1 566
cert_cover_5 1 2 0 1 3 4 38 566 2
cert_coverFacet 2 902
cert_cover_5 2 3 0 1 6 7 134 902 3
cert_coverFacet 3 186
cert_cover_5 3 1 0 2 3 4 170 186 2
cert_coverFacet 4 620
cert_cover_5 4 0 1 2 4 5 44 620 3
cert_coverFacet 5 844
cert_cover_5 5 0 1 2 5 7 588 844 3
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0038

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m13e11q2_0039.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0039

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 611, 899, 677, 409, 113, 177, 602, 794, 220, 620, 908, 244, 67, 259, 515, 49, 81, 145, 273, 97, 161, 545, 385, 641, 538, 82, 274, 578, 770, 76, 140, 524, 212, 100, 164, 548, 644, 88, 152, 280, 584, 392, 776, 112, 176, 608, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_611, vertices_899, vertices_677, vertices_409, vertices_113, vertices_177, vertices_602, vertices_794, vertices_220, vertices_620, vertices_908, vertices_244] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_49, vertices_81, vertices_145, vertices_273, vertices_97, vertices_161, vertices_545, vertices_385, vertices_641, vertices_538, vertices_82, vertices_274, vertices_578, vertices_770, vertices_76, vertices_140, vertices_524, vertices_212, vertices_100, vertices_164, vertices_548, vertices_644, vertices_88, vertices_152, vertices_280, vertices_584, vertices_392, vertices_776, vertices_112, vertices_176, vertices_608, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_611), (false, vertices_899), (false, vertices_677), (false, vertices_409), (false, vertices_113), (false, vertices_177), (true, vertices_538), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_212), (true, vertices_100), (true, vertices_88), (true, vertices_584), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 9 12 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 16 else
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_677) then 10 else
  if p.val = (false, vertices_409) then 13 else
  if p.val = (false, vertices_113) then 0 else
  if p.val = (false, vertices_177) then 1 else
  if p.val = (true, vertices_538) then 14 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_212) then 11 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_776) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_538), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 8 538
cert_row_2 1 1 3 5 6 212
cert_row_4 2 1 2 4 5 8 620 76 2
cert_row_4 3 1 2 6 7 8 908 140 3
cert_rows
cert_pivot_2 0 3 4 1
cert_heightProof 4
cert_coverFacet 0 602
cert_cover_5 0 0 0 2 3 5 538 602 3
cert_coverFacet 1 794
cert_cover_5 1 0 0 2 3 7 538 794 3
cert_coverFacet 2 220
cert_cover_5 2 1 1 2 3 5 76 220 2
cert_coverFacet 3 620
cert_cover_5 3 2 1 2 4 5 76 620 2
cert_coverFacet 4 908
cert_cover_5 4 3 1 2 6 7 140 908 3
cert_coverFacet 5 244
cert_cover_5 5 1 1 3 4 5 212 244 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0039

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m13e11q2_0040.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0040

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 283, 301, 653, 789, 721, 174, 298, 210, 850, 482, 740, 868, 27, 13, 261, 517, 137, 265, 145, 273, 529, 641, 42, 138, 266, 82, 146, 274, 162, 290, 194, 322, 44, 140, 612, 164, 292, 644, 772, 296, 208, 592, 784, 224, 352, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_283, vertices_301, vertices_653, vertices_789, vertices_721, vertices_174, vertices_298, vertices_210, vertices_850, vertices_482, vertices_740, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_13, vertices_261, vertices_517, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_641, vertices_42, vertices_138, vertices_266, vertices_82, vertices_146, vertices_274, vertices_162, vertices_290, vertices_194, vertices_322, vertices_44, vertices_140, vertices_612, vertices_164, vertices_292, vertices_644, vertices_772, vertices_296, vertices_208, vertices_592, vertices_784, vertices_224, vertices_352, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_283), (false, vertices_301), (false, vertices_653), (false, vertices_789), (false, vertices_721), (true, vertices_42), (true, vertices_82), (true, vertices_162), (true, vertices_290), (true, vertices_194), (true, vertices_322), (true, vertices_612), (true, vertices_164), (true, vertices_224), (true, vertices_352), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 16 13 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 11 else
  if p.val = (false, vertices_283) then 12 else
  if p.val = (false, vertices_301) then 14 else
  if p.val = (false, vertices_653) then 15 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_612) then 18 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 6 174 42 1
cert_row_2 1 1 4 5 8 612
cert_row_4 2 0 3 5 7 8 850 82 3
cert_row_4 3 0 4 5 6 7 482 162 2
cert_rows
cert_pivot_2 2 1 3 0
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 0 0 1 2 4 42 174 1
cert_coverFacet 1 298
cert_cover_2 1 2 0 4 7 42 298 3
cert_coverFacet 2 210
cert_cover_2 2 3 0 5 6 82 210 3
cert_coverFacet 3 850
cert_cover_5 3 2 0 3 5 7 82 850 3
cert_coverFacet 4 482
cert_cover_5 4 3 0 4 5 6 162 482 2
cert_coverFacet 5 740
cert_cover_5 5 1 1 4 5 6 612 740 3
cert_coverFacet 6 868
cert_cover_5 6 1 1 4 5 7 612 868 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0040

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m13e11q2_0041.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0041

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 901, 233, 625, 465, 673, 206, 782, 454, 122, 570, 338, 684, 81, 273, 529, 97, 161, 545, 193, 385, 641, 769, 14, 198, 262, 58, 74, 522, 82, 274, 530, 322, 770, 140, 524, 388, 644, 772, 104, 168, 552, 200, 112, 560, 336, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_901, vertices_233, vertices_625, vertices_465, vertices_673, vertices_206, vertices_782, vertices_454, vertices_122, vertices_570, vertices_338, vertices_684] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_198, vertices_262, vertices_58, vertices_74, vertices_522, vertices_82, vertices_274, vertices_530, vertices_322, vertices_770, vertices_140, vertices_524, vertices_388, vertices_644, vertices_772, vertices_104, vertices_168, vertices_552, vertices_200, vertices_112, vertices_560, vertices_336, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_901), (false, vertices_233), (false, vertices_625), (false, vertices_465), (false, vertices_673), (true, vertices_14), (true, vertices_198), (true, vertices_262), (true, vertices_58), (true, vertices_74), (true, vertices_522), (true, vertices_82), (true, vertices_322), (true, vertices_140), (true, vertices_524), (true, vertices_552)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 16 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_901) then 11 else
  if p.val = (false, vertices_233) then 17 else
  if p.val = (false, vertices_625) then 19 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (false, vertices_673) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_198) then 12 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_58) then 15 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_552) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_198), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_2 1 0 2 3 4 58
cert_row_4 2 0 1 2 7 8 782 14 3
cert_row_4 3 1 2 4 6 8 684 140 2
cert_rows
cert_pivot_2 5 3 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 782
cert_cover_5 1 2 0 1 2 7 14 782 3
cert_coverFacet 2 454
cert_cover_5 2 0 0 1 5 7 198 454 3
cert_coverFacet 3 122
cert_cover_5 3 1 0 2 3 5 58 122 3
cert_coverFacet 4 570
cert_cover_5 4 1 0 2 3 8 58 570 3
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 684
cert_cover_5 6 3 1 2 4 6 140 684 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0041

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m13e11q2_0042.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0042

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 595, 803, 301, 233, 737, 790, 338, 412, 684, 724, 804, 472, 67, 259, 515, 41, 73, 265, 225, 289, 545, 577, 82, 274, 530, 322, 770, 44, 140, 268, 148, 276, 532, 292, 548, 644, 772, 408, 168, 200, 328, 208, 336, 592, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_595, vertices_803, vertices_301, vertices_233, vertices_737, vertices_790, vertices_338, vertices_412, vertices_684, vertices_724, vertices_804, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_41, vertices_73, vertices_265, vertices_225, vertices_289, vertices_545, vertices_577, vertices_82, vertices_274, vertices_530, vertices_322, vertices_770, vertices_44, vertices_140, vertices_268, vertices_148, vertices_276, vertices_532, vertices_292, vertices_548, vertices_644, vertices_772, vertices_408, vertices_168, vertices_200, vertices_328, vertices_208, vertices_336, vertices_592, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_595), (false, vertices_803), (false, vertices_301), (false, vertices_233), (false, vertices_737), (true, vertices_274), (true, vertices_140), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_408), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 14 16 18 19 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 11 else
  if p.val = (false, vertices_595) then 12 else
  if p.val = (false, vertices_803) then 13 else
  if p.val = (false, vertices_301) then 15 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (false, vertices_737) then 21 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_408) then 17 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_336) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_2 1 2 3 6 7 408
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 1 3 5 6 8 724 148 2
cert_rows
cert_pivot_2 0 7 2 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 338
cert_cover_2 1 3 0 5 7 82 338 3
cert_coverFacet 2 412
cert_cover_5 2 1 1 2 3 6 140 412 2
cert_coverFacet 3 684
cert_cover_5 3 2 1 2 4 6 44 684 3
cert_coverFacet 4 724
cert_cover_5 4 3 1 3 5 6 148 724 2
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coverFacet 6 472
cert_cover_5 6 1 2 3 5 6 408 472 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0042

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m13e11q2_0043.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0043

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [87, 535, 653, 453, 369, 913, 558, 206, 234, 114, 818, 680, 992, 23, 69, 133, 517, 81, 273, 529, 321, 385, 641, 14, 70, 518, 42, 202, 50, 82, 530, 98, 546, 140, 524, 196, 168, 552, 648, 112, 304, 784, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_87, vertices_535, vertices_653, vertices_453, vertices_369, vertices_913, vertices_558, vertices_206, vertices_234, vertices_114, vertices_818, vertices_680, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_69, vertices_133, vertices_517, vertices_81, vertices_273, vertices_529, vertices_321, vertices_385, vertices_641, vertices_14, vertices_70, vertices_518, vertices_42, vertices_202, vertices_50, vertices_82, vertices_530, vertices_98, vertices_546, vertices_140, vertices_524, vertices_196, vertices_168, vertices_552, vertices_648, vertices_112, vertices_304, vertices_784, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_87), (false, vertices_535), (false, vertices_653), (false, vertices_453), (false, vertices_369), (false, vertices_913), (true, vertices_14), (true, vertices_42), (true, vertices_202), (true, vertices_50), (true, vertices_98), (true, vertices_546), (true, vertices_168), (true, vertices_552), (true, vertices_224), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 14 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_87) then 11 else
  if p.val = (false, vertices_535) then 12 else
  if p.val = (false, vertices_653) then 15 else
  if p.val = (false, vertices_453) then 16 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (false, vertices_913) then 20 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_202) then 13 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_87), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 14 3
cert_row_2 1 0 2 5 6 202
cert_row_4 2 0 3 4 7 8 818 50 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 1 2 0 4
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 14 558 3
cert_coverFacet 1 206
cert_cover_5 1 1 0 1 2 5 14 206 3
cert_coverFacet 2 234
cert_cover_5 2 1 0 2 4 5 42 234 3
cert_coverFacet 3 114
cert_cover_2 3 3 0 4 5 50 114 3
cert_coverFacet 4 818
cert_cover_5 4 2 0 3 4 7 50 818 3
cert_coverFacet 5 680
cert_cover_2 5 4 2 6 8 168 680 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0043

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m13e11q2_0044.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0044

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 333, 421, 677, 313, 617, 662, 454, 602, 466, 568, 344, 944, 165, 69, 261, 517, 41, 73, 265, 289, 545, 577, 70, 134, 518, 82, 146, 530, 450, 578, 324, 388, 644, 56, 88, 280, 536, 552, 328, 584, 304, 560, 336, 400, 656, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_333, vertices_421, vertices_677, vertices_313, vertices_617, vertices_662, vertices_454, vertices_602, vertices_466, vertices_568, vertices_344, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_165, vertices_69, vertices_261, vertices_517, vertices_41, vertices_73, vertices_265, vertices_289, vertices_545, vertices_577, vertices_70, vertices_134, vertices_518, vertices_82, vertices_146, vertices_530, vertices_450, vertices_578, vertices_324, vertices_388, vertices_644, vertices_56, vertices_88, vertices_280, vertices_536, vertices_552, vertices_328, vertices_584, vertices_304, vertices_560, vertices_336, vertices_400, vertices_656, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_333), (false, vertices_421), (false, vertices_677), (false, vertices_313), (false, vertices_617), (true, vertices_134), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_450), (true, vertices_88), (true, vertices_536), (true, vertices_560), (true, vertices_336), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 11 else
  if p.val = (false, vertices_333) then 14 else
  if p.val = (false, vertices_421) then 15 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_313) then 18 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_450) then 12 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_656) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_450), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 134 2
cert_row_4 1 0 2 3 5 8 602 82 1
cert_row_2 2 0 5 6 7 450
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 134 662 2
cert_coverFacet 1 454
cert_cover_5 1 2 0 1 5 6 70 454 3
cert_coverFacet 2 602
cert_cover_5 2 1 0 2 3 5 82 602 1
cert_coverFacet 3 466
cert_cover_5 3 2 0 3 5 6 82 466 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 344
cert_cover_2 5 3 2 5 7 88 344 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 304 944 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0044

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m13e11q2_0045.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0045

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 899, 397, 217, 793, 625, 782, 614, 166, 390, 242, 188, 572, 643, 25, 137, 265, 81, 529, 193, 577, 385, 769, 38, 134, 262, 518, 98, 162, 194, 578, 386, 770, 60, 140, 268, 524, 164, 548, 388, 152, 536, 776, 112, 176, 560, 208, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_899, vertices_397, vertices_217, vertices_793, vertices_625, vertices_782, vertices_614, vertices_166, vertices_390, vertices_242, vertices_188, vertices_572] (by decide +kernel)
  polygons := literalFinset [vertices_643, vertices_25, vertices_137, vertices_265, vertices_81, vertices_529, vertices_193, vertices_577, vertices_385, vertices_769, vertices_38, vertices_134, vertices_262, vertices_518, vertices_98, vertices_162, vertices_194, vertices_578, vertices_386, vertices_770, vertices_60, vertices_140, vertices_268, vertices_524, vertices_164, vertices_548, vertices_388, vertices_152, vertices_536, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_899), (false, vertices_397), (false, vertices_217), (false, vertices_793), (false, vertices_625), (true, vertices_38), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_98), (true, vertices_162), (true, vertices_60), (true, vertices_524), (true, vertices_164), (true, vertices_548), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 11 else
  if p.val = (false, vertices_899) then 12 else
  if p.val = (false, vertices_397) then 14 else
  if p.val = (false, vertices_217) then 17 else
  if p.val = (false, vertices_793) then 18 else
  if p.val = (false, vertices_625) then 20 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_60) then 15 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_176) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 262 2
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 1 4 5 8 614 38 3
cert_row_4 3 0 3 4 5 6 242 98 1
cert_rows
cert_pivot_2 7 2 1 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 262 782 2
cert_coverFacet 1 614
cert_cover_5 1 2 0 1 4 5 38 614 3
cert_coverFacet 2 166
cert_cover_2 2 1 0 4 6 38 166 3
cert_coverFacet 3 390
cert_cover_2 3 1 0 6 7 134 390 3
cert_coverFacet 4 242
cert_cover_5 4 3 0 3 4 5 98 242 1
cert_coverFacet 5 188
cert_cover_5 5 1 1 2 3 6 60 188 3
cert_coverFacet 6 572
cert_cover_5 6 1 1 2 3 8 60 572 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0045

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m13e11q2_0046.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0046

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 157, 313, 681, 721, 849, 174, 302, 214, 838, 674, 706, 348, 25, 41, 137, 593, 145, 273, 289, 545, 641, 769, 46, 70, 134, 262, 162, 290, 546, 194, 578, 642, 770, 28, 140, 268, 84, 148, 324, 280, 168, 296, 208, 336, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_157, vertices_313, vertices_681, vertices_721, vertices_849, vertices_174, vertices_302, vertices_214, vertices_838, vertices_674, vertices_706, vertices_348] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_137, vertices_593, vertices_145, vertices_273, vertices_289, vertices_545, vertices_641, vertices_769, vertices_46, vertices_70, vertices_134, vertices_262, vertices_162, vertices_290, vertices_546, vertices_194, vertices_578, vertices_642, vertices_770, vertices_28, vertices_140, vertices_268, vertices_84, vertices_148, vertices_324, vertices_280, vertices_168, vertices_296, vertices_208, vertices_336, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_157), (false, vertices_313), (false, vertices_681), (false, vertices_721), (false, vertices_849), (true, vertices_46), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_162), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_268), (true, vertices_84), (true, vertices_324)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 11 else
  if p.val = (false, vertices_157) then 14 else
  if p.val = (false, vertices_313) then 16 else
  if p.val = (false, vertices_681) then 17 else
  if p.val = (false, vertices_721) then 19 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (true, vertices_46) then 12 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_324) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 1 3 5 6 214 70 2
cert_row_4 2 0 1 5 7 8 838 70 3
cert_row_4 3 1 2 3 5 7 348 28 3
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 0 0 1 2 6 46 174 3
cert_coverFacet 1 302
cert_cover_5 1 0 0 1 2 7 46 302 3
cert_coverFacet 2 214
cert_cover_5 2 1 0 1 3 5 70 214 2
cert_coverFacet 3 838
cert_cover_5 3 2 0 1 5 7 70 838 3
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 348
cert_cover_5 6 3 1 2 3 5 28 348 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0046

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m13e11q2_0047.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0047

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 555, 397, 309, 677, 713, 566, 602, 458, 306, 338, 852, 964, 43, 37, 133, 261, 137, 265, 521, 289, 545, 641, 74, 266, 522, 50, 82, 274, 530, 290, 546, 322, 52, 276, 532, 548, 836, 388, 644, 200, 584, 392, 304, 336, 592, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_555, vertices_397, vertices_309, vertices_677, vertices_713, vertices_566, vertices_602, vertices_458, vertices_306, vertices_338, vertices_852, vertices_964] (by decide +kernel)
  polygons := literalFinset [vertices_43, vertices_37, vertices_133, vertices_261, vertices_137, vertices_265, vertices_521, vertices_289, vertices_545, vertices_641, vertices_74, vertices_266, vertices_522, vertices_50, vertices_82, vertices_274, vertices_530, vertices_290, vertices_546, vertices_322, vertices_52, vertices_276, vertices_532, vertices_548, vertices_836, vertices_388, vertices_644, vertices_200, vertices_584, vertices_392, vertices_304, vertices_336, vertices_592, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_555), (false, vertices_397), (false, vertices_309), (false, vertices_677), (false, vertices_713), (true, vertices_74), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_322), (true, vertices_532), (true, vertices_836), (true, vertices_336), (true, vertices_592), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 16 13 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 11 else
  if p.val = (false, vertices_555) then 12 else
  if p.val = (false, vertices_397) then 14 else
  if p.val = (false, vertices_309) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_713) then 15 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_836) then 19 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_836), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 50 1
cert_row_2 1 1 5 7 8 836
cert_row_4 2 0 2 3 5 8 602 74 2
cert_row_4 3 0 2 5 6 7 458 74 3
cert_rows
cert_pivot_2 4 1 3 0
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 50 566 1
cert_coverFacet 1 602
cert_cover_5 1 2 0 2 3 5 74 602 2
cert_coverFacet 2 458
cert_cover_5 2 3 0 2 5 6 74 458 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 852
cert_cover_5 5 1 1 3 5 7 276 852 2
cert_coverFacet 6 964
cert_cover_5 6 1 1 5 6 7 836 964 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0047

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m13e12q3_0000.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e12q3_0000

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 301, 181, 453, 817, 961, 110, 230, 314, 794, 714, 178, 844, 37, 133, 261, 49, 145, 529, 289, 449, 641, 769, 102, 282, 42, 74, 522, 50, 146, 530, 162, 194, 642, 44, 76, 268, 164, 196, 324, 296, 584, 776, 176, 304, 784, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_301, vertices_181, vertices_453, vertices_817, vertices_961, vertices_110, vertices_230, vertices_314, vertices_794, vertices_714, vertices_178, vertices_844] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_49, vertices_145, vertices_529, vertices_289, vertices_449, vertices_641, vertices_769, vertices_102, vertices_282, vertices_42, vertices_74, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_194, vertices_642, vertices_44, vertices_76, vertices_268, vertices_164, vertices_196, vertices_324, vertices_296, vertices_584, vertices_776, vertices_176, vertices_304, vertices_784, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_301), (false, vertices_181), (false, vertices_453), (false, vertices_817), (false, vertices_961), (true, vertices_102), (true, vertices_282), (true, vertices_42), (true, vertices_74), (true, vertices_522), (true, vertices_50), (true, vertices_162), (true, vertices_194), (true, vertices_76), (true, vertices_584), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 9 17 19 20 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 13 else
  if p.val = (false, vertices_301) then 10 else
  if p.val = (false, vertices_181) then 16 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_102) then 14 else
  if p.val = (true, vertices_282) then 11 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_776) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inl 2
  | 10 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_282), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 7 282
cert_row_2 1 0 1 4 5 102
cert_row_4 2 0 2 5 6 8 714 74 3
cert_row_4 3 1 2 5 7 8 844 76 3
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 102 110 2
cert_coverFacet 1 230
cert_cover_5 1 1 0 1 4 6 102 230 3
cert_coverFacet 2 314
cert_cover_5 2 0 0 2 3 4 282 314 3
cert_coverFacet 3 794
cert_cover_5 3 0 0 2 3 8 282 794 3
cert_coverFacet 4 714
cert_cover_5 4 2 0 2 5 6 74 714 3
cert_coverFacet 5 178
cert_cover_2 5 3 0 4 6 50 178 3
cert_coverFacet 6 844
cert_cover_5 6 3 1 2 5 7 76 844 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e12q3_0000

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m14e10q0_0004.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0004

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 541, 333, 709, 409, 481, 570, 242, 866, 706, 812, 836, 312, 432, 13, 69, 517, 25, 265, 145, 529, 193, 321, 385, 641, 50, 146, 530, 98, 546, 194, 578, 642, 268, 524, 324, 580, 772, 56, 280, 536, 296, 552, 176, 304, 400, 224, 352, 416, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_541, vertices_333, vertices_709, vertices_409, vertices_481, vertices_570, vertices_242, vertices_866, vertices_706, vertices_812, vertices_836, vertices_312, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_25, vertices_265, vertices_145, vertices_529, vertices_193, vertices_321, vertices_385, vertices_641, vertices_50, vertices_146, vertices_530, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_268, vertices_524, vertices_324, vertices_580, vertices_772, vertices_56, vertices_280, vertices_536, vertices_296, vertices_552, vertices_176, vertices_304, vertices_400, vertices_224, vertices_352, vertices_416, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_541), (false, vertices_333), (false, vertices_709), (false, vertices_409), (false, vertices_481), (true, vertices_50), (true, vertices_98), (true, vertices_546), (true, vertices_194), (true, vertices_578), (true, vertices_772), (true, vertices_56), (true, vertices_296), (true, vertices_552), (true, vertices_176), (true, vertices_304), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_541) then 16 else
  if p.val = (false, vertices_333) then 17 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
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
cert_row_4 0 0 3 4 5 6 242 50 3
cert_row_4 1 0 2 3 4 8 570 50 1
cert_row_4 2 0 4 5 7 8 866 98 3
cert_row_4 3 1 2 4 7 8 812 268 2
cert_rows
cert_pivot_2 6 3 0 1
cert_heightProof 4
cert_coverFacet 0 570
cert_cover_5 0 1 0 2 3 4 50 570 1
cert_coverFacet 1 242
cert_cover_5 1 0 0 3 4 5 50 242 3
cert_coverFacet 2 866
cert_cover_5 2 2 0 4 5 7 98 866 3
cert_coverFacet 3 706
cert_cover_2 3 5 0 6 8 194 706 3
cert_coverFacet 4 812
cert_cover_5 4 3 1 2 4 7 268 812 2
cert_coverFacet 5 836
cert_cover_2 5 5 1 7 8 324 836 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0004

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m14e10q0_0005.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0005

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 803, 707, 613, 217, 369, 782, 394, 650, 124, 284, 716, 820, 408, 131, 259, 515, 81, 145, 273, 97, 289, 545, 193, 577, 138, 266, 522, 386, 642, 770, 28, 76, 268, 524, 52, 276, 100, 548, 580, 772, 88, 152, 280, 200, 392, 648, 112, 304, 400, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_803, vertices_707, vertices_613, vertices_217, vertices_369, vertices_782, vertices_394, vertices_650, vertices_124, vertices_284, vertices_716, vertices_820, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_81, vertices_145, vertices_273, vertices_97, vertices_289, vertices_545, vertices_193, vertices_577, vertices_138, vertices_266, vertices_522, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_268, vertices_524, vertices_52, vertices_276, vertices_100, vertices_548, vertices_580, vertices_772, vertices_88, vertices_152, vertices_280, vertices_200, vertices_392, vertices_648, vertices_112, vertices_304, vertices_400, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_803), (false, vertices_707), (false, vertices_613), (false, vertices_217), (false, vertices_369), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_276), (true, vertices_772), (true, vertices_280), (true, vertices_392), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 14 else
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_217) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_648) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
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
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 1 2 5 6 8 716 76 3
cert_row_4 2 1 2 3 4 5 124 28 3
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 0 6 2 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 4 28 124 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 716
cert_cover_5 5 1 1 2 5 6 76 716 3
cert_coverFacet 6 820
cert_cover_5 6 3 1 3 4 7 52 820 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0005

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m14e10q0_0006.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0006

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 541, 405, 709, 345, 481, 566, 314, 538, 330, 738, 354, 308, 932, 21, 133, 517, 25, 73, 521, 273, 193, 321, 577, 385, 26, 74, 266, 522, 50, 530, 98, 290, 546, 322, 578, 52, 276, 532, 292, 548, 388, 644, 280, 536, 328, 304, 224, 352, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_541, vertices_405, vertices_709, vertices_345, vertices_481, vertices_566, vertices_314, vertices_538, vertices_330, vertices_738, vertices_354, vertices_308, vertices_932] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_25, vertices_73, vertices_521, vertices_273, vertices_193, vertices_321, vertices_577, vertices_385, vertices_26, vertices_74, vertices_266, vertices_522, vertices_50, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_52, vertices_276, vertices_532, vertices_292, vertices_548, vertices_388, vertices_644, vertices_280, vertices_536, vertices_328, vertices_304, vertices_224, vertices_352, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_541), (false, vertices_405), (false, vertices_709), (false, vertices_345), (false, vertices_481), (true, vertices_26), (true, vertices_266), (true, vertices_50), (true, vertices_530), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_52), (true, vertices_292), (true, vertices_548), (true, vertices_304), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_541) then 16 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
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
cert_row_4 0 0 2 3 4 7 314 26 3
cert_row_4 1 0 1 3 4 8 566 50 1
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 1 4 6 7 8 932 292 2
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 1 0 1 3 4 50 566 1
cert_coverFacet 1 314
cert_cover_5 1 0 0 2 3 4 26 314 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 330
cert_cover_2 3 2 0 5 7 74 330 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 98 738 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 932
cert_cover_5 7 3 1 4 6 7 292 932 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0006

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m14e10q0_0008.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0008

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 541, 405, 709, 345, 481, 310, 570, 282, 330, 738, 354, 564, 932, 21, 133, 517, 25, 73, 521, 273, 193, 321, 577, 385, 26, 74, 266, 522, 50, 274, 98, 290, 546, 322, 578, 52, 276, 532, 292, 548, 388, 644, 280, 536, 328, 560, 224, 352, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_541, vertices_405, vertices_709, vertices_345, vertices_481, vertices_310, vertices_570, vertices_282, vertices_330, vertices_738, vertices_354, vertices_564, vertices_932] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_25, vertices_73, vertices_521, vertices_273, vertices_193, vertices_321, vertices_577, vertices_385, vertices_26, vertices_74, vertices_266, vertices_522, vertices_50, vertices_274, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_52, vertices_276, vertices_532, vertices_292, vertices_548, vertices_388, vertices_644, vertices_280, vertices_536, vertices_328, vertices_560, vertices_224, vertices_352, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_541), (false, vertices_405), (false, vertices_709), (false, vertices_345), (false, vertices_481), (true, vertices_26), (true, vertices_266), (true, vertices_50), (true, vertices_274), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_52), (true, vertices_292), (true, vertices_548), (true, vertices_560), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_541) then 16 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
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
cert_row_4 0 0 2 3 4 8 570 26 3
cert_row_4 1 0 1 3 4 7 310 50 1
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 1 4 6 7 8 932 292 2
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 1 0 1 3 4 50 310 1
cert_coverFacet 1 570
cert_cover_5 1 0 0 2 3 4 26 570 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 330
cert_cover_2 3 2 0 5 7 74 330 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 98 738 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 932
cert_cover_5 7 3 1 4 6 7 292 932 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0008

end
end BundlePart29
-- Explicit facial frame witnesses.

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0180 : Certifies 180 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0016.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0181 : Certifies 181 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0017.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0182 : Certifies 182 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0018.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0183 : Certifies 183 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0020.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0184 : Certifies 184 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0022.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0185 : Certifies 185 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0024.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0186 : Certifies 186 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0025.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0187 : Certifies 187 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0026.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0188 : Certifies 188 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0028.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0189 : Certifies 189 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0029.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0190 : Certifies 190 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0030.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0191 : Certifies 191 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0032.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0192 : Certifies 192 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0035.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0193 : Certifies 193 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0036.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0194 : Certifies 194 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0037.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0195 : Certifies 195 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0038.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0196 : Certifies 196 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0039.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0197 : Certifies 197 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0040.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0198 : Certifies 198 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0041.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0199 : Certifies 199 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0042.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0200 : Certifies 200 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0043.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0201 : Certifies 201 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0044.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0202 : Certifies 202 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0045.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0203 : Certifies 203 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0046.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0204 : Certifies 204 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0047.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0205 : Certifies 205 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e12q3_0000.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0206 : Certifies 206 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0004.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0207 : Certifies 207 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0005.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0208 : Certifies 208 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0006.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0209 : Certifies 209 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0008.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B006 (j : Fin 30) :
    Certifies (180 + j.val) := by
  fin_cases j
  · exact projection_0180
  · exact projection_0181
  · exact projection_0182
  · exact projection_0183
  · exact projection_0184
  · exact projection_0185
  · exact projection_0186
  · exact projection_0187
  · exact projection_0188
  · exact projection_0189
  · exact projection_0190
  · exact projection_0191
  · exact projection_0192
  · exact projection_0193
  · exact projection_0194
  · exact projection_0195
  · exact projection_0196
  · exact projection_0197
  · exact projection_0198
  · exact projection_0199
  · exact projection_0200
  · exact projection_0201
  · exact projection_0202
  · exact projection_0203
  · exact projection_0204
  · exact projection_0205
  · exact projection_0206
  · exact projection_0207
  · exact projection_0208
  · exact projection_0209

end Nonrational.TerminalVerification
