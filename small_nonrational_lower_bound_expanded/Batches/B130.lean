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
/- Source: ProjectionCertificates/R_m16e10q1_0042.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0042

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 331, 707, 661, 229, 357, 282, 538, 586, 818, 188, 564, 804, 312, 728, 488, 67, 259, 515, 101, 133, 261, 517, 193, 321, 641, 26, 74, 266, 522, 274, 530, 578, 770, 52, 148, 532, 164, 292, 548, 772, 56, 152, 280, 536, 168, 296, 200, 328, 584, 304, 560, 656, 224, 352, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_331, vertices_707, vertices_661, vertices_229, vertices_357, vertices_282, vertices_538, vertices_586, vertices_818, vertices_188, vertices_564, vertices_804, vertices_312, vertices_728, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_101, vertices_133, vertices_261, vertices_517, vertices_193, vertices_321, vertices_641, vertices_26, vertices_74, vertices_266, vertices_522, vertices_274, vertices_530, vertices_578, vertices_770, vertices_52, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_772, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_200, vertices_328, vertices_584, vertices_304, vertices_560, vertices_656, vertices_224, vertices_352, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_331), (false, vertices_707), (false, vertices_661), (false, vertices_229), (false, vertices_357), (true, vertices_26), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_52), (true, vertices_548), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_296), (true, vertices_200), (true, vertices_584), (true, vertices_304), (true, vertices_560), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 25 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 18 else
  if p.val = (false, vertices_331) then 19 else
  if p.val = (false, vertices_707) then 20 else
  if p.val = (false, vertices_661) then 22 else
  if p.val = (false, vertices_229) then 23 else
  if p.val = (false, vertices_357) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_560) then 15 else
  if p.val = (true, vertices_800) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
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
cert_row_4 0 0 3 4 7 8 818 274 2
cert_row_4 1 1 2 3 4 6 188 52 1
cert_row_4 2 2 3 5 6 8 728 152 2
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 282
cert_cover_2 0 2 0 3 7 26 282 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 586
cert_cover_2 2 2 0 5 8 74 586 3
cert_coverFacet 3 818
cert_cover_5 3 0 0 3 4 7 274 818 2
cert_coverFacet 4 188
cert_cover_5 4 1 1 2 3 4 52 188 1
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 728
cert_cover_5 8 2 2 3 5 6 152 728 2
cert_coverFacet 9 488
cert_cover_5 9 3 2 4 5 6 168 488 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0042

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0043.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0043

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 653, 837, 409, 617, 329, 166, 806, 122, 178, 466, 866, 692, 568, 344, 664, 133, 261, 517, 73, 137, 265, 521, 321, 577, 385, 38, 134, 262, 50, 82, 146, 98, 162, 802, 322, 386, 164, 548, 644, 772, 56, 88, 152, 280, 536, 104, 552, 328, 648, 176, 560, 336, 400, 656, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_653, vertices_837, vertices_409, vertices_617, vertices_329, vertices_166, vertices_806, vertices_122, vertices_178, vertices_466, vertices_866, vertices_692, vertices_568, vertices_344, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_521, vertices_321, vertices_577, vertices_385, vertices_38, vertices_134, vertices_262, vertices_50, vertices_82, vertices_146, vertices_98, vertices_162, vertices_802, vertices_322, vertices_386, vertices_164, vertices_548, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_552, vertices_328, vertices_648, vertices_176, vertices_560, vertices_336, vertices_400, vertices_656, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_653), (false, vertices_837), (false, vertices_409), (false, vertices_617), (false, vertices_329), (true, vertices_38), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_98), (true, vertices_162), (true, vertices_802), (true, vertices_322), (true, vertices_164), (true, vertices_548), (true, vertices_56), (true, vertices_88), (true, vertices_536), (true, vertices_176), (true, vertices_560), (true, vertices_336), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 18 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (false, vertices_409) then 24 else
  if p.val = (false, vertices_617) then 25 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_802) then 19 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_336) then 15 else
  if p.val = (true, vertices_656) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_802), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 5 122 50 1
cert_row_4 1 0 3 5 6 7 466 82 3
cert_row_2 2 0 4 7 8 802
cert_row_4 3 1 3 4 6 8 692 164 1
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 166
cert_cover_2 0 1 0 4 6 38 166 3
cert_coverFacet 1 806
cert_cover_5 1 2 0 1 4 7 38 806 3
cert_coverFacet 2 122
cert_cover_5 2 0 0 2 3 4 50 122 1
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 466
cert_cover_5 4 1 0 3 5 6 82 466 3
cert_coverFacet 5 866
cert_cover_5 5 2 0 4 5 7 98 866 3
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 164 692 1
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coverFacet 9 664
cert_cover_2 9 3 2 6 8 152 664 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0043

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0044.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0044

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 613, 537, 361, 713, 817, 158, 790, 230, 806, 394, 418, 724, 664, 456, 480, 25, 73, 265, 521, 273, 529, 97, 289, 545, 577, 22, 38, 134, 774, 26, 138, 266, 274, 162, 290, 386, 148, 532, 100, 548, 196, 580, 152, 536, 200, 328, 392, 648, 656, 784, 224, 352, 416, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_613, vertices_537, vertices_361, vertices_713, vertices_817, vertices_158, vertices_790, vertices_230, vertices_806, vertices_394, vertices_418, vertices_724, vertices_664, vertices_456, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_521, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_577, vertices_22, vertices_38, vertices_134, vertices_774, vertices_26, vertices_138, vertices_266, vertices_274, vertices_162, vertices_290, vertices_386, vertices_148, vertices_532, vertices_100, vertices_548, vertices_196, vertices_580, vertices_152, vertices_536, vertices_200, vertices_328, vertices_392, vertices_648, vertices_656, vertices_784, vertices_224, vertices_352, vertices_416, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_613), (false, vertices_537), (false, vertices_361), (false, vertices_713), (false, vertices_817), (true, vertices_22), (true, vertices_38), (true, vertices_134), (true, vertices_774), (true, vertices_138), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_148), (true, vertices_532), (true, vertices_196), (true, vertices_152), (true, vertices_392), (true, vertices_656), (true, vertices_224), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 18 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (false, vertices_713) then 24 else
  if p.val = (false, vertices_817) then 26 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_774) then 19 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_416) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
cert_nodeAtPriority_33 537 22 38 134 138 162 290 386 148 532 196 152 392 656 224 416 448 283 774 613 361 713 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 0 1 2 3 6 158 22 2
cert_row_4 2 0 1 4 5 6 230 38 3
cert_row_4 3 1 3 5 6 8 724 148 2
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 22 158 2
cert_coverFacet 1 790
cert_cover_5 1 0 0 1 3 7 22 790 3
cert_coverFacet 2 230
cert_cover_5 2 2 0 1 4 5 38 230 3
cert_coverFacet 3 806
cert_cover_5 3 0 0 1 4 7 38 806 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 148 724 2
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coverFacet 9 480
cert_cover_2 9 5 4 6 7 224 480 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0044

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0045.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0045

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 195, 835, 397, 809, 465, 118, 690, 210, 610, 572, 668, 364, 340, 404, 864, 67, 131, 515, 137, 265, 521, 193, 321, 385, 769, 50, 82, 146, 98, 546, 194, 578, 642, 540, 44, 140, 268, 52, 84, 148, 276, 100, 324, 388, 296, 552, 648, 560, 208, 336, 400, 656, 352, 608, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_195, vertices_835, vertices_397, vertices_809, vertices_465, vertices_118, vertices_690, vertices_210, vertices_610, vertices_572, vertices_668, vertices_364, vertices_340, vertices_404, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_515, vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_385, vertices_769, vertices_50, vertices_82, vertices_146, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_540, vertices_44, vertices_140, vertices_268, vertices_52, vertices_84, vertices_148, vertices_276, vertices_100, vertices_324, vertices_388, vertices_296, vertices_552, vertices_648, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_352, vertices_608, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_195), (false, vertices_835), (false, vertices_397), (false, vertices_809), (false, vertices_465), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_98), (true, vertices_546), (true, vertices_540), (true, vertices_44), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_100), (true, vertices_324), (true, vertices_560), (true, vertices_656), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_397) then 21 else
  if p.val = (false, vertices_809) then 24 else
  if p.val = (false, vertices_465) then 26 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_540) then 22 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_324) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_352) then 15 else
  if p.val = (true, vertices_608) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_540), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 8 690 50 3
cert_row_2 1 1 2 3 8 540
cert_row_4 2 0 1 3 4 5 118 50 1
cert_row_4 3 1 2 4 5 7 364 44 3
cert_rows
cert_pivot_2 6 8 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 2 0 1 3 4 50 118 1
cert_coverFacet 1 690
cert_cover_5 1 0 0 3 4 6 50 690 3
cert_coverFacet 2 210
cert_cover_2 2 3 0 5 6 82 210 3
cert_coverFacet 3 610
cert_cover_2 3 4 0 5 8 98 610 3
cert_coverFacet 4 572
cert_cover_5 4 1 1 2 3 4 540 572 3
cert_coverFacet 5 668
cert_cover_5 5 1 1 2 3 6 540 668 3
cert_coverFacet 6 364
cert_cover_5 6 3 1 2 4 5 44 364 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coverFacet 8 404
cert_cover_2 8 3 1 6 7 148 404 3
cert_coverFacet 9 864
cert_cover_2 9 5 4 7 8 352 864 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0045

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0046.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0046

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 579, 771, 181, 805, 709, 481, 542, 90, 810, 722, 60, 556, 660, 440, 472, 67, 259, 515, 37, 133, 517, 161, 289, 193, 321, 577, 769, 26, 74, 266, 522, 82, 530, 578, 770, 28, 44, 524, 52, 148, 532, 548, 644, 56, 88, 408, 296, 552, 328, 176, 208, 656, 416, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_579, vertices_771, vertices_181, vertices_805, vertices_709, vertices_481, vertices_542, vertices_90, vertices_810, vertices_722, vertices_60, vertices_556, vertices_660, vertices_440, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_37, vertices_133, vertices_517, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_769, vertices_26, vertices_74, vertices_266, vertices_522, vertices_82, vertices_530, vertices_578, vertices_770, vertices_28, vertices_44, vertices_524, vertices_52, vertices_148, vertices_532, vertices_548, vertices_644, vertices_56, vertices_88, vertices_408, vertices_296, vertices_552, vertices_328, vertices_176, vertices_208, vertices_656, vertices_416, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_579), (false, vertices_771), (false, vertices_181), (false, vertices_805), (false, vertices_709), (false, vertices_481), (true, vertices_26), (true, vertices_522), (true, vertices_82), (true, vertices_530), (true, vertices_28), (true, vertices_44), (true, vertices_524), (true, vertices_532), (true, vertices_56), (true, vertices_88), (true, vertices_408), (true, vertices_296), (true, vertices_552), (true, vertices_208), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 17 else
  if p.val = (false, vertices_579) then 0 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_408) then 23 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_656) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_579), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 26 1
cert_row_4 1 0 2 4 7 8 810 266 2
cert_row_2 2 2 3 6 7 408
cert_row_4 3 0 3 5 6 8 722 82 3
cert_rows
cert_pivot_2 1 4 2 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 26 542 1
cert_coverFacet 1 90
cert_cover_2 1 2 0 3 5 26 90 3
cert_coverFacet 2 810
cert_cover_5 2 1 0 2 4 7 266 810 2
cert_coverFacet 3 722
cert_cover_5 3 3 0 3 5 6 82 722 3
cert_coverFacet 4 60
cert_cover_2 4 2 1 3 4 28 60 3
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 440
cert_cover_5 7 2 2 3 4 6 56 440 3
cert_coverFacet 8 472
cert_cover_5 8 2 2 3 5 6 88 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0046

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0048.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0048

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 837, 793, 369, 737, 286, 206, 406, 538, 682, 178, 588, 780, 484, 712, 432, 49, 273, 529, 97, 545, 321, 577, 769, 14, 278, 134, 26, 138, 522, 50, 146, 530, 162, 546, 76, 268, 524, 196, 324, 580, 388, 772, 280, 536, 200, 584, 648, 776, 176, 304, 400, 224, 352, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_837, vertices_793, vertices_369, vertices_737, vertices_286, vertices_206, vertices_406, vertices_538, vertices_682, vertices_178, vertices_588, vertices_780, vertices_484, vertices_712, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_273, vertices_529, vertices_97, vertices_545, vertices_321, vertices_577, vertices_769, vertices_14, vertices_278, vertices_134, vertices_26, vertices_138, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_546, vertices_76, vertices_268, vertices_524, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_280, vertices_536, vertices_200, vertices_584, vertices_648, vertices_776, vertices_176, vertices_304, vertices_400, vertices_224, vertices_352, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_837), (false, vertices_793), (false, vertices_369), (false, vertices_737), (true, vertices_14), (true, vertices_278), (true, vertices_134), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_162), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_196), (true, vertices_388), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_176), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 21 23 25 27 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 19 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (false, vertices_793) then 24 else
  if p.val = (false, vertices_369) then 26 else
  if p.val = (false, vertices_737) then 28 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_278) then 20 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_176) then 15 else
  if p.val = (true, vertices_400) then 16 else
  if p.val = (true, vertices_416) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_278), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 7 278
cert_row_4 1 0 2 4 6 8 682 138 2
cert_row_4 2 0 1 2 5 6 206 14 3
cert_row_4 3 1 4 5 6 7 484 196 1
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 14 286 3
cert_coverFacet 1 206
cert_cover_5 1 2 0 1 2 5 14 206 3
cert_coverFacet 2 406
cert_cover_5 2 0 0 1 3 6 278 406 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 682
cert_cover_5 4 1 0 2 4 6 138 682 2
cert_coverFacet 5 178
cert_cover_2 5 3 0 4 6 50 178 3
cert_coverFacet 6 588
cert_cover_2 6 2 1 5 8 76 588 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 484
cert_cover_5 8 3 1 4 5 6 196 484 1
cert_coverFacet 9 712
cert_cover_2 9 5 2 6 8 200 712 3
cert_coverFacet 10 432
cert_cover_2 10 4 3 6 7 176 432 3
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0048

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0049.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0049

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 179, 291, 707, 333, 581, 481, 666, 562, 802, 284, 540, 716, 820, 248, 376, 35, 131, 259, 515, 69, 261, 517, 161, 289, 193, 321, 577, 50, 146, 530, 290, 546, 642, 770, 28, 76, 268, 524, 276, 532, 580, 772, 120, 152, 280, 536, 200, 328, 648, 176, 304, 560, 224, 352, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_179, vertices_291, vertices_707, vertices_333, vertices_581, vertices_481, vertices_666, vertices_562, vertices_802, vertices_284, vertices_540, vertices_716, vertices_820, vertices_248, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_69, vertices_261, vertices_517, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_50, vertices_146, vertices_530, vertices_290, vertices_546, vertices_642, vertices_770, vertices_28, vertices_76, vertices_268, vertices_524, vertices_276, vertices_532, vertices_580, vertices_772, vertices_120, vertices_152, vertices_280, vertices_536, vertices_200, vertices_328, vertices_648, vertices_176, vertices_304, vertices_560, vertices_224, vertices_352, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_179), (false, vertices_291), (false, vertices_707), (false, vertices_333), (false, vertices_581), (false, vertices_481), (true, vertices_530), (true, vertices_546), (true, vertices_28), (true, vertices_524), (true, vertices_276), (true, vertices_532), (true, vertices_120), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_200), (true, vertices_648), (true, vertices_304), (true, vertices_560), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_179) then 18 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_707) then 19 else
  if p.val = (false, vertices_333) then 21 else
  if p.val = (false, vertices_581) then 1 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_120) then 23 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(true, vertices_120), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 146 1
cert_row_4 1 1 2 5 6 8 716 76 3
cert_row_2 2 2 3 4 5 120
cert_row_4 3 1 3 4 7 8 820 276 2
cert_rows
cert_pivot_2 0 6 2 1
cert_heightProof 4
cert_coverFacet 0 666
cert_cover_5 0 0 0 2 3 6 146 666 1
cert_coverFacet 1 562
cert_cover_2 1 3 0 4 8 50 562 3
cert_coverFacet 2 802
cert_cover_2 2 4 0 7 8 290 802 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 716
cert_cover_5 5 1 1 2 5 6 76 716 3
cert_coverFacet 6 820
cert_cover_5 6 3 1 3 4 7 276 820 2
cert_coverFacet 7 248
cert_cover_5 7 2 2 3 4 6 120 248 3
cert_coverFacet 8 376
cert_cover_5 8 2 2 3 4 7 120 376 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0049

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0050.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0050

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 523, 899, 613, 601, 481, 673, 158, 526, 678, 410, 540, 116, 436, 596, 376, 11, 259, 515, 73, 521, 97, 161, 545, 321, 577, 385, 641, 14, 134, 518, 154, 266, 522, 386, 642, 28, 524, 52, 84, 148, 532, 100, 164, 548, 580, 88, 280, 536, 328, 112, 304, 592, 400, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_523, vertices_899, vertices_613, vertices_601, vertices_481, vertices_673, vertices_158, vertices_526, vertices_678, vertices_410, vertices_540, vertices_116, vertices_436, vertices_596, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_259, vertices_515, vertices_73, vertices_521, vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_641, vertices_14, vertices_134, vertices_518, vertices_154, vertices_266, vertices_522, vertices_386, vertices_642, vertices_28, vertices_524, vertices_52, vertices_84, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_580, vertices_88, vertices_280, vertices_536, vertices_328, vertices_112, vertices_304, vertices_592, vertices_400, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_523), (false, vertices_899), (false, vertices_613), (false, vertices_601), (false, vertices_481), (false, vertices_673), (true, vertices_14), (true, vertices_134), (true, vertices_518), (true, vertices_154), (true, vertices_28), (true, vertices_524), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_164), (true, vertices_280), (true, vertices_112), (true, vertices_304), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 17 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (false, vertices_673) then 1 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_154) then 19 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_164) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 134 2
cert_row_2 1 0 2 3 6 154
cert_row_4 2 1 3 4 6 7 436 52 3
cert_row_4 3 2 3 4 5 7 376 88 2
cert_rows
cert_pivot_2 8 0 1 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 14 158 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 678
cert_cover_5 2 0 0 1 4 6 134 678 2
cert_coverFacet 3 410
cert_cover_5 3 1 0 2 3 7 154 410 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 116
cert_cover_2 5 3 1 4 5 52 116 3
cert_coverFacet 6 436
cert_cover_5 6 2 1 3 4 6 52 436 3
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 376
cert_cover_5 8 3 2 3 4 5 88 376 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0050

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0051.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0051

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 43, 331, 675, 121, 481, 897, 286, 542, 554, 244, 340, 660, 964, 696, 344, 11, 35, 259, 515, 41, 73, 97, 161, 321, 385, 641, 769, 30, 262, 518, 42, 266, 522, 546, 84, 148, 276, 532, 196, 324, 644, 772, 56, 88, 280, 536, 552, 328, 112, 176, 336, 656, 224, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_43, vertices_331, vertices_675, vertices_121, vertices_481, vertices_897, vertices_286, vertices_542, vertices_554, vertices_244, vertices_340, vertices_660, vertices_964, vertices_696, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_515, vertices_41, vertices_73, vertices_97, vertices_161, vertices_321, vertices_385, vertices_641, vertices_769, vertices_30, vertices_262, vertices_518, vertices_42, vertices_266, vertices_522, vertices_546, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_536, vertices_552, vertices_328, vertices_112, vertices_176, vertices_336, vertices_656, vertices_224, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_43), (false, vertices_331), (false, vertices_675), (false, vertices_121), (false, vertices_481), (false, vertices_897), (true, vertices_30), (true, vertices_522), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_196), (true, vertices_324), (true, vertices_644), (true, vertices_280), (true, vertices_536), (true, vertices_552), (true, vertices_176), (true, vertices_336), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 16 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_43) then 0 else
  if p.val = (false, vertices_331) then 20 else
  if p.val = (false, vertices_675) then 21 else
  if p.val = (false, vertices_121) then 23 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_30) then 18 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_656) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 0 43 1 897 522 84 148 276 532 196 324 644 280 536 552 176 336 656 775 30 331 675 121 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 1 5 6 7 8 964 196 3
cert_row_4 2 1 3 4 5 6 244 84 2
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 7 30 286 3
cert_coverFacet 1 542
cert_cover_5 1 0 0 1 2 8 30 542 3
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 244
cert_cover_5 3 2 1 3 4 5 84 244 2
cert_coverFacet 4 340
cert_cover_2 4 3 1 5 7 84 340 3
cert_coverFacet 5 660
cert_cover_2 5 3 1 6 8 148 660 3
cert_coverFacet 6 964
cert_cover_5 6 1 1 5 6 7 196 964 3
cert_coverFacet 7 696
cert_cover_5 7 3 2 3 4 6 56 696 3
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0051

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0052.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0052

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 307, 531, 707, 117, 593, 481, 654, 778, 786, 364, 556, 460, 564, 724, 824, 19, 131, 259, 515, 49, 81, 529, 97, 289, 193, 577, 385, 138, 266, 522, 274, 530, 642, 770, 44, 332, 140, 524, 52, 84, 532, 100, 548, 196, 644, 296, 552, 392, 776, 304, 560, 592, 784, 352, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_307, vertices_531, vertices_707, vertices_117, vertices_593, vertices_481, vertices_654, vertices_778, vertices_786, vertices_364, vertices_556, vertices_460, vertices_564, vertices_724, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_49, vertices_81, vertices_529, vertices_97, vertices_289, vertices_193, vertices_577, vertices_385, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_642, vertices_770, vertices_44, vertices_332, vertices_140, vertices_524, vertices_52, vertices_84, vertices_532, vertices_100, vertices_548, vertices_196, vertices_644, vertices_296, vertices_552, vertices_392, vertices_776, vertices_304, vertices_560, vertices_592, vertices_784, vertices_352, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_307), (false, vertices_531), (false, vertices_707), (false, vertices_117), (false, vertices_593), (false, vertices_481), (true, vertices_522), (true, vertices_770), (true, vertices_44), (true, vertices_332), (true, vertices_140), (true, vertices_524), (true, vertices_532), (true, vertices_548), (true, vertices_196), (true, vertices_644), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_560), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 17 else
  if p.val = (false, vertices_307) then 18 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_707) then 19 else
  if p.val = (false, vertices_117) then 21 else
  if p.val = (false, vertices_593) then 1 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_332) then 22 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_4 1 1 3 5 6 8 724 84 3
cert_row_2 2 1 2 5 7 332
cert_row_4 3 2 3 4 7 8 824 296 1
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 364
cert_cover_5 3 2 1 2 4 5 44 364 3
cert_coverFacet 4 556
cert_cover_2 4 2 1 4 8 44 556 3
cert_coverFacet 5 460
cert_cover_5 5 2 1 2 5 6 332 460 3
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 724
cert_cover_5 7 1 1 3 5 6 84 724 3
cert_coverFacet 8 824
cert_cover_5 8 3 2 3 4 7 296 824 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0052

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0053.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0053

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 557, 397, 181, 617, 481, 662, 602, 778, 370, 402, 898, 652, 628, 904, 432, 13, 37, 133, 553, 73, 265, 97, 161, 321, 385, 74, 266, 522, 82, 146, 274, 530, 322, 386, 642, 770, 140, 524, 52, 148, 532, 548, 644, 584, 392, 648, 776, 112, 176, 304, 592, 400, 352, 608, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_557, vertices_397, vertices_181, vertices_617, vertices_481, vertices_662, vertices_602, vertices_778, vertices_370, vertices_402, vertices_898, vertices_652, vertices_628, vertices_904, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_133, vertices_553, vertices_73, vertices_265, vertices_97, vertices_161, vertices_321, vertices_385, vertices_74, vertices_266, vertices_522, vertices_82, vertices_146, vertices_274, vertices_530, vertices_322, vertices_386, vertices_642, vertices_770, vertices_140, vertices_524, vertices_52, vertices_148, vertices_532, vertices_548, vertices_644, vertices_584, vertices_392, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_592, vertices_400, vertices_352, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_557), (false, vertices_397), (false, vertices_181), (false, vertices_617), (false, vertices_481), (true, vertices_522), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_532), (true, vertices_644), (true, vertices_648), (true, vertices_776), (true, vertices_112), (true, vertices_304), (true, vertices_592), (true, vertices_400), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 18 else
  if p.val = (false, vertices_557) then 23 else
  if p.val = (false, vertices_397) then 20 else
  if p.val = (false, vertices_181) then 21 else
  if p.val = (false, vertices_617) then 24 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_896) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_4 1 0 2 3 5 8 602 74 2
cert_row_4 2 0 3 4 5 7 370 82 2
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 602
cert_cover_5 1 1 0 2 3 5 74 602 2
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 370
cert_cover_5 3 2 0 3 4 5 82 370 2
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 628
cert_cover_5 7 3 1 3 4 5 52 628 3
cert_coverFacet 8 904
cert_cover_2 8 6 2 7 8 392 904 3
cert_coverFacet 9 432
cert_cover_2 9 4 3 6 7 176 432 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0053

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0054.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0054

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 597, 217, 841, 433, 785, 110, 270, 566, 774, 234, 930, 588, 780, 244, 816, 73, 137, 265, 81, 145, 273, 529, 577, 385, 769, 14, 38, 262, 518, 106, 138, 266, 162, 546, 386, 770, 76, 268, 524, 52, 84, 532, 100, 580, 772, 200, 584, 776, 176, 304, 560, 208, 784, 224, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_597, vertices_217, vertices_841, vertices_433, vertices_785, vertices_110, vertices_270, vertices_566, vertices_774, vertices_234, vertices_930, vertices_588, vertices_780, vertices_244, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_81, vertices_145, vertices_273, vertices_529, vertices_577, vertices_385, vertices_769, vertices_14, vertices_38, vertices_262, vertices_518, vertices_106, vertices_138, vertices_266, vertices_162, vertices_546, vertices_386, vertices_770, vertices_76, vertices_268, vertices_524, vertices_52, vertices_84, vertices_532, vertices_100, vertices_580, vertices_772, vertices_200, vertices_584, vertices_776, vertices_176, vertices_304, vertices_560, vertices_208, vertices_784, vertices_224, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_597), (false, vertices_217), (false, vertices_841), (false, vertices_433), (false, vertices_785), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_106), (true, vertices_162), (true, vertices_546), (true, vertices_770), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_100), (true, vertices_772), (true, vertices_560), (true, vertices_224), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_597) then 21 else
  if p.val = (false, vertices_217) then 23 else
  if p.val = (false, vertices_841) then 24 else
  if p.val = (false, vertices_433) then 26 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_106) then 19 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_52) then 11 else
  if p.val = (true, vertices_100) then 12 else
  if p.val = (true, vertices_772) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_800) then 16 else
  0
cert_priority
cert_nodeAtPriority_33 785 14 38 262 518 162 546 770 76 268 524 52 100 772 560 224 800 395 106 597 217 841 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 4 6 7 8 930 162 3
cert_row_4 2 0 1 3 4 8 566 38 2
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 566
cert_cover_5 2 2 0 1 3 4 38 566 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 234
cert_cover_5 4 0 0 2 4 6 106 234 3
cert_coverFacet 5 930
cert_cover_5 5 1 0 4 6 7 162 930 3
cert_coverFacet 6 588
cert_cover_2 6 2 1 5 8 76 588 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 244
cert_cover_5 8 3 1 3 4 5 52 244 3
cert_coverFacet 9 816
cert_cover_2 9 4 3 7 8 304 816 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0054

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0055.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0055

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 421, 217, 681, 465, 865, 30, 526, 406, 358, 550, 346, 610, 540, 692, 664, 73, 137, 521, 209, 161, 289, 545, 321, 577, 385, 14, 22, 38, 262, 518, 26, 74, 522, 274, 98, 546, 322, 578, 28, 524, 148, 532, 164, 292, 548, 388, 88, 152, 536, 648, 336, 400, 656, 352, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_421, vertices_217, vertices_681, vertices_465, vertices_865, vertices_30, vertices_526, vertices_406, vertices_358, vertices_550, vertices_346, vertices_610, vertices_540, vertices_692, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_521, vertices_209, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_14, vertices_22, vertices_38, vertices_262, vertices_518, vertices_26, vertices_74, vertices_522, vertices_274, vertices_98, vertices_546, vertices_322, vertices_578, vertices_28, vertices_524, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_88, vertices_152, vertices_536, vertices_648, vertices_336, vertices_400, vertices_656, vertices_352, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_421), (false, vertices_217), (false, vertices_681), (false, vertices_465), (false, vertices_865), (true, vertices_14), (true, vertices_22), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_274), (true, vertices_98), (true, vertices_546), (true, vertices_322), (true, vertices_28), (true, vertices_524), (true, vertices_148), (true, vertices_532), (true, vertices_548), (true, vertices_536), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 21 23 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 18 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_217) then 24 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (false, vertices_865) then 27 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_322) then 9 else
  if p.val = (true, vertices_28) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_148) then 12 else
  if p.val = (true, vertices_532) then 13 else
  if p.val = (true, vertices_548) then 14 else
  if p.val = (true, vertices_536) then 15 else
  if p.val = (true, vertices_656) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 7 346 26 3
cert_row_4 1 0 1 4 5 7 358 38 3
cert_row_4 2 0 1 3 6 7 406 22 3
cert_row_4 3 1 3 4 6 8 692 148 2
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 406
cert_cover_5 2 2 0 1 3 6 22 406 3
cert_coverFacet 3 358
cert_cover_5 3 1 0 1 4 5 38 358 3
cert_coverFacet 4 550
cert_cover_2 4 1 0 4 8 38 550 3
cert_coverFacet 5 346
cert_cover_5 5 0 0 2 3 5 26 346 3
cert_coverFacet 6 610
cert_cover_2 6 4 0 5 8 98 610 3
cert_coverFacet 7 540
cert_cover_2 7 2 1 3 8 28 540 3
cert_coverFacet 8 692
cert_cover_5 8 3 1 3 4 6 148 692 2
cert_coverFacet 9 664
cert_cover_2 9 3 2 6 8 152 664 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0055

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0056.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0056

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 213, 409, 625, 785, 481, 110, 270, 598, 774, 426, 610, 668, 236, 780, 792, 81, 145, 273, 529, 97, 289, 545, 193, 385, 769, 14, 70, 262, 518, 42, 266, 98, 290, 546, 578, 770, 108, 140, 268, 524, 84, 148, 532, 196, 772, 152, 280, 536, 168, 392, 776, 592, 784, 224, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_213, vertices_409, vertices_625, vertices_785, vertices_481, vertices_110, vertices_270, vertices_598, vertices_774, vertices_426, vertices_610, vertices_668, vertices_236, vertices_780, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_385, vertices_769, vertices_14, vertices_70, vertices_262, vertices_518, vertices_42, vertices_266, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_108, vertices_140, vertices_268, vertices_524, vertices_84, vertices_148, vertices_532, vertices_196, vertices_772, vertices_152, vertices_280, vertices_536, vertices_168, vertices_392, vertices_776, vertices_592, vertices_784, vertices_224, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_213), (false, vertices_409), (false, vertices_625), (false, vertices_785), (false, vertices_481), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_42), (true, vertices_266), (true, vertices_98), (true, vertices_578), (true, vertices_108), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_532), (true, vertices_772), (true, vertices_536), (true, vertices_168), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_409) then 23 else
  if p.val = (false, vertices_625) then 25 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_108) then 21 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_772) then 13 else
  if p.val = (true, vertices_536) then 14 else
  if p.val = (true, vertices_168) then 15 else
  if p.val = (true, vertices_776) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 42 3
cert_row_2 1 1 2 4 5 108
cert_row_4 2 0 1 3 5 8 598 70 2
cert_row_4 3 1 2 3 6 8 668 140 2
cert_rows
cert_pivot_2 7 4 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 598
cert_cover_5 2 2 0 1 3 5 70 598 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 426
cert_cover_5 4 0 0 2 4 6 42 426 3
cert_coverFacet 5 610
cert_cover_2 5 4 0 5 8 98 610 3
cert_coverFacet 6 668
cert_cover_5 6 3 1 2 3 6 140 668 2
cert_coverFacet 7 236
cert_cover_5 7 1 1 2 4 6 108 236 3
cert_coverFacet 8 780
cert_cover_2 8 2 1 7 8 268 780 3
cert_coverFacet 9 792
cert_cover_2 9 3 2 7 8 280 792 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0056

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0057.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0057

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 787, 451, 333, 525, 773, 233, 566, 434, 674, 60, 92, 684, 852, 120, 496, 131, 259, 515, 13, 261, 517, 73, 137, 521, 193, 321, 769, 50, 274, 530, 162, 546, 386, 642, 28, 44, 76, 524, 52, 84, 532, 548, 324, 772, 56, 88, 104, 168, 648, 112, 432, 336, 784, 224, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_787, vertices_451, vertices_333, vertices_525, vertices_773, vertices_233, vertices_566, vertices_434, vertices_674, vertices_60, vertices_92, vertices_684, vertices_852, vertices_120, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_13, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_193, vertices_321, vertices_769, vertices_50, vertices_274, vertices_530, vertices_162, vertices_546, vertices_386, vertices_642, vertices_28, vertices_44, vertices_76, vertices_524, vertices_52, vertices_84, vertices_532, vertices_548, vertices_324, vertices_772, vertices_56, vertices_88, vertices_104, vertices_168, vertices_648, vertices_112, vertices_432, vertices_336, vertices_784, vertices_224, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_787), (false, vertices_451), (false, vertices_333), (false, vertices_525), (false, vertices_773), (false, vertices_233), (true, vertices_50), (true, vertices_162), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_52), (true, vertices_84), (true, vertices_532), (true, vertices_548), (true, vertices_56), (true, vertices_88), (true, vertices_112), (true, vertices_432), (true, vertices_336), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 17 else
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_333) then 21 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_773) then 1 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_432) then 25 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 50 1
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_2 2 3 4 6 7 432
cert_row_4 3 1 3 5 7 8 852 84 3
cert_rows
cert_pivot_2 0 2 4 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 50 566 1
cert_coverFacet 1 434
cert_cover_5 1 2 0 3 4 6 50 434 3
cert_coverFacet 2 674
cert_cover_2 2 4 0 6 8 162 674 3
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 92
cert_cover_2 4 2 1 3 5 28 92 3
cert_coverFacet 5 684
cert_cover_5 5 1 1 2 4 6 44 684 3
cert_coverFacet 6 852
cert_cover_5 6 3 1 3 5 7 84 852 3
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coverFacet 8 496
cert_cover_5 8 2 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0057

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0058.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0058

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 333, 789, 709, 361, 625, 654, 794, 394, 242, 658, 418, 236, 780, 424, 720, 69, 261, 517, 329, 49, 273, 529, 97, 289, 577, 138, 266, 522, 50, 146, 274, 530, 162, 290, 386, 642, 76, 140, 268, 524, 196, 644, 772, 104, 168, 296, 392, 776, 112, 208, 592, 656, 784, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_333, vertices_789, vertices_709, vertices_361, vertices_625, vertices_654, vertices_794, vertices_394, vertices_242, vertices_658, vertices_418, vertices_236, vertices_780, vertices_424, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_329, vertices_49, vertices_273, vertices_529, vertices_97, vertices_289, vertices_577, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_386, vertices_642, vertices_76, vertices_140, vertices_268, vertices_524, vertices_196, vertices_644, vertices_772, vertices_104, vertices_168, vertices_296, vertices_392, vertices_776, vertices_112, vertices_208, vertices_592, vertices_656, vertices_784, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_333), (false, vertices_789), (false, vertices_709), (false, vertices_361), (false, vertices_625), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_140), (true, vertices_524), (true, vertices_168), (true, vertices_392), (true, vertices_776), (true, vertices_208), (true, vertices_656), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 18 else
  if p.val = (false, vertices_333) then 23 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_361) then 24 else
  if p.val = (false, vertices_625) then 26 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_4 0 0 2 3 7 8 794 266 2
cert_row_4 1 0 1 2 6 8 654 138 1
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 1 2 4 5 6 236 76 2
cert_rows
cert_pivot_2 7 8 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 138 654 1
cert_coverFacet 1 794
cert_cover_5 1 0 0 2 3 7 266 794 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 50 242 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 236
cert_cover_5 6 3 1 2 4 5 76 236 2
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coverFacet 9 720
cert_cover_2 9 5 3 6 8 208 720 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0058

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0059.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0059

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 677, 313, 553, 713, 481, 590, 566, 214, 778, 466, 786, 436, 708, 568, 792, 41, 73, 265, 521, 161, 289, 545, 193, 321, 641, 22, 70, 518, 74, 266, 522, 210, 274, 530, 322, 770, 52, 148, 164, 548, 196, 580, 644, 56, 280, 536, 552, 584, 776, 304, 560, 400, 784, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_677, vertices_313, vertices_553, vertices_713, vertices_481, vertices_590, vertices_566, vertices_214, vertices_778, vertices_466, vertices_786, vertices_436, vertices_708, vertices_568, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_22, vertices_70, vertices_518, vertices_74, vertices_266, vertices_522, vertices_210, vertices_274, vertices_530, vertices_322, vertices_770, vertices_52, vertices_148, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_280, vertices_536, vertices_552, vertices_584, vertices_776, vertices_304, vertices_560, vertices_400, vertices_784, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_677), (false, vertices_313), (false, vertices_553), (false, vertices_713), (false, vertices_481), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_522), (true, vertices_210), (true, vertices_274), (true, vertices_530), (true, vertices_770), (true, vertices_52), (true, vertices_148), (true, vertices_196), (true, vertices_580), (true, vertices_536), (true, vertices_776), (true, vertices_560), (true, vertices_400), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 18 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_313) then 23 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_713) then 24 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_210) then 19 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_784) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
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
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 466
cert_cover_5 4 1 0 3 5 7 210 466 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 52 436 3
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coverFacet 8 568
cert_cover_2 8 3 2 4 8 56 568 3
cert_coverFacet 9 792
cert_cover_2 9 3 2 7 8 280 792 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0059

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0060.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0060

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 613, 537, 361, 713, 817, 158, 790, 166, 806, 394, 482, 724, 228, 664, 456, 25, 73, 265, 521, 273, 529, 97, 289, 545, 577, 22, 38, 134, 774, 26, 138, 266, 274, 162, 290, 386, 148, 532, 100, 164, 548, 196, 580, 152, 536, 200, 328, 392, 648, 656, 784, 224, 352, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_613, vertices_537, vertices_361, vertices_713, vertices_817, vertices_158, vertices_790, vertices_166, vertices_806, vertices_394, vertices_482, vertices_724, vertices_228, vertices_664, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_521, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_577, vertices_22, vertices_38, vertices_134, vertices_774, vertices_26, vertices_138, vertices_266, vertices_274, vertices_162, vertices_290, vertices_386, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_152, vertices_536, vertices_200, vertices_328, vertices_392, vertices_648, vertices_656, vertices_784, vertices_224, vertices_352, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_613), (false, vertices_537), (false, vertices_361), (false, vertices_713), (false, vertices_817), (true, vertices_22), (true, vertices_38), (true, vertices_134), (true, vertices_774), (true, vertices_138), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_148), (true, vertices_532), (true, vertices_164), (true, vertices_196), (true, vertices_152), (true, vertices_392), (true, vertices_656), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 18 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (false, vertices_713) then 24 else
  if p.val = (false, vertices_817) then 26 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_774) then 19 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
cert_nodeAtPriority_33 537 22 38 134 138 162 290 386 148 532 164 196 152 392 656 224 448 283 774 613 361 713 817
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 6 158 22 2
cert_row_4 1 0 4 5 6 7 482 162 2
cert_row_2 2 0 1 7 8 774
cert_row_4 3 1 3 5 6 8 724 148 2
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 22 158 2
cert_coverFacet 1 790
cert_cover_5 1 2 0 1 3 7 22 790 3
cert_coverFacet 2 166
cert_cover_2 2 1 0 4 6 38 166 3
cert_coverFacet 3 806
cert_cover_5 3 2 0 1 4 7 38 806 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 482
cert_cover_5 5 1 0 4 5 6 162 482 2
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 148 724 2
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coverFacet 9 456
cert_cover_2 9 5 2 6 7 200 456 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0060

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0061.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0061

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 395, 707, 793, 233, 585, 310, 678, 418, 124, 852, 740, 184, 600, 408, 432, 131, 259, 515, 73, 137, 265, 521, 193, 577, 769, 38, 262, 518, 162, 290, 386, 642, 52, 84, 276, 100, 676, 580, 772, 56, 88, 152, 280, 536, 104, 168, 584, 392, 176, 304, 592, 400, 784, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_395, vertices_707, vertices_793, vertices_233, vertices_585, vertices_310, vertices_678, vertices_418, vertices_124, vertices_852, vertices_740, vertices_184, vertices_600, vertices_408, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_73, vertices_137, vertices_265, vertices_521, vertices_193, vertices_577, vertices_769, vertices_38, vertices_262, vertices_518, vertices_162, vertices_290, vertices_386, vertices_642, vertices_52, vertices_84, vertices_276, vertices_100, vertices_676, vertices_580, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_584, vertices_392, vertices_176, vertices_304, vertices_592, vertices_400, vertices_784, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_395), (false, vertices_707), (false, vertices_793), (false, vertices_233), (false, vertices_585), (true, vertices_38), (true, vertices_162), (true, vertices_290), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_100), (true, vertices_676), (true, vertices_580), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_176), (true, vertices_304), (true, vertices_592), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 18 else
  if p.val = (false, vertices_395) then 19 else
  if p.val = (false, vertices_707) then 20 else
  if p.val = (false, vertices_793) then 24 else
  if p.val = (false, vertices_233) then 25 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_676) then 22 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(true, vertices_676), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 6 8 676
cert_row_4 1 0 1 3 4 7 310 38 2
cert_row_4 2 1 2 3 4 5 124 52 1
cert_row_4 3 1 3 5 7 8 852 84 3
cert_rows
cert_pivot_2 6 0 2 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 1 0 1 3 4 38 310 2
cert_coverFacet 1 678
cert_cover_5 1 0 0 1 4 6 38 678 3
cert_coverFacet 2 418
cert_cover_2 2 4 0 6 7 162 418 3
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 4 52 124 1
cert_coverFacet 4 852
cert_cover_5 4 3 1 3 5 7 84 852 3
cert_coverFacet 5 740
cert_cover_5 5 0 1 4 5 6 100 740 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 432
cert_cover_2 9 4 3 6 7 176 432 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0061

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0062.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0062

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [115, 397, 789, 229, 581, 433, 593, 782, 58, 282, 682, 850, 738, 716, 312, 424, 69, 133, 261, 517, 49, 81, 273, 529, 97, 161, 577, 385, 26, 42, 266, 522, 50, 82, 274, 98, 674, 578, 770, 140, 268, 524, 196, 580, 772, 56, 280, 168, 296, 392, 648, 304, 592, 784, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_115, vertices_397, vertices_789, vertices_229, vertices_581, vertices_433, vertices_593, vertices_782, vertices_58, vertices_282, vertices_682, vertices_850, vertices_738, vertices_716, vertices_312, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_517, vertices_49, vertices_81, vertices_273, vertices_529, vertices_97, vertices_161, vertices_577, vertices_385, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_82, vertices_274, vertices_98, vertices_674, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_196, vertices_580, vertices_772, vertices_56, vertices_280, vertices_168, vertices_296, vertices_392, vertices_648, vertices_304, vertices_592, vertices_784, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_115), (false, vertices_397), (false, vertices_789), (false, vertices_229), (false, vertices_581), (false, vertices_433), (false, vertices_593), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_674), (true, vertices_578), (true, vertices_770), (true, vertices_524), (true, vertices_56), (true, vertices_280), (true, vertices_168), (true, vertices_296), (true, vertices_648), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_115) then 17 else
  if p.val = (false, vertices_397) then 20 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_433) then 25 else
  if p.val = (false, vertices_593) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_674) then 18 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
cert_nodeAtPriority_21 0 581 1 593 26 42 266 522 274 578 770 524 56 280 168 296 648 704 115 674 397 789 229 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 6 8 674
cert_row_4 1 0 3 5 7 8 850 82 3
cert_row_4 2 0 1 2 7 8 782 266 1
cert_row_4 3 1 2 5 6 8 716 140 2
cert_rows
cert_pivot_2 4 3 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 266 782 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 682
cert_cover_5 3 0 0 2 4 6 42 682 3
cert_coverFacet 4 850
cert_cover_5 4 1 0 3 5 7 82 850 3
cert_coverFacet 5 738
cert_cover_5 5 0 0 4 5 6 98 738 3
cert_coverFacet 6 716
cert_cover_5 6 3 1 2 5 6 140 716 2
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0062

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0063.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0063

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 333, 229, 805, 465, 673, 782, 570, 154, 394, 242, 674, 604, 628, 344, 408, 37, 69, 261, 161, 545, 193, 321, 385, 641, 769, 26, 138, 266, 522, 50, 146, 162, 546, 386, 642, 770, 76, 268, 524, 596, 100, 548, 772, 88, 152, 280, 536, 328, 392, 112, 560, 208, 336, 400, 224, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_333, vertices_229, vertices_805, vertices_465, vertices_673, vertices_782, vertices_570, vertices_154, vertices_394, vertices_242, vertices_674, vertices_604, vertices_628, vertices_344, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_261, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_268, vertices_524, vertices_596, vertices_100, vertices_548, vertices_772, vertices_88, vertices_152, vertices_280, vertices_536, vertices_328, vertices_392, vertices_112, vertices_560, vertices_208, vertices_336, vertices_400, vertices_224, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_333), (false, vertices_229), (false, vertices_805), (false, vertices_465), (false, vertices_673), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_162), (true, vertices_546), (true, vertices_524), (true, vertices_596), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_392), (true, vertices_112), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 19 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_333) then 20 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_805) then 23 else
  if p.val = (false, vertices_465) then 26 else
  if p.val = (false, vertices_673) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_162) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_596) then 24 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_112) then 15 else
  if p.val = (true, vertices_560) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_2 1 1 3 5 8 596
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 0 3 4 5 6 242 50 3
cert_rows
cert_pivot_2 7 1 2 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 570
cert_cover_5 1 2 0 2 3 4 26 570 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 242
cert_cover_5 4 3 0 3 4 5 50 242 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 604
cert_cover_5 6 1 1 2 3 5 76 604 2
cert_coverFacet 7 628
cert_cover_5 7 1 1 3 4 5 596 628 2
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coverFacet 9 408
cert_cover_2 9 3 2 6 7 152 408 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0063

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0064.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0064

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 779, 451, 117, 805, 481, 666, 426, 706, 284, 540, 780, 308, 724, 248, 312, 67, 259, 515, 37, 69, 517, 97, 289, 449, 769, 138, 266, 522, 194, 578, 386, 642, 28, 268, 524, 52, 84, 276, 532, 292, 580, 772, 56, 152, 280, 536, 168, 296, 776, 112, 304, 208, 656, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_779, vertices_451, vertices_117, vertices_805, vertices_481, vertices_666, vertices_426, vertices_706, vertices_284, vertices_540, vertices_780, vertices_308, vertices_724, vertices_248, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_37, vertices_69, vertices_517, vertices_97, vertices_289, vertices_449, vertices_769, vertices_138, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_642, vertices_28, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_532, vertices_292, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_776, vertices_112, vertices_304, vertices_208, vertices_656, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_779), (false, vertices_451), (false, vertices_117), (false, vertices_805), (false, vertices_481), (true, vertices_138), (true, vertices_642), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_532), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_296), (true, vertices_304), (true, vertices_208), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 24 25 26 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 18 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_451) then 27 else
  if p.val = (false, vertices_117) then 21 else
  if p.val = (false, vertices_805) then 22 else
  if p.val = (false, vertices_481) then 28 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_656) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 28 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 138 2
cert_row_4 1 0 2 3 6 8 666 138 2
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 666
cert_cover_5 0 1 0 2 3 6 138 666 2
cert_coverFacet 1 426
cert_cover_5 1 0 0 2 4 6 138 426 2
cert_coverFacet 2 706
cert_cover_2 2 5 0 6 8 194 706 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 724
cert_cover_5 7 2 1 3 5 6 84 724 3
cert_coverFacet 8 248
cert_cover_5 8 3 2 3 4 5 56 248 3
cert_coverFacet 9 312
cert_cover_2 9 3 2 4 7 56 312 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0064

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0065.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0065

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 805, 121, 793, 305, 737, 270, 526, 406, 678, 458, 706, 780, 244, 308, 472, 25, 73, 521, 49, 273, 97, 289, 545, 577, 769, 14, 134, 262, 518, 74, 266, 522, 194, 578, 386, 642, 268, 524, 52, 148, 276, 164, 292, 548, 772, 88, 280, 456, 776, 112, 304, 208, 400, 224, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_805, vertices_121, vertices_793, vertices_305, vertices_737, vertices_270, vertices_526, vertices_406, vertices_678, vertices_458, vertices_706, vertices_780, vertices_244, vertices_308, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_521, vertices_49, vertices_273, vertices_97, vertices_289, vertices_545, vertices_577, vertices_769, vertices_14, vertices_134, vertices_262, vertices_518, vertices_74, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_642, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_164, vertices_292, vertices_548, vertices_772, vertices_88, vertices_280, vertices_456, vertices_776, vertices_112, vertices_304, vertices_208, vertices_400, vertices_224, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_805), (false, vertices_121), (false, vertices_793), (false, vertices_305), (false, vertices_737), (true, vertices_14), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_164), (true, vertices_456), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 21 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 18 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_121) then 22 else
  if p.val = (false, vertices_793) then 23 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_52) then 11 else
  if p.val = (true, vertices_148) then 12 else
  if p.val = (true, vertices_276) then 13 else
  if p.val = (true, vertices_164) then 14 else
  if p.val = (true, vertices_456) then 24 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_456), by decide +kernel⟩
  | 25 => Sum.inl 3
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
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 244
cert_cover_5 7 3 1 3 4 5 52 244 3
cert_coverFacet 8 308
cert_cover_2 8 3 1 4 7 52 308 3
cert_coverFacet 9 472
cert_cover_5 9 0 2 3 5 6 88 472 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0065

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0066.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0066

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 333, 789, 709, 233, 393, 566, 154, 794, 394, 178, 738, 372, 612, 376, 184, 69, 261, 517, 73, 137, 265, 193, 385, 641, 769, 26, 138, 266, 50, 146, 530, 162, 546, 386, 642, 770, 52, 276, 532, 100, 548, 324, 580, 56, 152, 280, 104, 168, 328, 392, 368, 176, 784, 224, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_333, vertices_789, vertices_709, vertices_233, vertices_393, vertices_566, vertices_154, vertices_794, vertices_394, vertices_178, vertices_738, vertices_372, vertices_612, vertices_376, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_193, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_50, vertices_146, vertices_530, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_52, vertices_276, vertices_532, vertices_100, vertices_548, vertices_324, vertices_580, vertices_56, vertices_152, vertices_280, vertices_104, vertices_168, vertices_328, vertices_392, vertices_368, vertices_176, vertices_784, vertices_224, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_333), (false, vertices_789), (false, vertices_709), (false, vertices_233), (false, vertices_393), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_52), (true, vertices_100), (true, vertices_548), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_368), (true, vertices_176), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_333) then 20 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_233) then 24 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_162) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_280) then 14 else
  if p.val = (true, vertices_368) then 26 else
  if p.val = (true, vertices_176) then 15 else
  if p.val = (true, vertices_608) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(true, vertices_368), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 50 1
cert_row_4 1 0 2 3 7 8 794 26 3
cert_row_2 2 3 4 5 7 368
cert_row_4 3 0 4 5 6 8 738 162 2
cert_rows
cert_pivot_2 1 2 3 0
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 50 566 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 794
cert_cover_5 2 1 0 2 3 7 26 794 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 738
cert_cover_5 5 3 0 4 5 6 162 738 2
cert_coverFacet 6 372
cert_cover_5 6 2 1 3 4 5 52 372 3
cert_coverFacet 7 612
cert_cover_2 7 4 1 5 8 100 612 3
cert_coverFacet 8 376
cert_cover_5 8 2 2 3 4 5 56 376 3
cert_coverFacet 9 184
cert_cover_2 9 3 2 4 6 56 184 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0066

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0067.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0067

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 157, 781, 281, 817, 721, 806, 454, 362, 626, 706, 460, 184, 312, 232, 240, 13, 133, 517, 25, 265, 145, 273, 529, 641, 769, 134, 262, 518, 98, 290, 546, 194, 322, 578, 642, 140, 268, 452, 772, 56, 152, 280, 104, 168, 296, 200, 328, 112, 176, 304, 560, 208, 592, 224, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_157, vertices_781, vertices_281, vertices_817, vertices_721, vertices_806, vertices_454, vertices_362, vertices_626, vertices_706, vertices_460, vertices_184, vertices_312, vertices_232, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_25, vertices_265, vertices_145, vertices_273, vertices_529, vertices_641, vertices_769, vertices_134, vertices_262, vertices_518, vertices_98, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_642, vertices_140, vertices_268, vertices_452, vertices_772, vertices_56, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_200, vertices_328, vertices_112, vertices_176, vertices_304, vertices_560, vertices_208, vertices_592, vertices_224, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_157), (false, vertices_781), (false, vertices_281), (false, vertices_817), (false, vertices_721), (true, vertices_262), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_452), (true, vertices_56), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_200), (true, vertices_328), (true, vertices_112), (true, vertices_176), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 24 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 18 else
  if p.val = (false, vertices_157) then 20 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_817) then 25 else
  if p.val = (false, vertices_721) then 26 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_452) then 22 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_112) then 14 else
  if p.val = (true, vertices_176) then 15 else
  if p.val = (true, vertices_224) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_452), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 5 6 7 452
cert_row_4 1 0 1 4 7 8 806 262 2
cert_row_4 2 0 2 4 5 7 362 98 1
cert_row_4 3 0 3 4 5 8 626 98 1
cert_rows
cert_pivot_2 6 1 2 0
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 262 806 2
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 134 454 2
cert_coverFacet 2 362
cert_cover_5 2 2 0 2 4 5 98 362 1
cert_coverFacet 3 626
cert_cover_5 3 3 0 3 4 5 98 626 1
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 460
cert_cover_5 5 0 1 2 5 6 140 460 2
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 232
cert_cover_2 8 4 2 5 6 104 232 3
cert_coverFacet 9 240
cert_cover_2 9 4 3 5 6 112 240 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0067

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0068.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0068

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 781, 601, 457, 241, 401, 558, 182, 646, 626, 402, 898, 364, 484, 900, 616, 73, 265, 521, 81, 145, 273, 529, 193, 385, 769, 38, 134, 518, 50, 146, 274, 530, 546, 386, 642, 770, 44, 268, 524, 356, 164, 388, 644, 772, 104, 552, 328, 584, 112, 176, 592, 400, 224, 608, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_781, vertices_601, vertices_457, vertices_241, vertices_401, vertices_558, vertices_182, vertices_646, vertices_626, vertices_402, vertices_898, vertices_364, vertices_484, vertices_900, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_529, vertices_193, vertices_385, vertices_769, vertices_38, vertices_134, vertices_518, vertices_50, vertices_146, vertices_274, vertices_530, vertices_546, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_524, vertices_356, vertices_164, vertices_388, vertices_644, vertices_772, vertices_104, vertices_552, vertices_328, vertices_584, vertices_112, vertices_176, vertices_592, vertices_400, vertices_224, vertices_608, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_781), (false, vertices_601), (false, vertices_457), (false, vertices_241), (false, vertices_401), (true, vertices_38), (true, vertices_134), (true, vertices_518), (true, vertices_50), (true, vertices_146), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_44), (true, vertices_356), (true, vertices_164), (true, vertices_388), (true, vertices_644), (true, vertices_104), (true, vertices_552), (true, vertices_608), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (false, vertices_241) then 26 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_356) then 21 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_644) then 12 else
  if p.val = (true, vertices_104) then 13 else
  if p.val = (true, vertices_552) then 14 else
  if p.val = (true, vertices_608) then 15 else
  if p.val = (true, vertices_896) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_356), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 7 356
cert_row_4 1 0 1 2 4 8 558 38 2
cert_row_4 2 0 1 3 4 6 182 38 2
cert_row_4 3 0 3 4 5 8 626 50 3
cert_rows
cert_pivot_2 7 2 1 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 38 558 2
cert_coverFacet 1 182
cert_cover_5 1 2 0 1 3 4 38 182 2
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 626
cert_cover_5 3 3 0 3 4 5 50 626 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 364
cert_cover_5 6 0 1 2 4 5 44 364 3
cert_coverFacet 7 484
cert_cover_5 7 0 1 4 5 6 356 484 3
cert_coverFacet 8 900
cert_cover_2 8 6 1 7 8 388 900 3
cert_coverFacet 9 616
cert_cover_2 9 4 2 5 8 104 616 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0068

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0069.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0069

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 541, 409, 361, 585, 721, 558, 182, 710, 434, 866, 284, 300, 308, 660, 616, 25, 73, 265, 521, 145, 529, 193, 321, 577, 385, 38, 134, 518, 178, 290, 546, 194, 322, 578, 386, 28, 44, 268, 524, 52, 148, 276, 532, 292, 644, 280, 104, 296, 552, 584, 304, 400, 656, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_541, vertices_409, vertices_361, vertices_585, vertices_721, vertices_558, vertices_182, vertices_710, vertices_434, vertices_866, vertices_284, vertices_300, vertices_308, vertices_660, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_521, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_38, vertices_134, vertices_518, vertices_178, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_28, vertices_44, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_532, vertices_292, vertices_644, vertices_280, vertices_104, vertices_296, vertices_552, vertices_584, vertices_304, vertices_400, vertices_656, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_541), (false, vertices_409), (false, vertices_361), (false, vertices_585), (false, vertices_721), (true, vertices_38), (true, vertices_134), (true, vertices_518), (true, vertices_178), (true, vertices_290), (true, vertices_546), (true, vertices_578), (true, vertices_44), (true, vertices_268), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_292), (true, vertices_644), (true, vertices_552), (true, vertices_304), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 18 else
  if p.val = (false, vertices_541) then 21 else
  if p.val = (false, vertices_409) then 23 else
  if p.val = (false, vertices_361) then 24 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (false, vertices_721) then 26 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_178) then 19 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_292) then 12 else
  if p.val = (true, vertices_644) then 13 else
  if p.val = (true, vertices_552) then 14 else
  if p.val = (true, vertices_304) then 15 else
  if p.val = (true, vertices_608) then 16 else
  0
cert_priority
cert_nodeAtPriority_33 585 38 134 518 290 546 578 44 268 52 148 276 292 644 552 304 608 451 178 541 409 361 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 6 178
cert_row_4 1 0 1 2 4 8 558 38 2
cert_row_4 2 0 1 5 6 8 710 134 2
cert_row_4 3 0 4 5 7 8 866 290 2
cert_rows
cert_pivot_2 3 2 1 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 38 558 2
cert_coverFacet 1 182
cert_cover_5 1 0 0 1 3 4 38 182 2
cert_coverFacet 2 710
cert_cover_5 2 2 0 1 5 6 134 710 2
cert_coverFacet 3 434
cert_cover_5 3 0 0 3 4 7 178 434 3
cert_coverFacet 4 866
cert_cover_5 4 3 0 4 5 7 290 866 2
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coverFacet 8 660
cert_cover_2 8 3 1 6 8 148 660 3
cert_coverFacet 9 616
cert_cover_2 9 4 2 5 8 104 616 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0069

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0070.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0070

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 589, 229, 901, 625, 417, 782, 570, 154, 394, 242, 418, 348, 468, 600, 408, 69, 133, 517, 97, 161, 289, 545, 577, 385, 769, 26, 138, 266, 522, 50, 146, 162, 290, 546, 386, 770, 76, 268, 524, 340, 196, 388, 772, 88, 152, 280, 536, 584, 392, 112, 560, 208, 592, 400, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_589, vertices_229, vertices_901, vertices_625, vertices_417, vertices_782, vertices_570, vertices_154, vertices_394, vertices_242, vertices_418, vertices_348, vertices_468, vertices_600, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_97, vertices_161, vertices_289, vertices_545, vertices_577, vertices_385, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_76, vertices_268, vertices_524, vertices_340, vertices_196, vertices_388, vertices_772, vertices_88, vertices_152, vertices_280, vertices_536, vertices_584, vertices_392, vertices_112, vertices_560, vertices_208, vertices_592, vertices_400, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_589), (false, vertices_229), (false, vertices_901), (false, vertices_625), (false, vertices_417), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_162), (true, vertices_386), (true, vertices_268), (true, vertices_340), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_392), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 19 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_589) then 20 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_901) then 23 else
  if p.val = (false, vertices_625) then 26 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_162) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_340) then 24 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_340), by decide +kernel⟩
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
cert_row_4 0 0 3 4 5 6 242 50 3
cert_row_2 1 1 3 5 7 340
cert_row_4 2 0 1 2 7 8 782 266 1
cert_row_4 3 0 2 3 4 8 570 26 3
cert_rows
cert_pivot_2 6 5 1 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 266 782 1
cert_coverFacet 1 570
cert_cover_5 1 3 0 2 3 4 26 570 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 242
cert_cover_5 4 0 0 3 4 5 50 242 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 348
cert_cover_5 6 1 1 2 3 5 76 348 2
cert_coverFacet 7 468
cert_cover_5 7 1 1 3 5 6 340 468 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coverFacet 9 408
cert_cover_2 9 3 2 6 7 152 408 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0070

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0071.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0071

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 587, 557, 185, 817, 721, 270, 526, 598, 454, 426, 300, 340, 788, 804, 496, 75, 41, 137, 521, 49, 145, 529, 545, 193, 577, 14, 70, 262, 518, 138, 266, 522, 194, 578, 386, 44, 268, 524, 84, 276, 532, 292, 548, 324, 772, 168, 296, 176, 304, 208, 336, 592, 784, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_587, vertices_557, vertices_185, vertices_817, vertices_721, vertices_270, vertices_526, vertices_598, vertices_454, vertices_426, vertices_300, vertices_340, vertices_788, vertices_804, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_75, vertices_41, vertices_137, vertices_521, vertices_49, vertices_145, vertices_529, vertices_545, vertices_193, vertices_577, vertices_14, vertices_70, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_44, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_292, vertices_548, vertices_324, vertices_772, vertices_168, vertices_296, vertices_176, vertices_304, vertices_208, vertices_336, vertices_592, vertices_784, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_587), (false, vertices_557), (false, vertices_185), (false, vertices_817), (false, vertices_721), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_386), (true, vertices_268), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_324), (true, vertices_772), (true, vertices_296), (true, vertices_336), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 18 else
  if p.val = (false, vertices_587) then 19 else
  if p.val = (false, vertices_557) then 21 else
  if p.val = (false, vertices_185) then 23 else
  if p.val = (false, vertices_817) then 25 else
  if p.val = (false, vertices_721) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_416) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 70 2
cert_row_4 1 0 1 5 6 7 454 70 3
cert_row_4 2 0 2 4 6 7 426 138 2
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 8 1 0 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 598
cert_cover_5 2 0 0 1 3 5 70 598 2
cert_coverFacet 3 454
cert_cover_5 3 1 0 1 5 6 70 454 3
cert_coverFacet 4 426
cert_cover_5 4 2 0 2 4 6 138 426 2
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 804
cert_cover_2 8 4 1 7 8 292 804 3
cert_coverFacet 9 496
cert_cover_5 9 3 3 4 5 6 176 496 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0071

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0072.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0072

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 179, 403, 611, 841, 481, 542, 278, 562, 188, 204, 332, 780, 468, 568, 744, 147, 35, 259, 515, 97, 161, 321, 577, 385, 769, 22, 262, 518, 50, 274, 530, 546, 28, 76, 140, 268, 524, 148, 276, 196, 324, 772, 56, 536, 168, 552, 200, 328, 584, 776, 176, 560, 400, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_179, vertices_403, vertices_611, vertices_841, vertices_481, vertices_542, vertices_278, vertices_562, vertices_188, vertices_204, vertices_332, vertices_780, vertices_468, vertices_568, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_147, vertices_35, vertices_259, vertices_515, vertices_97, vertices_161, vertices_321, vertices_577, vertices_385, vertices_769, vertices_22, vertices_262, vertices_518, vertices_50, vertices_274, vertices_530, vertices_546, vertices_28, vertices_76, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_196, vertices_324, vertices_772, vertices_56, vertices_536, vertices_168, vertices_552, vertices_200, vertices_328, vertices_584, vertices_776, vertices_176, vertices_560, vertices_400, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_179), (false, vertices_403), (false, vertices_611), (false, vertices_841), (false, vertices_481), (true, vertices_22), (true, vertices_530), (true, vertices_28), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_196), (true, vertices_324), (true, vertices_56), (true, vertices_536), (true, vertices_168), (true, vertices_552), (true, vertices_200), (true, vertices_560)] (by decide +kernel)
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
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_552) then 14 else
  if p.val = (true, vertices_200) then 15 else
  if p.val = (true, vertices_560) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
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
cert_row_4 0 0 1 2 3 8 542 22 2
cert_row_4 1 1 3 5 6 7 468 148 2
cert_row_4 2 1 2 3 4 6 188 28 3
cert_row_4 3 2 4 5 6 8 744 168 2
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 22 542 2
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 562
cert_cover_2 2 3 0 4 8 50 562 3
cert_coverFacet 3 188
cert_cover_5 3 2 1 2 3 4 28 188 3
cert_coverFacet 4 204
cert_cover_2 4 2 1 5 6 76 204 3
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 468
cert_cover_5 7 1 1 3 5 6 148 468 2
cert_coverFacet 8 568
cert_cover_2 8 3 2 4 8 56 568 3
cert_coverFacet 9 744
cert_cover_5 9 3 2 4 5 6 168 744 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0072

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3933 : Certifies 3933 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0042.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3934 : Certifies 3934 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0043.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3935 : Certifies 3935 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0044.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3936 : Certifies 3936 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0045.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3937 : Certifies 3937 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0046.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3938 : Certifies 3938 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0048.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3939 : Certifies 3939 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0049.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3940 : Certifies 3940 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0050.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3941 : Certifies 3941 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0051.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3942 : Certifies 3942 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0052.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3943 : Certifies 3943 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0053.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3944 : Certifies 3944 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0054.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3945 : Certifies 3945 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0055.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3946 : Certifies 3946 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0056.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3947 : Certifies 3947 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0057.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3948 : Certifies 3948 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0058.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3949 : Certifies 3949 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0059.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3950 : Certifies 3950 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0060.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3951 : Certifies 3951 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0061.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3952 : Certifies 3952 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0062.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3953 : Certifies 3953 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0063.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3954 : Certifies 3954 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0064.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3955 : Certifies 3955 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0065.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3956 : Certifies 3956 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0066.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3957 : Certifies 3957 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0067.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3958 : Certifies 3958 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0068.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3959 : Certifies 3959 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0069.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3960 : Certifies 3960 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0070.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3961 : Certifies 3961 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0071.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3962 : Certifies 3962 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0072.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B130 (j : Fin 30) :
    Certifies (3933 + j.val) := by
  fin_cases j
  · exact projection_3933
  · exact projection_3934
  · exact projection_3935
  · exact projection_3936
  · exact projection_3937
  · exact projection_3938
  · exact projection_3939
  · exact projection_3940
  · exact projection_3941
  · exact projection_3942
  · exact projection_3943
  · exact projection_3944
  · exact projection_3945
  · exact projection_3946
  · exact projection_3947
  · exact projection_3948
  · exact projection_3949
  · exact projection_3950
  · exact projection_3951
  · exact projection_3952
  · exact projection_3953
  · exact projection_3954
  · exact projection_3955
  · exact projection_3956
  · exact projection_3957
  · exact projection_3958
  · exact projection_3959
  · exact projection_3960
  · exact projection_3961
  · exact projection_3962

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
