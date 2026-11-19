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
/- Source: ProjectionCertificates/R_m16e10q1_0133.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0133

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 205, 613, 645, 153, 841, 913, 806, 122, 618, 778, 434, 244, 420, 900, 216, 69, 133, 517, 25, 73, 137, 265, 145, 273, 577, 641, 769, 26, 106, 266, 522, 50, 274, 290, 546, 770, 100, 164, 292, 548, 196, 388, 644, 772, 88, 152, 200, 584, 776, 112, 176, 208, 400, 608, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_205, vertices_613, vertices_645, vertices_153, vertices_841, vertices_913, vertices_806, vertices_122, vertices_618, vertices_778, vertices_434, vertices_244, vertices_420, vertices_900, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_25, vertices_73, vertices_137, vertices_265, vertices_145, vertices_273, vertices_577, vertices_641, vertices_769, vertices_26, vertices_106, vertices_266, vertices_522, vertices_50, vertices_274, vertices_290, vertices_546, vertices_770, vertices_100, vertices_164, vertices_292, vertices_548, vertices_196, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_200, vertices_584, vertices_776, vertices_112, vertices_176, vertices_208, vertices_400, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_205), (false, vertices_613), (false, vertices_645), (false, vertices_153), (false, vertices_841), (false, vertices_913), (true, vertices_106), (true, vertices_522), (true, vertices_50), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_164), (true, vertices_292), (true, vertices_388), (true, vertices_772), (true, vertices_88), (true, vertices_112), (true, vertices_176), (true, vertices_208), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 17 else
  if p.val = (false, vertices_205) then 20 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_153) then 1 else
  if p.val = (false, vertices_841) then 23 else
  if p.val = (false, vertices_913) then 25 else
  if p.val = (true, vertices_106) then 18 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
cert_nodeAtPriority_50 1 645 0 153 522 50 290 546 770 164 292 388 772 88 112 176 208 416 283 106 205 613 841 913
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 3 4 6 7 434 50 3
cert_row_4 3 1 3 4 5 6 244 100 1
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 4 26 122 3
cert_coverFacet 2 618
cert_cover_5 2 0 0 2 4 8 106 618 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 434
cert_cover_5 4 2 0 3 4 6 50 434 3
cert_coverFacet 5 244
cert_cover_5 5 3 1 3 4 5 100 244 1
cert_coverFacet 6 420
cert_cover_2 6 4 1 6 7 164 420 3
cert_coverFacet 7 900
cert_cover_2 7 6 1 7 8 388 900 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0133

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0134.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0134

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [199, 583, 779, 403, 425, 713, 566, 150, 786, 620, 116, 468, 824, 232, 368, 480, 71, 131, 259, 515, 137, 265, 521, 193, 577, 385, 22, 134, 518, 146, 274, 530, 770, 52, 84, 148, 100, 548, 196, 580, 104, 168, 296, 552, 200, 584, 776, 112, 304, 560, 336, 400, 784, 224, 352, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_199, vertices_583, vertices_779, vertices_403, vertices_425, vertices_713, vertices_566, vertices_150, vertices_786, vertices_620, vertices_116, vertices_468, vertices_824, vertices_232, vertices_368, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_71, vertices_131, vertices_259, vertices_515, vertices_137, vertices_265, vertices_521, vertices_193, vertices_577, vertices_385, vertices_22, vertices_134, vertices_518, vertices_146, vertices_274, vertices_530, vertices_770, vertices_52, vertices_84, vertices_148, vertices_100, vertices_548, vertices_196, vertices_580, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_584, vertices_776, vertices_112, vertices_304, vertices_560, vertices_336, vertices_400, vertices_784, vertices_224, vertices_352, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_199), (false, vertices_583), (false, vertices_779), (false, vertices_403), (false, vertices_425), (false, vertices_713), (true, vertices_22), (true, vertices_530), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_100), (true, vertices_548), (true, vertices_104), (true, vertices_552), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_224), (true, vertices_352), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 20 17 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_199) then 18 else
  if p.val = (false, vertices_583) then 19 else
  if p.val = (false, vertices_779) then 21 else
  if p.val = (false, vertices_403) then 22 else
  if p.val = (false, vertices_425) then 24 else
  if p.val = (false, vertices_713) then 25 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_352) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 20 => Sum.inl 0
  | 21 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_4 0 0 1 3 4 8 566 22 3
cert_row_4 1 1 3 5 6 7 468 84 3
cert_row_4 2 1 2 4 5 8 620 100 1
cert_row_4 3 2 3 4 7 8 824 296 1
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 22 566 3
cert_coverFacet 1 150
cert_cover_2 1 1 0 3 6 22 150 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 620
cert_cover_5 3 2 1 2 4 5 100 620 1
cert_coverFacet 4 116
cert_cover_2 4 3 1 4 5 52 116 3
cert_coverFacet 5 468
cert_cover_5 5 1 1 3 5 6 84 468 3
cert_coverFacet 6 824
cert_cover_5 6 3 2 3 4 7 296 824 1
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coverFacet 9 480
cert_cover_2 9 5 4 6 7 224 480 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0134

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0135.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0135

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 781, 425, 713, 369, 225, 654, 342, 150, 774, 626, 658, 188, 316, 688, 736, 137, 265, 521, 97, 161, 289, 193, 321, 577, 769, 22, 134, 262, 518, 82, 146, 530, 322, 578, 642, 770, 60, 140, 268, 524, 148, 276, 772, 168, 296, 648, 112, 176, 304, 560, 336, 656, 224, 608, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_781, vertices_425, vertices_713, vertices_369, vertices_225, vertices_654, vertices_342, vertices_150, vertices_774, vertices_626, vertices_658, vertices_188, vertices_316, vertices_688, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_769, vertices_22, vertices_134, vertices_262, vertices_518, vertices_82, vertices_146, vertices_530, vertices_322, vertices_578, vertices_642, vertices_770, vertices_60, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_772, vertices_168, vertices_296, vertices_648, vertices_112, vertices_176, vertices_304, vertices_560, vertices_336, vertices_656, vertices_224, vertices_608, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_781), (false, vertices_425), (false, vertices_713), (false, vertices_369), (false, vertices_225), (true, vertices_22), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_642), (true, vertices_60), (true, vertices_140), (true, vertices_148), (true, vertices_276), (true, vertices_176), (true, vertices_560), (true, vertices_656), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_425) then 23 else
  if p.val = (false, vertices_713) then 24 else
  if p.val = (false, vertices_369) then 26 else
  if p.val = (false, vertices_225) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_60) then 21 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_608) then 15 else
  if p.val = (true, vertices_672) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 134 2
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 1 3 5 7 342 22 3
cert_row_4 3 0 3 4 5 8 626 82 2
cert_rows
cert_pivot_2 6 2 1 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 134 654 2
cert_coverFacet 1 342
cert_cover_5 1 2 0 1 3 5 22 342 3
cert_coverFacet 2 150
cert_cover_2 2 1 0 3 6 22 150 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 626
cert_cover_5 4 3 0 3 4 5 82 626 2
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 188
cert_cover_5 6 1 1 2 3 6 60 188 3
cert_coverFacet 7 316
cert_cover_5 7 1 1 2 3 7 60 316 3
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coverFacet 9 736
cert_cover_2 9 5 4 6 8 224 736 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0135

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0136.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0136

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 213, 533, 837, 409, 481, 182, 566, 154, 282, 682, 842, 620, 228, 360, 424, 21, 69, 517, 145, 273, 529, 193, 321, 385, 769, 54, 26, 138, 266, 522, 146, 274, 530, 162, 546, 770, 148, 532, 100, 164, 548, 196, 580, 152, 280, 104, 168, 296, 552, 328, 584, 392, 224, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_213, vertices_533, vertices_837, vertices_409, vertices_481, vertices_182, vertices_566, vertices_154, vertices_282, vertices_682, vertices_842, vertices_620, vertices_228, vertices_360, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_517, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_385, vertices_769, vertices_54, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_770, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_552, vertices_328, vertices_584, vertices_392, vertices_224, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_213), (false, vertices_533), (false, vertices_837), (false, vertices_409), (false, vertices_481), (true, vertices_54), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_162), (true, vertices_546), (true, vertices_100), (true, vertices_164), (true, vertices_548), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_213) then 21 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (false, vertices_409) then 24 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_54) then 19 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_552) then 14 else
  if p.val = (true, vertices_328) then 15 else
  if p.val = (true, vertices_584) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
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
cert_row_2 0 0 1 3 4 54
cert_row_4 1 0 2 4 6 8 682 138 2
cert_row_4 2 0 2 5 7 8 842 266 2
cert_row_4 3 1 2 4 5 8 620 100 1
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 6 54 182 3
cert_coverFacet 1 566
cert_cover_5 1 0 0 1 3 8 54 566 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 682
cert_cover_5 4 1 0 2 4 6 138 682 2
cert_coverFacet 5 842
cert_cover_5 5 2 0 2 5 7 266 842 2
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 100 620 1
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coverFacet 9 424
cert_cover_2 9 4 2 6 7 168 424 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0136

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0137.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0137

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 557, 789, 165, 57, 601, 433, 230, 614, 774, 458, 850, 184, 344, 408, 744, 37, 133, 261, 517, 25, 41, 521, 49, 273, 529, 161, 385, 102, 134, 262, 518, 194, 322, 578, 386, 770, 164, 548, 772, 56, 88, 152, 280, 168, 552, 200, 328, 584, 392, 176, 336, 592, 400, 784, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_557, vertices_789, vertices_165, vertices_57, vertices_601, vertices_433, vertices_230, vertices_614, vertices_774, vertices_458, vertices_850, vertices_184, vertices_344, vertices_408, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_517, vertices_25, vertices_41, vertices_521, vertices_49, vertices_273, vertices_529, vertices_161, vertices_385, vertices_102, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_164, vertices_548, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_168, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_176, vertices_336, vertices_592, vertices_400, vertices_784, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_557), (false, vertices_789), (false, vertices_165), (false, vertices_57), (false, vertices_601), (false, vertices_433), (true, vertices_102), (true, vertices_518), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_200), (true, vertices_328), (true, vertices_392), (true, vertices_336), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 17 else
  if p.val = (false, vertices_557) then 20 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_57) then 1 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_433) then 25 else
  if p.val = (true, vertices_102) then 18 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_608) then 15 else
  0
cert_priority
cert_nodeAtPriority_50 1 165 0 57 518 194 322 578 770 152 280 168 200 328 392 336 224 608 391 102 557 789 601 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 5 102
cert_row_4 1 0 3 5 7 8 850 322 1
cert_row_4 2 0 2 5 6 7 458 194 1
cert_row_4 3 2 4 5 6 8 744 168 2
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 0 0 1 4 6 102 230 3
cert_coverFacet 1 614
cert_cover_5 1 0 0 1 4 8 102 614 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 458
cert_cover_5 3 2 0 2 5 6 194 458 1
cert_coverFacet 4 850
cert_cover_5 4 1 0 3 5 7 322 850 1
cert_coverFacet 5 184
cert_cover_2 5 3 2 4 6 56 184 3
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 744
cert_cover_5 8 3 2 4 5 6 168 744 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0137

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0138.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0138

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 341, 149, 677, 581, 409, 481, 838, 570, 234, 458, 778, 796, 660, 184, 688, 21, 69, 133, 517, 145, 273, 97, 161, 545, 321, 577, 385, 42, 202, 266, 522, 98, 546, 322, 578, 770, 148, 276, 532, 324, 580, 644, 772, 56, 152, 280, 536, 168, 392, 776, 176, 560, 656, 224, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_341, vertices_149, vertices_677, vertices_581, vertices_409, vertices_481, vertices_838, vertices_570, vertices_234, vertices_458, vertices_778, vertices_796, vertices_660, vertices_184, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_133, vertices_517, vertices_145, vertices_273, vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_42, vertices_202, vertices_266, vertices_522, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_148, vertices_276, vertices_532, vertices_324, vertices_580, vertices_644, vertices_772, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_392, vertices_776, vertices_176, vertices_560, vertices_656, vertices_224, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_341), (false, vertices_149), (false, vertices_677), (false, vertices_581), (false, vertices_409), (false, vertices_481), (true, vertices_42), (true, vertices_202), (true, vertices_266), (true, vertices_522), (true, vertices_322), (true, vertices_770), (true, vertices_532), (true, vertices_772), (true, vertices_56), (true, vertices_536), (true, vertices_168), (true, vertices_776), (true, vertices_176), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_341) then 20 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_581) then 1 else
  if p.val = (false, vertices_409) then 23 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_656) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 1 149 0 581 42 266 522 322 770 532 772 56 536 168 776 176 560 656 611 202 341 677 409 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 2 3 4 8 570 42 2
cert_row_4 3 1 2 3 7 8 796 276 1
cert_rows
cert_pivot_2 6 5 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 570
cert_cover_5 1 2 0 2 3 4 42 570 2
cert_coverFacet 2 234
cert_cover_5 2 0 0 2 4 5 42 234 3
cert_coverFacet 3 458
cert_cover_5 3 0 0 2 5 7 202 458 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 796
cert_cover_5 5 3 1 2 3 7 276 796 1
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0138

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0139.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0139

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 611, 163, 589, 425, 329, 369, 902, 818, 418, 220, 652, 628, 404, 788, 472, 35, 131, 515, 73, 137, 265, 521, 97, 161, 289, 321, 577, 162, 290, 546, 386, 642, 770, 76, 140, 524, 84, 148, 276, 532, 580, 388, 644, 772, 216, 328, 392, 648, 112, 304, 560, 336, 400, 784, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_611, vertices_163, vertices_589, vertices_425, vertices_329, vertices_369, vertices_902, vertices_818, vertices_418, vertices_220, vertices_652, vertices_628, vertices_404, vertices_788, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_73, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_321, vertices_577, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_580, vertices_388, vertices_644, vertices_772, vertices_216, vertices_328, vertices_392, vertices_648, vertices_112, vertices_304, vertices_560, vertices_336, vertices_400, vertices_784, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_611), (false, vertices_163), (false, vertices_589), (false, vertices_425), (false, vertices_329), (false, vertices_369), (true, vertices_290), (true, vertices_386), (true, vertices_770), (true, vertices_140), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_216), (true, vertices_560), (true, vertices_400), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 17 else
  if p.val = (false, vertices_611) then 18 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_589) then 20 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_216) then 23 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 23 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 5 6 216
cert_row_4 1 0 1 6 7 8 902 386 1
cert_row_4 2 0 3 4 7 8 818 290 1
cert_row_4 3 1 3 4 5 8 628 84 2
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 818
cert_cover_5 1 2 0 3 4 7 290 818 1
cert_coverFacet 2 418
cert_cover_2 2 4 0 6 7 162 418 3
cert_coverFacet 3 220
cert_cover_5 3 0 1 2 3 5 76 220 2
cert_coverFacet 4 652
cert_cover_2 4 2 1 6 8 140 652 3
cert_coverFacet 5 628
cert_cover_5 5 3 1 3 4 5 84 628 2
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 472
cert_cover_5 8 0 2 3 5 7 216 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0139

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0140.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0140

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 611, 163, 781, 425, 817, 710, 370, 418, 450, 220, 284, 652, 628, 788, 472, 35, 131, 515, 137, 265, 521, 161, 289, 545, 769, 98, 162, 290, 194, 322, 578, 386, 642, 28, 140, 268, 524, 84, 276, 532, 196, 580, 644, 772, 216, 280, 392, 648, 112, 304, 560, 336, 784, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_611, vertices_163, vertices_781, vertices_425, vertices_817, vertices_710, vertices_370, vertices_418, vertices_450, vertices_220, vertices_284, vertices_652, vertices_628, vertices_788, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_137, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_769, vertices_98, vertices_162, vertices_290, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_28, vertices_140, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_196, vertices_580, vertices_644, vertices_772, vertices_216, vertices_280, vertices_392, vertices_648, vertices_112, vertices_304, vertices_560, vertices_336, vertices_784, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_611), (false, vertices_163), (false, vertices_781), (false, vertices_425), (false, vertices_817), (true, vertices_290), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_28), (true, vertices_140), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_196), (true, vertices_580), (true, vertices_644), (true, vertices_216), (true, vertices_280), (true, vertices_112), (true, vertices_336), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_611) then 19 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_425) then 23 else
  if p.val = (false, vertices_817) then 26 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_644) then 12 else
  if p.val = (true, vertices_216) then 24 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_112) then 14 else
  if p.val = (true, vertices_336) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 5 6 216
cert_row_4 1 0 1 5 6 8 710 194 1
cert_row_4 2 0 3 4 5 7 370 98 1
cert_row_4 3 1 3 4 5 8 628 84 2
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 1 0 1 5 6 194 710 1
cert_coverFacet 1 370
cert_cover_5 1 2 0 3 4 5 98 370 1
cert_coverFacet 2 418
cert_cover_2 2 4 0 6 7 162 418 3
cert_coverFacet 3 450
cert_cover_2 3 5 0 6 7 194 450 3
cert_coverFacet 4 220
cert_cover_5 4 0 1 2 3 5 28 220 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 628
cert_cover_5 7 3 1 3 4 5 84 628 2
cert_coverFacet 8 788
cert_cover_2 8 3 1 7 8 276 788 3
cert_coverFacet 9 472
cert_cover_5 9 0 2 3 5 7 216 472 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0140

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0141.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0141

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 173, 781, 453, 649, 721, 806, 122, 618, 306, 466, 556, 436, 184, 600, 664, 13, 133, 261, 137, 521, 193, 321, 577, 641, 769, 106, 50, 82, 274, 290, 546, 322, 578, 770, 44, 524, 164, 292, 548, 388, 772, 56, 88, 152, 536, 168, 552, 584, 648, 176, 304, 208, 592, 400, 656, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_173, vertices_781, vertices_453, vertices_649, vertices_721, vertices_806, vertices_122, vertices_618, vertices_306, vertices_466, vertices_556, vertices_436, vertices_184, vertices_600, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_137, vertices_521, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_106, vertices_50, vertices_82, vertices_274, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_44, vertices_524, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_56, vertices_88, vertices_152, vertices_536, vertices_168, vertices_552, vertices_584, vertices_648, vertices_176, vertices_304, vertices_208, vertices_592, vertices_400, vertices_656, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_173), (false, vertices_781), (false, vertices_453), (false, vertices_649), (false, vertices_721), (true, vertices_106), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_290), (true, vertices_546), (true, vertices_292), (true, vertices_548), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_552), (true, vertices_584), (true, vertices_176), (true, vertices_304), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_173) then 21 else
  if p.val = (false, vertices_781) then 22 else
  if p.val = (false, vertices_453) then 23 else
  if p.val = (false, vertices_649) then 0 else
  if p.val = (false, vertices_721) then 26 else
  if p.val = (true, vertices_106) then 19 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_304) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
cert_nodeAtPriority_45 649 50 82 274 290 546 292 548 56 88 152 536 552 584 176 304 400 835 106 173 781 453 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 3 5 6 7 466 82 3
cert_row_4 3 1 3 4 6 7 436 164 1
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 4 106 122 2
cert_coverFacet 2 618
cert_cover_5 2 0 0 2 4 8 106 618 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 466
cert_cover_5 4 2 0 3 5 6 82 466 3
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 164 436 1
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coverFacet 9 664
cert_cover_2 9 3 2 6 8 152 664 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0141

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0142.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0142

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 109, 269, 677, 841, 625, 158, 286, 646, 690, 850, 172, 408, 488, 240, 464, 13, 37, 261, 517, 73, 265, 97, 545, 577, 769, 30, 134, 262, 518, 146, 274, 530, 642, 770, 44, 140, 268, 164, 644, 152, 280, 104, 168, 328, 392, 112, 176, 560, 208, 336, 592, 400, 224, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_109, vertices_269, vertices_677, vertices_841, vertices_625, vertices_158, vertices_286, vertices_646, vertices_690, vertices_850, vertices_172, vertices_408, vertices_488, vertices_240, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_261, vertices_517, vertices_73, vertices_265, vertices_97, vertices_545, vertices_577, vertices_769, vertices_30, vertices_134, vertices_262, vertices_518, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_44, vertices_140, vertices_268, vertices_164, vertices_644, vertices_152, vertices_280, vertices_104, vertices_168, vertices_328, vertices_392, vertices_112, vertices_176, vertices_560, vertices_208, vertices_336, vertices_592, vertices_400, vertices_224, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_109), (false, vertices_269), (false, vertices_677), (false, vertices_841), (false, vertices_625), (true, vertices_30), (true, vertices_134), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_642), (true, vertices_140), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_392), (true, vertices_176), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 18 else
  if p.val = (false, vertices_109) then 21 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_841) then 24 else
  if p.val = (false, vertices_625) then 26 else
  if p.val = (true, vertices_30) then 19 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
cert_nodeAtPriority_14 269 134 146 274 530 642 140 152 280 168 392 176 208 336 400 224 448 775 30 109 677 841 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 2 4 5 6 7 488 104 3
cert_row_4 2 0 3 4 6 8 690 146 2
cert_row_4 3 0 3 5 7 8 850 274 2
cert_rows
cert_pivot_2 1 2 4 0
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 6 30 158 3
cert_coverFacet 1 286
cert_cover_5 1 0 0 1 2 7 30 286 3
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 690
cert_cover_5 3 2 0 3 4 6 146 690 2
cert_coverFacet 4 850
cert_cover_5 4 3 0 3 5 7 274 850 2
cert_coverFacet 5 172
cert_cover_2 5 2 1 4 6 44 172 3
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 488
cert_cover_5 7 1 2 4 5 6 104 488 3
cert_coverFacet 8 240
cert_cover_2 8 4 3 5 6 112 240 3
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0142

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0143.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0143

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 661, 837, 409, 625, 337, 654, 358, 614, 570, 170, 418, 120, 344, 664, 488, 133, 261, 517, 81, 145, 273, 529, 321, 577, 385, 102, 134, 262, 518, 42, 138, 522, 162, 290, 546, 386, 324, 580, 644, 56, 88, 152, 280, 536, 104, 168, 328, 392, 648, 112, 560, 336, 656, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_661, vertices_837, vertices_409, vertices_625, vertices_337, vertices_654, vertices_358, vertices_614, vertices_570, vertices_170, vertices_418, vertices_120, vertices_344, vertices_664, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_273, vertices_529, vertices_321, vertices_577, vertices_385, vertices_102, vertices_134, vertices_262, vertices_518, vertices_42, vertices_138, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_324, vertices_580, vertices_644, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_328, vertices_392, vertices_648, vertices_112, vertices_560, vertices_336, vertices_656, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_661), (false, vertices_837), (false, vertices_409), (false, vertices_625), (false, vertices_337), (true, vertices_102), (true, vertices_518), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_56), (true, vertices_88), (true, vertices_536), (true, vertices_104), (true, vertices_168), (true, vertices_328), (true, vertices_648), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 18 else
  if p.val = (false, vertices_661) then 21 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (false, vertices_409) then 24 else
  if p.val = (false, vertices_625) then 26 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (true, vertices_102) then 19 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_352) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
cert_nodeAtPriority_14 337 518 42 138 522 162 290 546 56 88 536 104 168 328 648 352 416 391 102 661 837 409 625
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
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coverFacet 9 488
cert_cover_5 9 3 2 4 5 6 104 488 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0143

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0144.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0144

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 109, 589, 309, 901, 625, 654, 602, 202, 242, 402, 898, 300, 396, 488, 432, 77, 37, 261, 517, 49, 273, 529, 97, 577, 769, 74, 138, 522, 82, 146, 274, 530, 194, 386, 642, 770, 44, 140, 268, 524, 292, 388, 644, 104, 296, 200, 584, 392, 112, 176, 304, 592, 400, 224, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_109, vertices_589, vertices_309, vertices_901, vertices_625, vertices_654, vertices_602, vertices_202, vertices_242, vertices_402, vertices_898, vertices_300, vertices_396, vertices_488, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_77, vertices_37, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_97, vertices_577, vertices_769, vertices_74, vertices_138, vertices_522, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_268, vertices_524, vertices_292, vertices_388, vertices_644, vertices_104, vertices_296, vertices_200, vertices_584, vertices_392, vertices_112, vertices_176, vertices_304, vertices_592, vertices_400, vertices_224, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_109), (false, vertices_589), (false, vertices_309), (false, vertices_901), (false, vertices_625), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_140), (true, vertices_268), (true, vertices_296), (true, vertices_200), (true, vertices_392), (true, vertices_176), (true, vertices_400), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 22 19 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_109) then 20 else
  if p.val = (false, vertices_589) then 21 else
  if p.val = (false, vertices_309) then 23 else
  if p.val = (false, vertices_901) then 24 else
  if p.val = (false, vertices_625) then 26 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
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
cert_row_4 1 0 2 3 5 8 602 74 2
cert_row_4 2 0 3 4 5 6 242 82 2
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 602
cert_cover_5 1 1 0 2 3 5 74 602 2
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 82 242 2
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 396
cert_cover_2 7 2 1 6 7 140 396 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 104 488 3
cert_coverFacet 9 432
cert_cover_2 9 4 3 6 7 176 432 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0144

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0145.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0145

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 397, 789, 677, 713, 566, 218, 410, 618, 114, 786, 308, 484, 368, 464, 736, 133, 261, 517, 137, 265, 521, 641, 769, 154, 74, 266, 522, 50, 82, 274, 530, 98, 546, 770, 52, 276, 532, 164, 292, 548, 388, 200, 584, 392, 112, 304, 208, 336, 400, 784, 224, 352, 608, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_397, vertices_789, vertices_677, vertices_713, vertices_566, vertices_218, vertices_410, vertices_618, vertices_114, vertices_786, vertices_308, vertices_484, vertices_368, vertices_464, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_641, vertices_769, vertices_154, vertices_74, vertices_266, vertices_522, vertices_50, vertices_82, vertices_274, vertices_530, vertices_98, vertices_546, vertices_770, vertices_52, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_200, vertices_584, vertices_392, vertices_112, vertices_304, vertices_208, vertices_336, vertices_400, vertices_784, vertices_224, vertices_352, vertices_608, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_397), (false, vertices_789), (false, vertices_677), (false, vertices_713), (true, vertices_154), (true, vertices_74), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_546), (true, vertices_52), (true, vertices_292), (true, vertices_112), (true, vertices_304), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_224), (true, vertices_352), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 21 25 27 28 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_397) then 22 else
  if p.val = (false, vertices_789) then 23 else
  if p.val = (false, vertices_677) then 24 else
  if p.val = (false, vertices_713) then 26 else
  if p.val = (true, vertices_154) then 20 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_352) then 15 else
  if p.val = (true, vertices_608) then 16 else
  if p.val = (true, vertices_448) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 25 => Sum.inl 2
  | 26 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 27 => Sum.inl 3
  | 28 => Sum.inl 4
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 4 5 6 7 484 164 2
cert_row_2 1 0 2 3 6 154
cert_row_4 2 0 1 3 4 8 566 50 1
cert_row_4 3 0 2 4 5 8 618 74 2
cert_rows
cert_pivot_2 7 6 1 0
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 2 0 1 3 4 50 566 1
cert_coverFacet 1 218
cert_cover_5 1 1 0 2 3 5 154 218 3
cert_coverFacet 2 410
cert_cover_5 2 1 0 2 3 7 154 410 3
cert_coverFacet 3 618
cert_cover_5 3 3 0 2 4 5 74 618 2
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 484
cert_cover_5 7 0 1 4 5 6 164 484 2
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coverFacet 10 736
cert_cover_2 10 5 4 6 8 224 736 3
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0145

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0146.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0146

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 781, 425, 713, 817, 590, 566, 86, 370, 226, 706, 220, 412, 788, 464, 480, 137, 265, 521, 161, 289, 545, 641, 769, 22, 70, 518, 50, 82, 98, 162, 546, 194, 578, 642, 156, 76, 268, 524, 84, 276, 532, 772, 200, 584, 392, 304, 560, 208, 336, 400, 784, 224, 352, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_781, vertices_425, vertices_713, vertices_817, vertices_590, vertices_566, vertices_86, vertices_370, vertices_226, vertices_706, vertices_220, vertices_412, vertices_788, vertices_464, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_22, vertices_70, vertices_518, vertices_50, vertices_82, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_156, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_772, vertices_200, vertices_584, vertices_392, vertices_304, vertices_560, vertices_208, vertices_336, vertices_400, vertices_784, vertices_224, vertices_352, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_781), (false, vertices_425), (false, vertices_713), (false, vertices_817), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_50), (true, vertices_82), (true, vertices_98), (true, vertices_194), (true, vertices_578), (true, vertices_156), (true, vertices_76), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_224), (true, vertices_352), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 20 23 26 28 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 19 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_425) then 24 else
  if p.val = (false, vertices_713) then 25 else
  if p.val = (false, vertices_817) then 27 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_156) then 22 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_352) then 16 else
  if p.val = (true, vertices_448) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 28 => Sum.inl 4
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 6 156
cert_row_4 1 0 1 2 5 8 590 70 2
cert_row_4 2 0 1 3 4 8 566 22 3
cert_row_4 3 0 3 4 5 7 370 50 3
cert_rows
cert_pivot_2 6 2 1 0
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 70 590 2
cert_coverFacet 1 566
cert_cover_5 1 2 0 1 3 4 22 566 3
cert_coverFacet 2 86
cert_cover_2 2 1 0 3 5 22 86 3
cert_coverFacet 3 370
cert_cover_5 3 3 0 3 4 5 50 370 3
cert_coverFacet 4 226
cert_cover_2 4 4 0 5 6 98 226 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 220
cert_cover_5 6 0 1 2 3 5 156 220 3
cert_coverFacet 7 412
cert_cover_5 7 0 1 2 3 7 156 412 3
cert_coverFacet 8 788
cert_cover_2 8 3 1 7 8 276 788 3
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coverFacet 10 480
cert_cover_2 10 5 4 6 7 224 480 3
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0146

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0147.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0147

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 589, 677, 453, 625, 353, 782, 902, 154, 282, 650, 370, 178, 348, 696, 600, 69, 133, 517, 97, 161, 289, 545, 321, 577, 385, 774, 26, 138, 266, 522, 50, 146, 274, 162, 290, 386, 642, 76, 268, 524, 324, 388, 644, 88, 152, 280, 536, 584, 648, 112, 176, 560, 336, 592, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_589, vertices_677, vertices_453, vertices_625, vertices_353, vertices_782, vertices_902, vertices_154, vertices_282, vertices_650, vertices_370, vertices_178, vertices_348, vertices_696, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_97, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_774, vertices_26, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_386, vertices_642, vertices_76, vertices_268, vertices_524, vertices_324, vertices_388, vertices_644, vertices_88, vertices_152, vertices_280, vertices_536, vertices_584, vertices_648, vertices_112, vertices_176, vertices_560, vertices_336, vertices_592, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_589), (false, vertices_677), (false, vertices_453), (false, vertices_625), (false, vertices_353), (true, vertices_774), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_642), (true, vertices_268), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_648), (true, vertices_176), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 18 else
  if p.val = (false, vertices_589) then 21 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_453) then 23 else
  if p.val = (false, vertices_625) then 26 else
  if p.val = (false, vertices_353) then 0 else
  if p.val = (true, vertices_774) then 19 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_274) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_176) then 15 else
  if p.val = (true, vertices_336) then 16 else
  0
cert_priority
cert_nodeAtPriority_45 353 26 138 266 522 50 146 274 642 268 88 152 280 536 648 176 336 419 774 589 677 453 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 6 8 696 152 2
cert_row_2 1 0 1 7 8 774
cert_row_4 2 0 3 4 5 7 370 50 3
cert_row_4 3 1 2 3 5 7 348 76 2
cert_rows
cert_pivot_2 6 8 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 774 782 2
cert_coverFacet 1 902
cert_cover_5 1 1 0 1 6 7 774 902 2
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 370
cert_cover_5 5 2 0 3 4 5 50 370 3
cert_coverFacet 6 178
cert_cover_2 6 3 0 4 6 50 178 3
cert_coverFacet 7 348
cert_cover_5 7 3 1 2 3 5 76 348 2
cert_coverFacet 8 696
cert_cover_5 8 0 2 3 4 6 152 696 2
cert_coverFacet 9 600
cert_cover_2 9 3 2 5 8 88 600 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0147

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0148.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0148

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 789, 569, 409, 233, 801, 342, 806, 582, 618, 226, 450, 668, 716, 212, 464, 25, 41, 137, 273, 529, 161, 289, 545, 385, 769, 70, 262, 518, 98, 162, 290, 546, 194, 322, 578, 386, 652, 84, 148, 276, 532, 196, 580, 772, 152, 536, 104, 552, 200, 584, 208, 336, 400, 224, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_789, vertices_569, vertices_409, vertices_233, vertices_801, vertices_342, vertices_806, vertices_582, vertices_618, vertices_226, vertices_450, vertices_668, vertices_716, vertices_212, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_137, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_385, vertices_769, vertices_70, vertices_262, vertices_518, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_652, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_580, vertices_772, vertices_152, vertices_536, vertices_104, vertices_552, vertices_200, vertices_584, vertices_208, vertices_336, vertices_400, vertices_224, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_789), (false, vertices_569), (false, vertices_409), (false, vertices_233), (false, vertices_801), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_98), (true, vertices_546), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_652), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_580), (true, vertices_584), (true, vertices_208), (true, vertices_336), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 18 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_409) then 24 else
  if p.val = (false, vertices_233) then 25 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_652) then 21 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_580) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_336) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
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
cert_row_2 0 1 2 6 8 652
cert_row_4 1 0 1 3 5 7 342 70 2
cert_row_4 2 0 1 4 7 8 806 262 2
cert_row_4 3 0 2 4 5 8 618 98 1
cert_rows
cert_pivot_2 6 3 1 0
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 1 0 1 3 5 70 342 2
cert_coverFacet 1 806
cert_cover_5 1 2 0 1 4 7 262 806 2
cert_coverFacet 2 582
cert_cover_2 2 1 0 5 8 70 582 3
cert_coverFacet 3 618
cert_cover_5 3 3 0 2 4 5 98 618 1
cert_coverFacet 4 226
cert_cover_2 4 4 0 5 6 98 226 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 668
cert_cover_5 6 0 1 2 3 6 652 668 2
cert_coverFacet 7 716
cert_cover_5 7 0 1 2 5 6 652 716 2
cert_coverFacet 8 212
cert_cover_2 8 3 1 5 6 84 212 3
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0148

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0149.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0149

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 213, 837, 793, 689, 337, 782, 230, 358, 570, 298, 674, 184, 216, 344, 488, 69, 133, 517, 81, 145, 273, 529, 321, 641, 769, 102, 134, 262, 518, 42, 266, 522, 162, 290, 546, 642, 196, 324, 772, 56, 88, 152, 280, 536, 168, 296, 200, 328, 776, 176, 560, 208, 336, 224, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_213, vertices_837, vertices_793, vertices_689, vertices_337, vertices_782, vertices_230, vertices_358, vertices_570, vertices_298, vertices_674, vertices_184, vertices_216, vertices_344, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_81, vertices_145, vertices_273, vertices_529, vertices_321, vertices_641, vertices_769, vertices_102, vertices_134, vertices_262, vertices_518, vertices_42, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_642, vertices_196, vertices_324, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_200, vertices_328, vertices_776, vertices_176, vertices_560, vertices_208, vertices_336, vertices_224, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_213), (false, vertices_837), (false, vertices_793), (false, vertices_689), (false, vertices_337), (true, vertices_102), (true, vertices_262), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_168), (true, vertices_296), (true, vertices_200), (true, vertices_328), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 18 else
  if p.val = (false, vertices_213) then 21 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (false, vertices_793) then 24 else
  if p.val = (false, vertices_689) then 26 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (true, vertices_102) then 19 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_328) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_352) then 16 else
  0
cert_priority
cert_nodeAtPriority_14 337 262 42 266 522 162 290 546 56 88 152 168 296 200 328 224 352 647 102 213 837 793 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 42 2
cert_row_4 1 0 1 2 7 8 782 262 2
cert_row_2 2 0 1 4 5 102
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 3 8 0 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 262 782 2
cert_coverFacet 1 230
cert_cover_5 1 2 0 1 4 6 102 230 3
cert_coverFacet 2 358
cert_cover_5 2 2 0 1 4 7 102 358 3
cert_coverFacet 3 570
cert_cover_5 3 0 0 2 3 4 42 570 2
cert_coverFacet 4 298
cert_cover_2 4 2 0 4 7 42 298 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coverFacet 9 488
cert_cover_5 9 3 2 4 5 6 168 488 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0149

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0150.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0150

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 109, 589, 789, 421, 369, 398, 794, 650, 242, 402, 706, 172, 780, 744, 432, 77, 37, 261, 517, 81, 273, 529, 97, 289, 577, 138, 266, 522, 82, 146, 274, 530, 194, 578, 386, 642, 44, 140, 268, 524, 164, 388, 772, 104, 168, 584, 648, 776, 112, 176, 304, 400, 784, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_109, vertices_589, vertices_789, vertices_421, vertices_369, vertices_398, vertices_794, vertices_650, vertices_242, vertices_402, vertices_706, vertices_172, vertices_780, vertices_744, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_77, vertices_37, vertices_261, vertices_517, vertices_81, vertices_273, vertices_529, vertices_97, vertices_289, vertices_577, vertices_138, vertices_266, vertices_522, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_578, vertices_386, vertices_642, vertices_44, vertices_140, vertices_268, vertices_524, vertices_164, vertices_388, vertices_772, vertices_104, vertices_168, vertices_584, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_400, vertices_784, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_109), (false, vertices_589), (false, vertices_789), (false, vertices_421), (false, vertices_369), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_140), (true, vertices_268), (true, vertices_168), (true, vertices_648), (true, vertices_776), (true, vertices_176), (true, vertices_400), (true, vertices_224), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 22 19 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 18 else
  if p.val = (false, vertices_109) then 20 else
  if p.val = (false, vertices_589) then 21 else
  if p.val = (false, vertices_789) then 23 else
  if p.val = (false, vertices_421) then 24 else
  if p.val = (false, vertices_369) then 26 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 138 1
cert_row_4 1 0 2 3 7 8 794 266 2
cert_row_4 2 0 3 4 5 6 242 82 2
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 138 398 1
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 266 794 2
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 82 242 2
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 172
cert_cover_2 6 2 1 4 6 44 172 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 744
cert_cover_5 8 3 2 4 5 6 104 744 3
cert_coverFacet 9 432
cert_cover_2 9 4 3 6 7 176 432 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0150

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0151.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0151

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 597, 405, 325, 665, 737, 838, 410, 234, 298, 610, 802, 316, 572, 804, 680, 21, 69, 261, 145, 529, 193, 321, 577, 385, 641, 42, 138, 266, 98, 290, 546, 194, 322, 578, 386, 770, 60, 276, 532, 292, 548, 324, 580, 772, 152, 280, 536, 168, 296, 552, 648, 400, 224, 608, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_597, vertices_405, vertices_325, vertices_665, vertices_737, vertices_838, vertices_410, vertices_234, vertices_298, vertices_610, vertices_802, vertices_316, vertices_572, vertices_804, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_261, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_42, vertices_138, vertices_266, vertices_98, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_60, vertices_276, vertices_532, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_648, vertices_400, vertices_224, vertices_608, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_597), (false, vertices_405), (false, vertices_325), (false, vertices_665), (false, vertices_737), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_578), (true, vertices_770), (true, vertices_60), (true, vertices_292), (true, vertices_548), (true, vertices_772), (true, vertices_280), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 22 19 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 18 else
  if p.val = (false, vertices_597) then 23 else
  if p.val = (false, vertices_405) then 24 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_60) then 21 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_296) then 14 else
  if p.val = (true, vertices_552) then 15 else
  if p.val = (true, vertices_800) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
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
cert_row_4 0 0 1 5 7 8 838 322 1
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 2 3 6 7 410 138 2
cert_row_4 3 0 2 4 5 6 234 42 3
cert_rows
cert_pivot_2 8 1 3 0
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 0 0 1 5 7 322 838 1
cert_coverFacet 1 410
cert_cover_5 1 2 0 2 3 6 138 410 2
cert_coverFacet 2 234
cert_cover_5 2 3 0 2 4 5 42 234 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 610
cert_cover_2 4 4 0 5 8 98 610 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 316
cert_cover_5 6 1 1 2 3 7 60 316 3
cert_coverFacet 7 572
cert_cover_5 7 1 1 2 3 8 60 572 3
cert_coverFacet 8 804
cert_cover_2 8 4 1 7 8 292 804 3
cert_coverFacet 9 680
cert_cover_2 9 4 2 6 8 168 680 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0151

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0152.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0152

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 93, 285, 805, 709, 625, 654, 810, 394, 178, 402, 738, 204, 780, 472, 240, 29, 69, 261, 517, 49, 81, 273, 289, 545, 577, 138, 266, 522, 50, 146, 274, 162, 290, 546, 386, 642, 76, 140, 268, 524, 196, 644, 772, 88, 280, 200, 392, 776, 112, 176, 208, 400, 224, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_93, vertices_285, vertices_805, vertices_709, vertices_625, vertices_654, vertices_810, vertices_394, vertices_178, vertices_402, vertices_738, vertices_204, vertices_780, vertices_472, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_69, vertices_261, vertices_517, vertices_49, vertices_81, vertices_273, vertices_289, vertices_545, vertices_577, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_76, vertices_140, vertices_268, vertices_524, vertices_196, vertices_644, vertices_772, vertices_88, vertices_280, vertices_200, vertices_392, vertices_776, vertices_112, vertices_176, vertices_208, vertices_400, vertices_224, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_93), (false, vertices_285), (false, vertices_805), (false, vertices_709), (false, vertices_625), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_162), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_140), (true, vertices_524), (true, vertices_200), (true, vertices_392), (true, vertices_776), (true, vertices_176), (true, vertices_208), (true, vertices_400), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 22 19 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 18 else
  if p.val = (false, vertices_93) then 20 else
  if p.val = (false, vertices_285) then 21 else
  if p.val = (false, vertices_805) then 23 else
  if p.val = (false, vertices_709) then 24 else
  if p.val = (false, vertices_625) then 26 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_224) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
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
cert_row_4 1 2 3 5 6 7 472 88 3
cert_row_4 2 0 2 4 7 8 810 266 2
cert_row_4 3 0 4 5 6 8 738 162 2
cert_rows
cert_pivot_2 1 3 2 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 810
cert_cover_5 1 2 0 2 4 7 266 810 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 738
cert_cover_5 5 3 0 4 5 6 162 738 2
cert_coverFacet 6 204
cert_cover_2 6 2 1 5 6 76 204 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 472
cert_cover_5 8 1 2 3 5 6 88 472 3
cert_coverFacet 9 240
cert_cover_2 9 4 3 5 6 112 240 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0152

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0153.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0153

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 341, 709, 601, 433, 657, 654, 358, 614, 186, 554, 418, 312, 344, 664, 872, 69, 133, 261, 81, 145, 273, 529, 577, 385, 641, 102, 134, 262, 518, 42, 138, 522, 162, 290, 546, 386, 324, 580, 644, 56, 88, 152, 280, 536, 296, 552, 328, 584, 648, 176, 304, 336, 656, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_341, vertices_709, vertices_601, vertices_433, vertices_657, vertices_654, vertices_358, vertices_614, vertices_186, vertices_554, vertices_418, vertices_312, vertices_344, vertices_664, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_81, vertices_145, vertices_273, vertices_529, vertices_577, vertices_385, vertices_641, vertices_102, vertices_134, vertices_262, vertices_518, vertices_42, vertices_138, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_324, vertices_580, vertices_644, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_296, vertices_552, vertices_328, vertices_584, vertices_648, vertices_176, vertices_304, vertices_336, vertices_656, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_341), (false, vertices_709), (false, vertices_601), (false, vertices_433), (false, vertices_657), (true, vertices_102), (true, vertices_518), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_648), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 18 else
  if p.val = (false, vertices_341) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_601) then 24 else
  if p.val = (false, vertices_433) then 26 else
  if p.val = (false, vertices_657) then 0 else
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
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_352) then 15 else
  if p.val = (true, vertices_608) then 16 else
  0
cert_priority
cert_nodeAtPriority_14 657 518 42 138 522 162 290 546 56 152 280 296 552 328 648 352 608 391 102 341 709 601 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 6 186 42 2
cert_row_4 1 0 1 2 6 8 654 134 2
cert_row_2 2 0 1 4 5 102
cert_row_4 3 2 4 5 7 8 872 296 2
cert_rows
cert_pivot_2 3 6 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 134 654 2
cert_coverFacet 1 358
cert_cover_5 1 2 0 1 4 7 102 358 3
cert_coverFacet 2 614
cert_cover_5 2 2 0 1 4 8 102 614 3
cert_coverFacet 3 186
cert_cover_5 3 0 0 2 3 4 42 186 2
cert_coverFacet 4 554
cert_cover_2 4 2 0 4 8 42 554 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coverFacet 9 872
cert_cover_5 9 3 2 4 5 7 296 872 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0153

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0154.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0154

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 93, 285, 229, 465, 929, 590, 270, 550, 666, 282, 818, 612, 216, 744, 912, 29, 37, 69, 261, 81, 273, 161, 289, 193, 385, 14, 38, 262, 518, 26, 266, 522, 274, 530, 290, 546, 76, 268, 100, 548, 580, 88, 152, 280, 200, 584, 648, 208, 400, 656, 784, 224, 608, 672, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_93, vertices_285, vertices_229, vertices_465, vertices_929, vertices_590, vertices_270, vertices_550, vertices_666, vertices_282, vertices_818, vertices_612, vertices_216, vertices_744, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_37, vertices_69, vertices_261, vertices_81, vertices_273, vertices_161, vertices_289, vertices_193, vertices_385, vertices_14, vertices_38, vertices_262, vertices_518, vertices_26, vertices_266, vertices_522, vertices_274, vertices_530, vertices_290, vertices_546, vertices_76, vertices_268, vertices_100, vertices_548, vertices_580, vertices_88, vertices_152, vertices_280, vertices_200, vertices_584, vertices_648, vertices_208, vertices_400, vertices_656, vertices_784, vertices_224, vertices_608, vertices_672, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_93), (false, vertices_285), (false, vertices_229), (false, vertices_465), (false, vertices_929), (true, vertices_14), (true, vertices_518), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_548), (true, vertices_580), (true, vertices_152), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_656), (true, vertices_784), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 18 else
  if p.val = (false, vertices_93) then 20 else
  if p.val = (false, vertices_285) then 21 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (false, vertices_929) then 27 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_784) then 15 else
  if p.val = (true, vertices_608) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 0 3 4 7 8 818 274 2
cert_row_4 2 0 2 3 6 8 666 26 3
cert_row_4 3 2 4 5 6 8 744 200 1
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 666
cert_cover_5 3 2 0 2 3 6 26 666 3
cert_coverFacet 4 282
cert_cover_2 4 2 0 3 7 26 282 3
cert_coverFacet 5 818
cert_cover_5 5 1 0 3 4 7 274 818 2
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 744
cert_cover_5 8 3 2 4 5 6 200 744 1
cert_coverFacet 9 912
cert_cover_2 9 6 3 7 8 400 912 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0154

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0155.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0155

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 535, 395, 675, 817, 481, 270, 526, 714, 124, 284, 588, 564, 740, 472, 368, 23, 131, 259, 515, 273, 529, 161, 289, 545, 385, 14, 262, 518, 138, 266, 522, 642, 28, 76, 268, 524, 52, 276, 532, 100, 548, 580, 88, 280, 200, 584, 392, 112, 304, 560, 336, 224, 352, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_535, vertices_395, vertices_675, vertices_817, vertices_481, vertices_270, vertices_526, vertices_714, vertices_124, vertices_284, vertices_588, vertices_564, vertices_740, vertices_472, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_131, vertices_259, vertices_515, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_385, vertices_14, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_642, vertices_28, vertices_76, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_100, vertices_548, vertices_580, vertices_88, vertices_280, vertices_200, vertices_584, vertices_392, vertices_112, vertices_304, vertices_560, vertices_336, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_535), (false, vertices_395), (false, vertices_675), (false, vertices_817), (false, vertices_481), (true, vertices_14), (true, vertices_522), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_100), (true, vertices_548), (true, vertices_580), (true, vertices_88), (true, vertices_280), (true, vertices_200), (true, vertices_584), (true, vertices_112), (true, vertices_336), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 20 17 23 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 18 else
  if p.val = (false, vertices_535) then 19 else
  if p.val = (false, vertices_395) then 21 else
  if p.val = (false, vertices_675) then 22 else
  if p.val = (false, vertices_817) then 25 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_112) then 14 else
  if p.val = (true, vertices_336) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 20 => Sum.inl 0
  | 21 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 23 => Sum.inl 2
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
cert_row_4 0 0 2 5 6 8 714 138 2
cert_row_4 1 1 4 5 6 8 740 100 3
cert_row_4 2 1 2 3 4 5 124 28 3
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 714
cert_cover_5 2 0 0 2 5 6 138 714 2
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 4 28 124 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 588
cert_cover_2 5 2 1 5 8 76 588 3
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 740
cert_cover_5 7 1 1 4 5 6 100 740 3
cert_coverFacet 8 472
cert_cover_5 8 3 2 3 5 6 88 472 3
cert_coverFacet 9 368
cert_cover_2 9 4 3 5 7 112 368 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0155

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0156.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0156

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 283, 539, 611, 849, 481, 654, 270, 550, 220, 284, 436, 676, 600, 744, 464, 27, 35, 259, 515, 273, 529, 97, 289, 321, 577, 14, 38, 262, 518, 266, 522, 546, 28, 140, 268, 148, 276, 164, 292, 548, 644, 88, 280, 536, 200, 584, 648, 208, 336, 592, 400, 224, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_283, vertices_539, vertices_611, vertices_849, vertices_481, vertices_654, vertices_270, vertices_550, vertices_220, vertices_284, vertices_436, vertices_676, vertices_600, vertices_744, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_35, vertices_259, vertices_515, vertices_273, vertices_529, vertices_97, vertices_289, vertices_321, vertices_577, vertices_14, vertices_38, vertices_262, vertices_518, vertices_266, vertices_522, vertices_546, vertices_28, vertices_140, vertices_268, vertices_148, vertices_276, vertices_164, vertices_292, vertices_548, vertices_644, vertices_88, vertices_280, vertices_536, vertices_200, vertices_584, vertices_648, vertices_208, vertices_336, vertices_592, vertices_400, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_283), (false, vertices_539), (false, vertices_611), (false, vertices_849), (false, vertices_481), (true, vertices_14), (true, vertices_518), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_164), (true, vertices_548), (true, vertices_644), (true, vertices_88), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_208), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 17 23 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 18 else
  if p.val = (false, vertices_283) then 20 else
  if p.val = (false, vertices_539) then 21 else
  if p.val = (false, vertices_611) then 22 else
  if p.val = (false, vertices_849) then 25 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_672) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 1 3 4 6 7 436 148 2
cert_row_4 2 1 2 3 5 6 220 28 3
cert_row_4 3 2 4 5 6 8 744 200 1
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 220
cert_cover_5 3 2 1 2 3 5 28 220 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 436
cert_cover_5 5 1 1 3 4 6 148 436 2
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coverFacet 8 744
cert_cover_5 8 3 2 4 5 6 200 744 1
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0156

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0157.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0157

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 93, 285, 233, 369, 929, 270, 526, 566, 278, 714, 914, 588, 116, 740, 816, 29, 73, 137, 265, 81, 273, 97, 161, 289, 385, 14, 22, 262, 518, 138, 266, 522, 274, 530, 386, 642, 76, 268, 524, 52, 84, 276, 100, 548, 580, 200, 584, 112, 304, 560, 784, 224, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_93, vertices_285, vertices_233, vertices_369, vertices_929, vertices_270, vertices_526, vertices_566, vertices_278, vertices_714, vertices_914, vertices_588, vertices_116, vertices_740, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_73, vertices_137, vertices_265, vertices_81, vertices_273, vertices_97, vertices_161, vertices_289, vertices_385, vertices_14, vertices_22, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_386, vertices_642, vertices_76, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_100, vertices_548, vertices_580, vertices_200, vertices_584, vertices_112, vertices_304, vertices_560, vertices_784, vertices_224, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_93), (false, vertices_285), (false, vertices_233), (false, vertices_369), (false, vertices_929), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_642), (true, vertices_524), (true, vertices_52), (true, vertices_100), (true, vertices_548), (true, vertices_580), (true, vertices_584), (true, vertices_560), (true, vertices_784), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_93) then 20 else
  if p.val = (false, vertices_285) then 21 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (false, vertices_929) then 27 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_580) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_784) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 138 2
cert_row_4 1 0 3 6 7 8 914 274 2
cert_row_4 2 0 1 3 4 8 566 22 3
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 566
cert_cover_5 2 2 0 1 3 4 22 566 3
cert_coverFacet 3 278
cert_cover_2 3 1 0 3 7 22 278 3
cert_coverFacet 4 714
cert_cover_5 4 0 0 2 5 6 138 714 2
cert_coverFacet 5 914
cert_cover_5 5 1 0 3 6 7 274 914 2
cert_coverFacet 6 588
cert_cover_2 6 2 1 5 8 76 588 3
cert_coverFacet 7 116
cert_cover_2 7 3 1 4 5 52 116 3
cert_coverFacet 8 740
cert_cover_5 8 3 1 4 5 6 100 740 3
cert_coverFacet 9 816
cert_cover_2 9 4 3 7 8 304 816 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0157

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0158.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0158

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 333, 233, 777, 689, 865, 94, 270, 662, 806, 218, 778, 308, 564, 340, 496, 73, 137, 265, 521, 97, 161, 545, 321, 641, 769, 14, 22, 262, 518, 90, 138, 266, 522, 146, 642, 770, 76, 268, 52, 84, 276, 532, 292, 548, 324, 200, 776, 176, 304, 560, 208, 336, 656, 224, 352, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_333, vertices_233, vertices_777, vertices_689, vertices_865, vertices_94, vertices_270, vertices_662, vertices_806, vertices_218, vertices_778, vertices_308, vertices_564, vertices_340, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_321, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_518, vertices_90, vertices_138, vertices_266, vertices_522, vertices_146, vertices_642, vertices_770, vertices_76, vertices_268, vertices_52, vertices_84, vertices_276, vertices_532, vertices_292, vertices_548, vertices_324, vertices_200, vertices_776, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_656, vertices_224, vertices_352, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_333), (false, vertices_233), (false, vertices_777), (false, vertices_689), (false, vertices_865), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_90), (true, vertices_266), (true, vertices_146), (true, vertices_770), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_548), (true, vertices_304), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_333) then 21 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_689) then 25 else
  if p.val = (false, vertices_865) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_90) then 19 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_292) then 12 else
  if p.val = (true, vertices_548) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_336) then 16 else
  0
cert_priority
cert_nodeAtPriority_66 777 14 22 262 518 266 146 770 52 84 276 532 292 548 304 208 336 651 90 333 233 689 865
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 3 4 5 6 7 496 176 2
cert_row_4 2 0 1 3 6 8 662 22 3
cert_row_4 3 0 1 4 7 8 806 262 2
cert_rows
cert_pivot_2 2 5 3 0
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 14 94 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 662
cert_cover_5 2 2 0 1 3 6 22 662 3
cert_coverFacet 3 806
cert_cover_5 3 3 0 1 4 7 262 806 2
cert_coverFacet 4 218
cert_cover_5 4 0 0 2 3 6 90 218 3
cert_coverFacet 5 778
cert_cover_2 5 2 0 7 8 266 778 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 564
cert_cover_2 7 3 1 4 8 52 564 3
cert_coverFacet 8 340
cert_cover_2 8 3 1 5 7 84 340 3
cert_coverFacet 9 496
cert_cover_5 9 1 3 4 5 6 176 496 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0158

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0159.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0159

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 43, 587, 419, 105, 241, 961, 286, 526, 314, 124, 716, 212, 660, 788, 944, 11, 35, 259, 515, 41, 73, 97, 161, 193, 577, 385, 769, 14, 262, 518, 282, 42, 522, 290, 28, 76, 524, 84, 148, 276, 532, 196, 644, 772, 56, 104, 584, 112, 176, 304, 208, 656, 784, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_43, vertices_587, vertices_419, vertices_105, vertices_241, vertices_961, vertices_286, vertices_526, vertices_314, vertices_124, vertices_716, vertices_212, vertices_660, vertices_788, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_515, vertices_41, vertices_73, vertices_97, vertices_161, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_262, vertices_518, vertices_282, vertices_42, vertices_522, vertices_290, vertices_28, vertices_76, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_644, vertices_772, vertices_56, vertices_104, vertices_584, vertices_112, vertices_176, vertices_304, vertices_208, vertices_656, vertices_784, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_43), (false, vertices_587), (false, vertices_419), (false, vertices_105), (false, vertices_241), (false, vertices_961), (true, vertices_14), (true, vertices_282), (true, vertices_28), (true, vertices_76), (true, vertices_524), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_196), (true, vertices_644), (true, vertices_56), (true, vertices_304), (true, vertices_656), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 16 22 23 25 26 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_43) then 0 else
  if p.val = (false, vertices_587) then 19 else
  if p.val = (false, vertices_419) then 20 else
  if p.val = (false, vertices_105) then 1 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (false, vertices_961) then 27 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_282) then 21 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_43), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_105), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_282), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 7 282
cert_row_4 1 3 4 6 7 8 944 176 3
cert_row_4 2 1 2 3 4 5 124 28 3
cert_row_4 3 1 2 5 6 8 716 76 3
cert_rows
cert_pivot_2 0 7 3 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 14 286 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 314
cert_cover_5 2 0 0 2 3 4 282 314 3
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 4 28 124 3
cert_coverFacet 4 716
cert_cover_5 4 3 1 2 5 6 76 716 3
cert_coverFacet 5 212
cert_cover_2 5 3 1 5 6 84 212 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 944
cert_cover_5 8 1 3 4 6 7 176 944 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0159

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0160.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0160

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 283, 51, 675, 453, 645, 185, 393, 626, 786, 604, 796, 332, 740, 120, 488, 19, 35, 259, 515, 133, 261, 517, 25, 137, 265, 49, 161, 385, 641, 50, 274, 530, 546, 770, 540, 76, 268, 196, 324, 580, 644, 772, 56, 88, 280, 104, 168, 328, 392, 112, 592, 784, 224, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_283, vertices_51, vertices_675, vertices_453, vertices_645, vertices_185, vertices_393, vertices_626, vertices_786, vertices_604, vertices_796, vertices_332, vertices_740, vertices_120, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_515, vertices_133, vertices_261, vertices_517, vertices_25, vertices_137, vertices_265, vertices_49, vertices_161, vertices_385, vertices_641, vertices_50, vertices_274, vertices_530, vertices_546, vertices_770, vertices_540, vertices_76, vertices_268, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_104, vertices_168, vertices_328, vertices_392, vertices_112, vertices_592, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_283), (false, vertices_51), (false, vertices_675), (false, vertices_453), (false, vertices_645), (false, vertices_185), (false, vertices_393), (true, vertices_530), (true, vertices_540), (true, vertices_76), (true, vertices_268), (true, vertices_580), (true, vertices_88), (true, vertices_104), (true, vertices_328), (true, vertices_112), (true, vertices_592), (true, vertices_784), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_283) then 17 else
  if p.val = (false, vertices_51) then 0 else
  if p.val = (false, vertices_675) then 18 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_645) then 1 else
  if p.val = (false, vertices_185) then 23 else
  if p.val = (false, vertices_393) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_540) then 21 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_645), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_540), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 8 626 50 3
cert_row_2 1 1 2 3 8 540
cert_row_4 2 1 4 5 6 8 740 196 1
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 626
cert_cover_5 0 0 0 3 4 5 50 626 3
cert_coverFacet 1 786
cert_cover_2 1 3 0 7 8 274 786 3
cert_coverFacet 2 604
cert_cover_5 2 1 1 2 3 5 540 604 3
cert_coverFacet 3 796
cert_cover_5 3 1 1 2 3 7 540 796 3
cert_coverFacet 4 332
cert_cover_2 4 2 1 5 7 76 332 3
cert_coverFacet 5 740
cert_cover_5 5 2 1 4 5 6 196 740 1
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0160

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0161.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0161

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 147, 611, 643, 709, 361, 465, 662, 810, 786, 412, 796, 236, 556, 612, 456, 19, 35, 131, 515, 145, 273, 97, 289, 193, 321, 577, 641, 146, 274, 530, 290, 546, 642, 770, 284, 44, 140, 524, 148, 532, 100, 548, 196, 580, 644, 104, 296, 552, 200, 328, 392, 776, 400, 784, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_147, vertices_611, vertices_643, vertices_709, vertices_361, vertices_465, vertices_662, vertices_810, vertices_786, vertices_412, vertices_796, vertices_236, vertices_556, vertices_612, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_515, vertices_145, vertices_273, vertices_97, vertices_289, vertices_193, vertices_321, vertices_577, vertices_641, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_642, vertices_770, vertices_284, vertices_44, vertices_140, vertices_524, vertices_148, vertices_532, vertices_100, vertices_548, vertices_196, vertices_580, vertices_644, vertices_104, vertices_296, vertices_552, vertices_200, vertices_328, vertices_392, vertices_776, vertices_400, vertices_784, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_147), (false, vertices_611), (false, vertices_643), (false, vertices_709), (false, vertices_361), (false, vertices_465), (true, vertices_530), (true, vertices_770), (true, vertices_284), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_148), (true, vertices_532), (true, vertices_100), (true, vertices_548), (true, vertices_552), (true, vertices_200), (true, vertices_392), (true, vertices_776), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 17 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_611) then 18 else
  if p.val = (false, vertices_643) then 1 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_284) then 21 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_776) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
cert_nodeAtPriority_61 0 147 1 643 530 770 44 140 524 148 532 100 548 552 200 392 776 784 307 611 709 284 361 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 5 6 236 44 3
cert_row_4 1 0 1 3 6 8 662 146 1
cert_row_2 2 1 2 3 7 284
cert_row_4 3 0 2 4 7 8 810 290 1
cert_rows
cert_pivot_2 5 6 1 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 146 662 1
cert_coverFacet 1 810
cert_cover_5 1 3 0 2 4 7 290 810 1
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 412
cert_cover_5 3 2 1 2 3 6 284 412 3
cert_coverFacet 4 796
cert_cover_5 4 2 1 2 3 8 284 796 3
cert_coverFacet 5 236
cert_cover_5 5 0 1 2 4 5 44 236 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 612
cert_cover_2 7 4 1 5 8 100 612 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0161

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0162.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0162

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 285, 301, 181, 233, 585, 721, 790, 282, 618, 298, 354, 962, 660, 484, 900, 269, 21, 37, 25, 41, 73, 521, 145, 529, 161, 193, 577, 26, 42, 266, 522, 274, 530, 98, 290, 322, 578, 770, 148, 276, 532, 164, 292, 388, 644, 772, 280, 104, 296, 584, 656, 224, 352, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_285, vertices_301, vertices_181, vertices_233, vertices_585, vertices_721, vertices_790, vertices_282, vertices_618, vertices_298, vertices_354, vertices_962, vertices_660, vertices_484, vertices_900] (by decide +kernel)
  polygons := literalFinset [vertices_269, vertices_21, vertices_37, vertices_25, vertices_41, vertices_73, vertices_521, vertices_145, vertices_529, vertices_161, vertices_193, vertices_577, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_530, vertices_98, vertices_290, vertices_322, vertices_578, vertices_770, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_388, vertices_644, vertices_772, vertices_280, vertices_104, vertices_296, vertices_584, vertices_656, vertices_224, vertices_352, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_285), (false, vertices_301), (false, vertices_181), (false, vertices_233), (false, vertices_585), (false, vertices_721), (true, vertices_42), (true, vertices_266), (true, vertices_274), (true, vertices_98), (true, vertices_290), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_532), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_352), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 17 else
  if p.val = (false, vertices_285) then 19 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_181) then 21 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_448) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_4 1 0 2 4 5 8 618 42 3
cert_row_4 2 0 5 6 7 8 962 322 2
cert_row_4 3 1 4 5 6 7 484 164 2
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 618
cert_cover_5 2 1 0 2 4 5 42 618 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 354
cert_cover_2 4 4 0 5 7 98 354 3
cert_coverFacet 5 962
cert_cover_5 5 2 0 5 6 7 322 962 2
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 164 484 2
cert_coverFacet 8 900
cert_cover_2 8 6 1 7 8 388 900 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0162

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_4023 : Certifies 4023 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0133.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4024 : Certifies 4024 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0134.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4025 : Certifies 4025 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0135.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4026 : Certifies 4026 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0136.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4027 : Certifies 4027 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0137.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4028 : Certifies 4028 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0138.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4029 : Certifies 4029 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0139.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4030 : Certifies 4030 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0140.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4031 : Certifies 4031 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0141.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4032 : Certifies 4032 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0142.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4033 : Certifies 4033 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0143.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4034 : Certifies 4034 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0144.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4035 : Certifies 4035 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0145.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4036 : Certifies 4036 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0146.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4037 : Certifies 4037 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0147.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4038 : Certifies 4038 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0148.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4039 : Certifies 4039 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0149.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4040 : Certifies 4040 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0150.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4041 : Certifies 4041 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0151.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4042 : Certifies 4042 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0152.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4043 : Certifies 4043 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0153.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4044 : Certifies 4044 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0154.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4045 : Certifies 4045 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0155.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4046 : Certifies 4046 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0156.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4047 : Certifies 4047 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0157.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4048 : Certifies 4048 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0158.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4049 : Certifies 4049 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0159.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4050 : Certifies 4050 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0160.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4051 : Certifies 4051 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0161.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4052 : Certifies 4052 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0162.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B133 (j : Fin 30) :
    Certifies (4023 + j.val) := by
  fin_cases j
  · exact projection_4023
  · exact projection_4024
  · exact projection_4025
  · exact projection_4026
  · exact projection_4027
  · exact projection_4028
  · exact projection_4029
  · exact projection_4030
  · exact projection_4031
  · exact projection_4032
  · exact projection_4033
  · exact projection_4034
  · exact projection_4035
  · exact projection_4036
  · exact projection_4037
  · exact projection_4038
  · exact projection_4039
  · exact projection_4040
  · exact projection_4041
  · exact projection_4042
  · exact projection_4043
  · exact projection_4044
  · exact projection_4045
  · exact projection_4046
  · exact projection_4047
  · exact projection_4048
  · exact projection_4049
  · exact projection_4050
  · exact projection_4051
  · exact projection_4052

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
