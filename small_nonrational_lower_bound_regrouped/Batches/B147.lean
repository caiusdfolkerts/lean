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
/- Source: ProjectionCertificates/R_m16e10q1_0559.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0559

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 781, 181, 277, 425, 649, 369, 214, 342, 774, 714, 866, 632, 184, 216, 808, 21, 133, 261, 517, 137, 265, 521, 49, 273, 161, 289, 641, 86, 134, 262, 518, 194, 322, 578, 642, 770, 148, 276, 772, 56, 88, 152, 168, 296, 552, 200, 584, 648, 776, 112, 176, 208, 336, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_781, vertices_181, vertices_277, vertices_425, vertices_649, vertices_369, vertices_214, vertices_342, vertices_774, vertices_714, vertices_866, vertices_632, vertices_184, vertices_216, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_49, vertices_273, vertices_161, vertices_289, vertices_641, vertices_86, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_148, vertices_276, vertices_772, vertices_56, vertices_88, vertices_152, vertices_168, vertices_296, vertices_552, vertices_200, vertices_584, vertices_648, vertices_776, vertices_112, vertices_176, vertices_208, vertices_336, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_781), (false, vertices_181), (false, vertices_277), (false, vertices_425), (false, vertices_649), (false, vertices_369), (true, vertices_86), (true, vertices_262), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_552), (true, vertices_200), (true, vertices_584), (true, vertices_208), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 17 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_181) then 21 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_425) then 23 else
  if p.val = (false, vertices_649) then 1 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (true, vertices_86) then 18 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_608) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
cert_nodeAtPriority_50 1 277 0 649 262 194 322 578 770 56 88 152 552 200 584 208 608 800 647 86 781 181 425 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 2 5 6 8 714 194 1
cert_row_4 2 0 4 5 7 8 866 322 1
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 6 86 214 3
cert_coverFacet 1 342
cert_cover_5 1 0 0 1 3 7 86 342 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 714
cert_cover_5 3 1 0 2 5 6 194 714 1
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 322 866 1
cert_coverFacet 5 632
cert_cover_5 5 3 2 3 4 5 56 632 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0559

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0560.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0560

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 563, 707, 613, 57, 361, 201, 902, 402, 786, 572, 796, 300, 484, 708, 472, 19, 131, 515, 25, 41, 73, 137, 49, 97, 545, 193, 577, 146, 274, 530, 386, 642, 770, 540, 44, 268, 100, 292, 548, 196, 580, 388, 644, 772, 56, 152, 280, 296, 200, 328, 560, 400, 784, 352, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_563, vertices_707, vertices_613, vertices_57, vertices_361, vertices_201, vertices_902, vertices_402, vertices_786, vertices_572, vertices_796, vertices_300, vertices_484, vertices_708, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_515, vertices_25, vertices_41, vertices_73, vertices_137, vertices_49, vertices_97, vertices_545, vertices_193, vertices_577, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_540, vertices_44, vertices_268, vertices_100, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_152, vertices_280, vertices_296, vertices_200, vertices_328, vertices_560, vertices_400, vertices_784, vertices_352, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_563), (false, vertices_707), (false, vertices_613), (false, vertices_57), (false, vertices_361), (false, vertices_201), (true, vertices_274), (true, vertices_386), (true, vertices_770), (true, vertices_540), (true, vertices_44), (true, vertices_268), (true, vertices_292), (true, vertices_196), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_280), (true, vertices_400), (true, vertices_784), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 17 else
  if p.val = (false, vertices_563) then 18 else
  if p.val = (false, vertices_707) then 19 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_361) then 24 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_540) then 22 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
cert_nodeAtPriority_60 57 201 274 386 770 44 268 292 196 388 644 772 280 400 784 448 155 563 707 613 540 361
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_2 1 1 2 3 8 540
cert_row_4 2 1 4 5 6 7 484 100 3
cert_row_4 3 2 3 5 6 7 472 152 2
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 402
cert_cover_2 1 3 0 6 7 146 402 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 572
cert_cover_5 3 1 1 2 3 4 540 572 3
cert_coverFacet 4 796
cert_cover_5 4 1 1 2 3 7 540 796 3
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 484
cert_cover_5 6 2 1 4 5 6 100 484 3
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coverFacet 8 472
cert_cover_5 8 3 2 3 5 6 152 472 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0560

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0561.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0561

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 147, 835, 643, 357, 665, 625, 422, 906, 178, 604, 236, 396, 780, 836, 248, 19, 131, 259, 515, 49, 145, 529, 97, 289, 321, 577, 641, 50, 146, 162, 290, 386, 642, 770, 76, 140, 268, 524, 100, 164, 292, 324, 580, 388, 772, 88, 152, 536, 232, 392, 648, 776, 112, 176, 592, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_147, vertices_835, vertices_643, vertices_357, vertices_665, vertices_625, vertices_422, vertices_906, vertices_178, vertices_604, vertices_236, vertices_396, vertices_780, vertices_836, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_49, vertices_145, vertices_529, vertices_97, vertices_289, vertices_321, vertices_577, vertices_641, vertices_50, vertices_146, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_268, vertices_524, vertices_100, vertices_164, vertices_292, vertices_324, vertices_580, vertices_388, vertices_772, vertices_88, vertices_152, vertices_536, vertices_232, vertices_392, vertices_648, vertices_776, vertices_112, vertices_176, vertices_592, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_147), (false, vertices_835), (false, vertices_643), (false, vertices_357), (false, vertices_665), (false, vertices_625), (true, vertices_162), (true, vertices_386), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_164), (true, vertices_580), (true, vertices_388), (true, vertices_772), (true, vertices_88), (true, vertices_232), (true, vertices_392), (true, vertices_776), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 17 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_643) then 1 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_625) then 25 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_232) then 23 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_776) then 14 else
  if p.val = (true, vertices_176) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 23 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 5 8 604 76 2
cert_row_2 1 2 4 5 6 232
cert_row_4 2 0 1 4 6 7 422 162 1
cert_row_4 3 0 2 6 7 8 906 386 1
cert_rows
cert_pivot_2 3 5 1 0
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 2 0 1 4 6 162 422 1
cert_coverFacet 1 906
cert_cover_5 1 3 0 2 6 7 386 906 1
cert_coverFacet 2 178
cert_cover_2 2 3 0 4 6 50 178 3
cert_coverFacet 3 604
cert_cover_5 3 0 1 2 3 5 76 604 2
cert_coverFacet 4 236
cert_cover_5 4 1 1 2 4 5 76 236 2
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 836
cert_cover_2 7 5 1 7 8 324 836 3
cert_coverFacet 8 248
cert_cover_5 8 1 2 3 4 5 88 248 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0561

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0562.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0562

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 213, 613, 901, 361, 457, 790, 154, 538, 618, 170, 434, 604, 404, 216, 424, 69, 133, 517, 329, 97, 289, 545, 193, 385, 769, 26, 42, 138, 522, 146, 274, 530, 162, 290, 546, 770, 84, 148, 276, 532, 580, 388, 772, 88, 152, 536, 104, 168, 296, 200, 584, 392, 208, 400, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_213, vertices_613, vertices_901, vertices_361, vertices_457, vertices_790, vertices_154, vertices_538, vertices_618, vertices_170, vertices_434, vertices_604, vertices_404, vertices_216, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_329, vertices_97, vertices_289, vertices_545, vertices_193, vertices_385, vertices_769, vertices_26, vertices_42, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_770, vertices_84, vertices_148, vertices_276, vertices_532, vertices_580, vertices_388, vertices_772, vertices_88, vertices_152, vertices_536, vertices_104, vertices_168, vertices_296, vertices_200, vertices_584, vertices_392, vertices_208, vertices_400, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_213), (false, vertices_613), (false, vertices_901), (false, vertices_361), (false, vertices_457), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_276), (true, vertices_532), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_168), (true, vertices_584), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_901) then 22 else
  if p.val = (false, vertices_361) then 24 else
  if p.val = (false, vertices_457) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_162) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_584) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 7 434 146 2
cert_row_4 1 0 1 3 7 8 790 274 1
cert_row_4 2 0 2 4 5 8 618 42 3
cert_row_4 3 1 2 3 5 8 604 84 1
cert_rows
cert_pivot_2 6 7 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 274 790 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 618
cert_cover_5 3 2 0 2 4 5 42 618 3
cert_coverFacet 4 170
cert_cover_2 4 2 0 4 6 42 170 3
cert_coverFacet 5 434
cert_cover_5 5 0 0 3 4 6 146 434 2
cert_coverFacet 6 604
cert_cover_5 6 3 1 2 3 5 84 604 1
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coverFacet 9 424
cert_cover_2 9 4 2 6 7 168 424 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0562

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0563.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0563

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 109, 653, 805, 185, 433, 710, 346, 818, 594, 450, 204, 628, 120, 408, 456, 13, 37, 517, 41, 137, 177, 289, 385, 641, 769, 82, 274, 530, 194, 322, 578, 386, 642, 770, 76, 140, 100, 548, 196, 580, 644, 56, 88, 152, 280, 104, 200, 328, 392, 112, 304, 560, 592, 400, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_109, vertices_653, vertices_805, vertices_185, vertices_433, vertices_710, vertices_346, vertices_818, vertices_594, vertices_450, vertices_204, vertices_628, vertices_120, vertices_408, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_517, vertices_41, vertices_137, vertices_177, vertices_289, vertices_385, vertices_641, vertices_769, vertices_82, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_100, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_88, vertices_152, vertices_280, vertices_104, vertices_200, vertices_328, vertices_392, vertices_112, vertices_304, vertices_560, vertices_592, vertices_400, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_109), (false, vertices_653), (false, vertices_805), (false, vertices_185), (false, vertices_433), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_196), (true, vertices_580), (true, vertices_88), (true, vertices_280), (true, vertices_200), (true, vertices_328), (true, vertices_392), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 24 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_109) then 20 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_805) then 22 else
  if p.val = (false, vertices_185) then 25 else
  if p.val = (false, vertices_433) then 26 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_592) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 8 710 194 1
cert_row_4 1 0 2 3 5 7 346 82 1
cert_row_4 2 0 3 4 7 8 818 274 2
cert_row_4 3 1 3 4 5 8 628 100 1
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 0 0 1 5 6 194 710 1
cert_coverFacet 1 346
cert_cover_5 1 1 0 2 3 5 82 346 1
cert_coverFacet 2 818
cert_cover_5 2 2 0 3 4 7 274 818 2
cert_coverFacet 3 594
cert_cover_2 3 3 0 5 8 82 594 3
cert_coverFacet 4 450
cert_cover_2 4 5 0 6 7 194 450 3
cert_coverFacet 5 204
cert_cover_2 5 2 1 5 6 76 204 3
cert_coverFacet 6 628
cert_cover_5 6 3 1 3 4 5 100 628 1
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 456
cert_cover_2 9 5 2 6 7 200 456 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0563

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0564.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0564

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 139, 707, 771, 805, 217, 617, 398, 662, 774, 412, 372, 564, 344, 360, 752, 11, 131, 259, 515, 41, 73, 137, 289, 545, 193, 577, 769, 134, 262, 518, 138, 266, 642, 770, 396, 52, 148, 276, 532, 292, 548, 772, 88, 152, 280, 104, 296, 328, 112, 560, 208, 336, 656, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_139, vertices_707, vertices_771, vertices_805, vertices_217, vertices_617, vertices_398, vertices_662, vertices_774, vertices_412, vertices_372, vertices_564, vertices_344, vertices_360, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_131, vertices_259, vertices_515, vertices_41, vertices_73, vertices_137, vertices_289, vertices_545, vertices_193, vertices_577, vertices_769, vertices_134, vertices_262, vertices_518, vertices_138, vertices_266, vertices_642, vertices_770, vertices_396, vertices_52, vertices_148, vertices_276, vertices_532, vertices_292, vertices_548, vertices_772, vertices_88, vertices_152, vertices_280, vertices_104, vertices_296, vertices_328, vertices_112, vertices_560, vertices_208, vertices_336, vertices_656, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_139), (false, vertices_707), (false, vertices_771), (false, vertices_805), (false, vertices_217), (false, vertices_617), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_396), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_280), (true, vertices_328), (true, vertices_112), (true, vertices_560), (true, vertices_336), (true, vertices_656), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 17 else
  if p.val = (false, vertices_139) then 0 else
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_217) then 23 else
  if p.val = (false, vertices_617) then 24 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_396) then 21 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_352) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 1 3 6 8 662 134 2
cert_row_4 2 1 3 4 5 7 372 52 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 662
cert_cover_5 1 1 0 1 3 6 134 662 2
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 412
cert_cover_5 3 0 1 2 3 6 396 412 2
cert_coverFacet 4 372
cert_cover_5 4 2 1 3 4 5 52 372 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 112 752 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0564

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0565.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0565

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 355, 899, 661, 101, 549, 453, 542, 314, 786, 156, 236, 556, 376, 216, 976, 35, 259, 515, 37, 69, 133, 517, 97, 545, 321, 385, 641, 26, 42, 522, 274, 530, 290, 770, 28, 44, 140, 524, 148, 532, 100, 548, 196, 312, 88, 152, 104, 552, 200, 208, 336, 656, 784, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_355, vertices_899, vertices_661, vertices_101, vertices_549, vertices_453, vertices_542, vertices_314, vertices_786, vertices_156, vertices_236, vertices_556, vertices_376, vertices_216, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_37, vertices_69, vertices_133, vertices_517, vertices_97, vertices_545, vertices_321, vertices_385, vertices_641, vertices_26, vertices_42, vertices_522, vertices_274, vertices_530, vertices_290, vertices_770, vertices_28, vertices_44, vertices_140, vertices_524, vertices_148, vertices_532, vertices_100, vertices_548, vertices_196, vertices_312, vertices_88, vertices_152, vertices_104, vertices_552, vertices_200, vertices_208, vertices_336, vertices_656, vertices_784, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_355), (false, vertices_899), (false, vertices_661), (false, vertices_101), (false, vertices_549), (false, vertices_453), (true, vertices_26), (true, vertices_274), (true, vertices_530), (true, vertices_28), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_312), (true, vertices_88), (true, vertices_152), (true, vertices_104), (true, vertices_200), (true, vertices_208), (true, vertices_336), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 17 else
  if p.val = (false, vertices_355) then 18 else
  if p.val = (false, vertices_899) then 19 else
  if p.val = (false, vertices_661) then 21 else
  if p.val = (false, vertices_101) then 0 else
  if p.val = (false, vertices_549) then 1 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_312) then 24 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_101), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_549), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(true, vertices_312), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 26 1
cert_row_4 1 1 2 4 5 6 236 44 3
cert_row_2 2 2 3 4 7 312
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 26 542 1
cert_coverFacet 1 314
cert_cover_5 1 2 0 2 3 4 26 314 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 156
cert_cover_2 3 2 1 3 6 28 156 3
cert_coverFacet 4 236
cert_cover_5 4 1 1 2 4 5 44 236 3
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 376
cert_cover_5 6 2 2 3 4 5 312 376 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 976
cert_cover_5 8 3 3 5 6 7 208 976 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0565

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0566.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0566

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 141, 565, 213, 681, 113, 481, 286, 534, 778, 370, 562, 930, 348, 204, 968, 13, 21, 133, 517, 137, 521, 49, 81, 97, 161, 545, 193, 14, 22, 518, 266, 522, 50, 274, 530, 290, 546, 770, 284, 76, 140, 84, 532, 196, 200, 328, 648, 776, 112, 560, 336, 352, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_141, vertices_565, vertices_213, vertices_681, vertices_113, vertices_481, vertices_286, vertices_534, vertices_778, vertices_370, vertices_562, vertices_930, vertices_348, vertices_204, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_133, vertices_517, vertices_137, vertices_521, vertices_49, vertices_81, vertices_97, vertices_161, vertices_545, vertices_193, vertices_14, vertices_22, vertices_518, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_284, vertices_76, vertices_140, vertices_84, vertices_532, vertices_196, vertices_200, vertices_328, vertices_648, vertices_776, vertices_112, vertices_560, vertices_336, vertices_352, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_141), (false, vertices_565), (false, vertices_213), (false, vertices_681), (false, vertices_113), (false, vertices_481), (true, vertices_22), (true, vertices_266), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_284), (true, vertices_76), (true, vertices_200), (true, vertices_328), (true, vertices_776), (true, vertices_336), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 21 18 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 17 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_565) then 22 else
  if p.val = (false, vertices_213) then 23 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (false, vertices_113) then 1 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_284) then 20 else
  if p.val = (true, vertices_76) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_284), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
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
cert_row_2 0 1 2 3 7 284
cert_row_4 1 0 3 4 5 7 370 50 3
cert_row_4 2 0 4 6 7 8 930 290 2
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 14 286 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 370
cert_cover_5 3 1 0 3 4 5 50 370 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 930
cert_cover_5 5 2 0 4 6 7 290 930 2
cert_coverFacet 6 348
cert_cover_5 6 0 1 2 3 5 284 348 3
cert_coverFacet 7 204
cert_cover_2 7 2 1 5 6 76 204 3
cert_coverFacet 8 968
cert_cover_5 8 3 2 5 6 7 200 968 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0566

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0567.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0567

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 285, 149, 709, 601, 777, 241, 406, 678, 362, 554, 778, 434, 344, 744, 368, 21, 133, 261, 517, 25, 265, 521, 81, 145, 193, 577, 769, 134, 262, 518, 42, 266, 522, 402, 162, 290, 546, 770, 148, 276, 644, 88, 280, 104, 552, 328, 584, 776, 112, 176, 304, 336, 224, 352, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_285, vertices_149, vertices_709, vertices_601, vertices_777, vertices_241, vertices_406, vertices_678, vertices_362, vertices_554, vertices_778, vertices_434, vertices_344, vertices_744, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_25, vertices_265, vertices_521, vertices_81, vertices_145, vertices_193, vertices_577, vertices_769, vertices_134, vertices_262, vertices_518, vertices_42, vertices_266, vertices_522, vertices_402, vertices_162, vertices_290, vertices_546, vertices_770, vertices_148, vertices_276, vertices_644, vertices_88, vertices_280, vertices_104, vertices_552, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_304, vertices_336, vertices_224, vertices_352, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_285), (false, vertices_149), (false, vertices_709), (false, vertices_601), (false, vertices_777), (false, vertices_241), (true, vertices_134), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_402), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_104), (true, vertices_552), (true, vertices_328), (true, vertices_304), (true, vertices_336), (true, vertices_352), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_285) then 20 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_402) then 18 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
cert_nodeAtPriority_50 1 149 0 777 134 42 266 522 162 290 546 104 552 328 304 336 352 672 775 402 285 709 601 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 6 7 402
cert_row_4 1 0 1 4 6 8 678 134 2
cert_row_4 2 0 2 4 5 7 362 42 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 134 406 2
cert_coverFacet 1 678
cert_cover_5 1 1 0 1 4 6 134 678 2
cert_coverFacet 2 362
cert_cover_5 2 2 0 2 4 5 42 362 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 434
cert_cover_5 5 0 0 3 4 6 402 434 2
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 104 744 3
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0567

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0568.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0568

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 227, 643, 301, 165, 901, 865, 406, 794, 210, 898, 220, 284, 236, 632, 808, 67, 131, 515, 37, 133, 261, 97, 161, 289, 577, 641, 769, 82, 146, 274, 530, 194, 386, 642, 770, 28, 44, 204, 268, 148, 276, 164, 388, 88, 280, 536, 104, 296, 552, 776, 208, 592, 224, 608, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_227, vertices_643, vertices_301, vertices_165, vertices_901, vertices_865, vertices_406, vertices_794, vertices_210, vertices_898, vertices_220, vertices_284, vertices_236, vertices_632, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_515, vertices_37, vertices_133, vertices_261, vertices_97, vertices_161, vertices_289, vertices_577, vertices_641, vertices_769, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_204, vertices_268, vertices_148, vertices_276, vertices_164, vertices_388, vertices_88, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_776, vertices_208, vertices_592, vertices_224, vertices_608, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_227), (false, vertices_643), (false, vertices_301), (false, vertices_165), (false, vertices_901), (false, vertices_865), (true, vertices_146), (true, vertices_274), (true, vertices_386), (true, vertices_770), (true, vertices_28), (true, vertices_204), (true, vertices_148), (true, vertices_276), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_104), (true, vertices_552), (true, vertices_776), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 17 else
  if p.val = (false, vertices_227) then 18 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_165) then 1 else
  if p.val = (false, vertices_901) then 21 else
  if p.val = (false, vertices_865) then 26 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_204) then 22 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_776) then 14 else
  if p.val = (true, vertices_208) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 5 8 632 88 2
cert_row_2 1 1 2 5 6 204
cert_row_4 2 0 1 3 6 7 406 146 1
cert_row_4 3 0 2 3 7 8 794 274 1
cert_rows
cert_pivot_2 4 5 1 0
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 2 0 1 3 6 146 406 1
cert_coverFacet 1 794
cert_cover_5 1 3 0 2 3 7 274 794 1
cert_coverFacet 2 210
cert_cover_2 2 3 0 5 6 82 210 3
cert_coverFacet 3 898
cert_cover_2 3 6 0 7 8 386 898 3
cert_coverFacet 4 220
cert_cover_5 4 1 1 2 3 5 28 220 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 236
cert_cover_5 6 1 1 2 4 5 44 236 3
cert_coverFacet 7 632
cert_cover_5 7 0 2 3 4 5 88 632 2
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0568

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0569.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0569

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 147, 227, 835, 541, 777, 721, 406, 422, 354, 284, 364, 556, 692, 744, 840, 19, 67, 131, 259, 25, 265, 521, 145, 529, 193, 577, 769, 390, 146, 274, 98, 162, 290, 322, 28, 44, 268, 524, 148, 276, 532, 164, 292, 548, 280, 104, 552, 328, 584, 776, 656, 224, 352, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_147, vertices_227, vertices_835, vertices_541, vertices_777, vertices_721, vertices_406, vertices_422, vertices_354, vertices_284, vertices_364, vertices_556, vertices_692, vertices_744, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_131, vertices_259, vertices_25, vertices_265, vertices_521, vertices_145, vertices_529, vertices_193, vertices_577, vertices_769, vertices_390, vertices_146, vertices_274, vertices_98, vertices_162, vertices_290, vertices_322, vertices_28, vertices_44, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_280, vertices_104, vertices_552, vertices_328, vertices_584, vertices_776, vertices_656, vertices_224, vertices_352, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_147), (false, vertices_227), (false, vertices_835), (false, vertices_541), (false, vertices_777), (false, vertices_721), (true, vertices_390), (true, vertices_290), (true, vertices_44), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_104), (true, vertices_552), (true, vertices_328), (true, vertices_584), (true, vertices_352), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 16 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 20 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_227) then 21 else
  if p.val = (false, vertices_835) then 22 else
  if p.val = (false, vertices_541) then 17 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (true, vertices_390) then 18 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
cert_nodeAtPriority_21 1 147 0 777 290 44 268 148 276 164 292 548 104 552 328 584 352 672 541 390 283 227 835 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_4 1 1 2 4 5 7 364 44 3
cert_row_4 2 1 3 4 6 8 692 148 2
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 390 406 2
cert_coverFacet 1 422
cert_cover_5 1 0 0 1 4 6 390 422 2
cert_coverFacet 2 354
cert_cover_2 2 4 0 5 7 98 354 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 364
cert_cover_5 4 1 1 2 4 5 44 364 3
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 692
cert_cover_5 6 2 1 3 4 6 148 692 2
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 104 744 3
cert_coverFacet 8 840
cert_cover_2 8 5 2 7 8 328 840 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0569

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0570.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0570

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 613, 453, 645, 809, 369, 654, 186, 298, 778, 306, 466, 604, 156, 212, 632, 69, 133, 517, 97, 289, 545, 321, 385, 641, 769, 42, 138, 266, 522, 50, 146, 274, 290, 386, 642, 770, 28, 140, 524, 84, 148, 196, 580, 644, 56, 600, 152, 296, 552, 776, 112, 304, 208, 336, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_613, vertices_453, vertices_645, vertices_809, vertices_369, vertices_654, vertices_186, vertices_298, vertices_778, vertices_306, vertices_466, vertices_604, vertices_156, vertices_212, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_97, vertices_289, vertices_545, vertices_321, vertices_385, vertices_641, vertices_769, vertices_42, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_290, vertices_386, vertices_642, vertices_770, vertices_28, vertices_140, vertices_524, vertices_84, vertices_148, vertices_196, vertices_580, vertices_644, vertices_56, vertices_600, vertices_152, vertices_296, vertices_552, vertices_776, vertices_112, vertices_304, vertices_208, vertices_336, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_613), (false, vertices_453), (false, vertices_645), (false, vertices_809), (false, vertices_369), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_290), (true, vertices_28), (true, vertices_140), (true, vertices_524), (true, vertices_84), (true, vertices_148), (true, vertices_56), (true, vertices_600), (true, vertices_152), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_809) then 23 else
  if p.val = (false, vertices_369) then 26 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_274) then 7 else
  if p.val = (true, vertices_290) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_84) then 12 else
  if p.val = (true, vertices_148) then 13 else
  if p.val = (true, vertices_56) then 14 else
  if p.val = (true, vertices_600) then 24 else
  if p.val = (true, vertices_152) then 15 else
  if p.val = (true, vertices_208) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_645), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_600), by decide +kernel⟩
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
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_2 1 2 3 5 8 600
cert_row_4 2 0 2 3 4 6 186 42 2
cert_row_4 3 0 3 5 6 7 466 146 2
cert_rows
cert_pivot_2 1 8 2 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 186
cert_cover_5 1 2 0 2 3 4 42 186 2
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 466
cert_cover_5 5 3 0 3 5 6 146 466 2
cert_coverFacet 6 604
cert_cover_5 6 1 1 2 3 5 28 604 3
cert_coverFacet 7 156
cert_cover_2 7 2 1 3 6 28 156 3
cert_coverFacet 8 212
cert_cover_2 8 3 1 5 6 84 212 3
cert_coverFacet 9 632
cert_cover_5 9 1 2 3 4 5 56 632 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0570

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0571.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0571

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [103, 199, 555, 899, 165, 793, 425, 722, 610, 348, 212, 916, 356, 420, 632, 360, 71, 35, 131, 515, 37, 133, 41, 265, 521, 161, 385, 769, 98, 546, 194, 578, 642, 84, 148, 276, 100, 164, 292, 196, 324, 388, 88, 280, 536, 104, 296, 552, 328, 208, 592, 656, 784, 352, 608, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_103, vertices_199, vertices_555, vertices_899, vertices_165, vertices_793, vertices_425, vertices_722, vertices_610, vertices_348, vertices_212, vertices_916, vertices_356, vertices_420, vertices_632, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_71, vertices_35, vertices_131, vertices_515, vertices_37, vertices_133, vertices_41, vertices_265, vertices_521, vertices_161, vertices_385, vertices_769, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_84, vertices_148, vertices_276, vertices_100, vertices_164, vertices_292, vertices_196, vertices_324, vertices_388, vertices_88, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_328, vertices_208, vertices_592, vertices_656, vertices_784, vertices_352, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_103), (false, vertices_199), (false, vertices_555), (false, vertices_899), (false, vertices_165), (false, vertices_793), (false, vertices_425), (true, vertices_578), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_292), (true, vertices_324), (true, vertices_388), (true, vertices_88), (true, vertices_104), (true, vertices_328), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 16 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_103) then 17 else
  if p.val = (false, vertices_199) then 18 else
  if p.val = (false, vertices_555) then 20 else
  if p.val = (false, vertices_899) then 21 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_793) then 23 else
  if p.val = (false, vertices_425) then 24 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_608) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_103), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 8 722 194 1
cert_row_4 1 1 3 6 7 8 916 148 3
cert_row_4 2 1 2 3 5 7 348 84 1
cert_row_4 3 2 3 4 5 8 632 88 2
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 722
cert_cover_5 0 0 0 3 5 6 194 722 1
cert_coverFacet 1 610
cert_cover_2 1 4 0 5 8 98 610 3
cert_coverFacet 2 348
cert_cover_5 2 2 1 2 3 5 84 348 1
cert_coverFacet 3 212
cert_cover_2 3 3 1 5 6 84 212 3
cert_coverFacet 4 916
cert_cover_5 4 1 1 3 6 7 148 916 3
cert_coverFacet 5 356
cert_cover_2 5 4 1 5 7 100 356 3
cert_coverFacet 6 420
cert_cover_2 6 4 1 6 7 164 420 3
cert_coverFacet 7 632
cert_cover_5 7 3 2 3 4 5 88 632 2
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0571

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0572.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0572

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 45, 653, 613, 313, 393, 481, 662, 218, 346, 786, 866, 60, 156, 820, 456, 13, 37, 517, 41, 137, 265, 97, 289, 193, 577, 385, 641, 90, 146, 274, 530, 194, 322, 578, 642, 770, 28, 44, 140, 52, 148, 532, 548, 644, 56, 152, 280, 200, 328, 392, 304, 784, 352, 608, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_45, vertices_653, vertices_613, vertices_313, vertices_393, vertices_481, vertices_662, vertices_218, vertices_346, vertices_786, vertices_866, vertices_60, vertices_156, vertices_820, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_517, vertices_41, vertices_137, vertices_265, vertices_97, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_90, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_44, vertices_140, vertices_52, vertices_148, vertices_532, vertices_548, vertices_644, vertices_56, vertices_152, vertices_280, vertices_200, vertices_328, vertices_392, vertices_304, vertices_784, vertices_352, vertices_608, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_45), (false, vertices_653), (false, vertices_613), (false, vertices_313), (false, vertices_393), (false, vertices_481), (true, vertices_90), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_322), (true, vertices_770), (true, vertices_28), (true, vertices_52), (true, vertices_148), (true, vertices_532), (true, vertices_152), (true, vertices_200), (true, vertices_328), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_45) then 0 else
  if p.val = (false, vertices_653) then 20 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_313) then 23 else
  if p.val = (false, vertices_393) then 1 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_90) then 18 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 1 45 0 393 146 274 530 322 770 28 52 148 532 152 200 328 784 800 707 90 653 613 313 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 3 6 8 662 146 1
cert_row_4 2 0 4 5 7 8 866 322 1
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 146 662 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 6 90 218 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 7 90 346 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 322 866 1
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 156
cert_cover_2 6 2 1 3 6 28 156 3
cert_coverFacet 7 820
cert_cover_5 7 3 1 3 4 7 52 820 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0572

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0573.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0573

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 93, 589, 405, 805, 665, 614, 714, 434, 226, 802, 340, 356, 376, 184, 232, 77, 21, 261, 517, 25, 521, 145, 385, 641, 769, 98, 162, 290, 546, 194, 578, 386, 642, 770, 84, 276, 100, 292, 548, 324, 580, 56, 88, 152, 104, 168, 200, 584, 648, 176, 304, 336, 400, 224, 352, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_93, vertices_589, vertices_405, vertices_805, vertices_665, vertices_614, vertices_714, vertices_434, vertices_226, vertices_802, vertices_340, vertices_356, vertices_376, vertices_184, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_77, vertices_21, vertices_261, vertices_517, vertices_25, vertices_521, vertices_145, vertices_385, vertices_641, vertices_769, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_84, vertices_276, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_56, vertices_88, vertices_152, vertices_104, vertices_168, vertices_200, vertices_584, vertices_648, vertices_176, vertices_304, vertices_336, vertices_400, vertices_224, vertices_352, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_93), (false, vertices_589), (false, vertices_405), (false, vertices_805), (false, vertices_665), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_194), (true, vertices_578), (true, vertices_100), (true, vertices_324), (true, vertices_56), (true, vertices_104), (true, vertices_168), (true, vertices_200), (true, vertices_176), (true, vertices_304), (true, vertices_336), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 23 19 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_93) then 20 else
  if p.val = (false, vertices_589) then 21 else
  if p.val = (false, vertices_405) then 24 else
  if p.val = (false, vertices_805) then 25 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_352) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 23 => Sum.inl 1
  | 24 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 8 614 98 1
cert_row_4 1 0 2 5 6 8 714 194 1
cert_row_4 2 0 3 4 6 7 434 162 1
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 0 0 1 4 5 98 614 1
cert_coverFacet 1 714
cert_cover_5 1 1 0 2 5 6 194 714 1
cert_coverFacet 2 434
cert_cover_5 2 2 0 3 4 6 162 434 1
cert_coverFacet 3 226
cert_cover_2 3 4 0 5 6 98 226 3
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 356
cert_cover_2 6 4 1 5 7 100 356 3
cert_coverFacet 7 376
cert_cover_5 7 3 2 3 4 5 56 376 3
cert_coverFacet 8 184
cert_cover_2 8 3 2 4 6 56 184 3
cert_coverFacet 9 232
cert_cover_2 9 4 2 5 6 104 232 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0573

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0574.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0574

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 307, 163, 835, 589, 233, 353, 406, 178, 898, 124, 188, 908, 596, 788, 880, 35, 131, 259, 515, 73, 137, 521, 97, 161, 289, 321, 577, 50, 146, 274, 162, 386, 642, 770, 60, 76, 140, 524, 84, 148, 276, 532, 580, 388, 772, 104, 168, 648, 112, 176, 304, 592, 784, 352, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_307, vertices_163, vertices_835, vertices_589, vertices_233, vertices_353, vertices_406, vertices_178, vertices_898, vertices_124, vertices_188, vertices_908, vertices_596, vertices_788, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_73, vertices_137, vertices_521, vertices_97, vertices_161, vertices_289, vertices_321, vertices_577, vertices_50, vertices_146, vertices_274, vertices_162, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_140, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_580, vertices_388, vertices_772, vertices_104, vertices_168, vertices_648, vertices_112, vertices_176, vertices_304, vertices_592, vertices_784, vertices_352, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_307), (false, vertices_163), (false, vertices_835), (false, vertices_589), (false, vertices_233), (false, vertices_353), (true, vertices_146), (true, vertices_386), (true, vertices_60), (true, vertices_140), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_388), (true, vertices_772), (true, vertices_112), (true, vertices_176), (true, vertices_592), (true, vertices_784), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 17 else
  if p.val = (false, vertices_307) then 18 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_589) then 21 else
  if p.val = (false, vertices_233) then 24 else
  if p.val = (false, vertices_353) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_60) then 22 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
cert_nodeAtPriority_60 163 353 146 386 140 84 148 276 532 388 772 112 176 592 784 896 651 307 835 589 60 233
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 7 406 146 1
cert_row_4 1 1 2 6 7 8 908 140 3
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 6 1 3
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 146 406 1
cert_coverFacet 1 178
cert_cover_2 1 3 0 4 6 50 178 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 5 60 124 3
cert_coverFacet 4 188
cert_cover_5 4 2 1 2 3 6 60 188 3
cert_coverFacet 5 908
cert_cover_5 5 1 1 2 6 7 140 908 3
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 880
cert_cover_5 8 3 3 4 5 7 112 880 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0574

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0575.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0575

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 163, 803, 589, 233, 849, 353, 406, 370, 178, 898, 124, 188, 908, 596, 788, 35, 131, 515, 73, 137, 521, 97, 161, 289, 321, 577, 769, 50, 146, 274, 162, 290, 386, 642, 770, 60, 76, 140, 524, 84, 148, 276, 532, 580, 388, 772, 104, 168, 648, 112, 176, 336, 592, 784, 352, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_163, vertices_803, vertices_589, vertices_233, vertices_849, vertices_353, vertices_406, vertices_370, vertices_178, vertices_898, vertices_124, vertices_188, vertices_908, vertices_596, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_73, vertices_137, vertices_521, vertices_97, vertices_161, vertices_289, vertices_321, vertices_577, vertices_769, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_140, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_580, vertices_388, vertices_772, vertices_104, vertices_168, vertices_648, vertices_112, vertices_176, vertices_336, vertices_592, vertices_784, vertices_352, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_163), (false, vertices_803), (false, vertices_589), (false, vertices_233), (false, vertices_849), (false, vertices_353), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_386), (true, vertices_60), (true, vertices_140), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_388), (true, vertices_772), (true, vertices_112), (true, vertices_176), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 17 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_589) then 20 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_849) then 25 else
  if p.val = (false, vertices_353) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_60) then 21 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
cert_nodeAtPriority_61 0 163 1 353 50 146 274 386 140 84 148 276 532 388 772 112 176 896 651 803 589 60 233 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 7 370 50 3
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 1 3 6 7 406 146 1
cert_row_4 3 1 2 6 7 8 908 140 3
cert_rows
cert_pivot_2 5 4 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 2 0 1 3 6 146 406 1
cert_coverFacet 1 370
cert_cover_5 1 0 0 3 4 5 50 370 3
cert_coverFacet 2 178
cert_cover_2 2 3 0 4 6 50 178 3
cert_coverFacet 3 898
cert_cover_2 3 6 0 7 8 386 898 3
cert_coverFacet 4 124
cert_cover_5 4 1 1 2 3 5 60 124 3
cert_coverFacet 5 188
cert_cover_5 5 1 1 2 3 6 60 188 3
cert_coverFacet 6 908
cert_cover_5 6 3 1 2 6 7 140 908 3
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 788
cert_cover_2 8 3 1 7 8 276 788 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0575

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0576.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0576

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [199, 651, 787, 323, 565, 341, 645, 426, 778, 450, 620, 716, 116, 824, 232, 496, 67, 131, 259, 515, 21, 69, 133, 517, 273, 529, 321, 641, 138, 266, 522, 194, 322, 386, 770, 588, 52, 84, 100, 548, 196, 644, 104, 168, 296, 552, 200, 648, 776, 112, 304, 560, 336, 784, 224, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_199, vertices_651, vertices_787, vertices_323, vertices_565, vertices_341, vertices_645, vertices_426, vertices_778, vertices_450, vertices_620, vertices_716, vertices_116, vertices_824, vertices_232, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_21, vertices_69, vertices_133, vertices_517, vertices_273, vertices_529, vertices_321, vertices_641, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_386, vertices_770, vertices_588, vertices_52, vertices_84, vertices_100, vertices_548, vertices_196, vertices_644, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_304, vertices_560, vertices_336, vertices_784, vertices_224, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_199), (false, vertices_651), (false, vertices_787), (false, vertices_323), (false, vertices_565), (false, vertices_341), (false, vertices_645), (true, vertices_266), (true, vertices_386), (true, vertices_588), (true, vertices_100), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_200), (true, vertices_776), (true, vertices_112), (true, vertices_304), (true, vertices_224), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 24 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_199) then 17 else
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_787) then 19 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_565) then 21 else
  if p.val = (false, vertices_341) then 22 else
  if p.val = (false, vertices_645) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_588) then 23 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_416) then 14 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
cert_nodeAtPriority_6 323 645 266 386 100 104 168 296 552 200 776 112 304 224 416 448 199 651 787 565 341 588
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 8 588
cert_row_4 1 0 2 4 6 7 426 138 2
cert_row_4 2 2 3 4 7 8 824 296 1
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 426
cert_cover_5 0 1 0 2 4 6 138 426 2
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 620
cert_cover_5 3 0 1 2 4 5 588 620 2
cert_coverFacet 4 716
cert_cover_5 4 0 1 2 5 6 588 716 3
cert_coverFacet 5 116
cert_cover_2 5 3 1 4 5 52 116 3
cert_coverFacet 6 824
cert_cover_5 6 2 2 3 4 7 296 824 1
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0576

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0577.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0577

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 77, 653, 453, 793, 361, 662, 314, 178, 786, 482, 588, 244, 628, 568, 616, 13, 69, 133, 73, 265, 521, 321, 385, 641, 769, 50, 146, 274, 530, 162, 290, 386, 642, 770, 76, 524, 116, 148, 532, 196, 580, 644, 56, 280, 536, 104, 296, 552, 584, 176, 560, 784, 224, 352, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_77, vertices_653, vertices_453, vertices_793, vertices_361, vertices_662, vertices_314, vertices_178, vertices_786, vertices_482, vertices_588, vertices_244, vertices_628, vertices_568, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_133, vertices_73, vertices_265, vertices_521, vertices_321, vertices_385, vertices_641, vertices_769, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_76, vertices_524, vertices_116, vertices_148, vertices_532, vertices_196, vertices_580, vertices_644, vertices_56, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_584, vertices_176, vertices_560, vertices_784, vertices_224, vertices_352, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_77), (false, vertices_653), (false, vertices_453), (false, vertices_793), (false, vertices_361), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_116), (true, vertices_148), (true, vertices_532), (true, vertices_580), (true, vertices_56), (true, vertices_552), (true, vertices_584), (true, vertices_176), (true, vertices_560), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_77) then 0 else
  if p.val = (false, vertices_653) then 20 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_793) then 24 else
  if p.val = (false, vertices_361) then 25 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_116) then 22 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_608) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_77), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_116), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_2 1 1 3 4 5 116
cert_row_4 2 0 2 3 4 7 314 50 1
cert_row_4 3 0 4 5 6 7 482 162 2
cert_rows
cert_pivot_2 8 1 2 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 314
cert_cover_5 1 2 0 2 3 4 50 314 1
cert_coverFacet 2 178
cert_cover_2 2 3 0 4 6 50 178 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 482
cert_cover_5 4 3 0 4 5 6 162 482 2
cert_coverFacet 5 588
cert_cover_2 5 2 1 5 8 76 588 3
cert_coverFacet 6 244
cert_cover_5 6 1 1 3 4 6 116 244 3
cert_coverFacet 7 628
cert_cover_5 7 1 1 3 4 8 116 628 3
cert_coverFacet 8 568
cert_cover_2 8 3 2 4 8 56 568 3
cert_coverFacet 9 616
cert_cover_2 9 4 2 5 8 104 616 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0577

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0578.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0578

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 309, 809, 113, 465, 737, 158, 302, 278, 714, 778, 402, 220, 556, 588, 628, 49, 81, 273, 97, 289, 545, 193, 385, 641, 769, 14, 22, 262, 138, 266, 522, 146, 274, 386, 642, 770, 156, 44, 76, 524, 52, 84, 276, 292, 548, 580, 296, 552, 200, 584, 776, 112, 208, 400, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_309, vertices_809, vertices_113, vertices_465, vertices_737, vertices_158, vertices_302, vertices_278, vertices_714, vertices_778, vertices_402, vertices_220, vertices_556, vertices_588, vertices_628] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_273, vertices_97, vertices_289, vertices_545, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_386, vertices_642, vertices_770, vertices_156, vertices_44, vertices_76, vertices_524, vertices_52, vertices_84, vertices_276, vertices_292, vertices_548, vertices_580, vertices_296, vertices_552, vertices_200, vertices_584, vertices_776, vertices_112, vertices_208, vertices_400, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_309), (false, vertices_809), (false, vertices_113), (false, vertices_465), (false, vertices_737), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_156), (true, vertices_44), (true, vertices_76), (true, vertices_524), (true, vertices_84), (true, vertices_548), (true, vertices_580), (true, vertices_200), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_309) then 20 else
  if p.val = (false, vertices_809) then 23 else
  if p.val = (false, vertices_113) then 0 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_146) then 7 else
  if p.val = (true, vertices_274) then 8 else
  if p.val = (true, vertices_156) then 21 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_76) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_84) then 12 else
  if p.val = (true, vertices_548) then 13 else
  if p.val = (true, vertices_580) then 14 else
  if p.val = (true, vertices_200) then 15 else
  if p.val = (true, vertices_584) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 7 302 14 3
cert_row_4 1 0 2 5 6 8 714 138 2
cert_row_2 2 1 2 3 6 156
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 7 0 2 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 2 0 1 2 3 14 158 3
cert_coverFacet 1 302
cert_cover_5 1 0 0 1 2 4 14 302 3
cert_coverFacet 2 278
cert_cover_2 2 1 0 3 7 22 278 3
cert_coverFacet 3 714
cert_cover_5 3 1 0 2 5 6 138 714 2
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 220
cert_cover_5 6 2 1 2 3 5 156 220 3
cert_coverFacet 7 556
cert_cover_2 7 2 1 4 8 44 556 3
cert_coverFacet 8 588
cert_cover_2 8 2 1 5 8 76 588 3
cert_coverFacet 9 628
cert_cover_5 9 3 1 3 4 5 52 628 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0578

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0579.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0579

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 85, 661, 453, 841, 625, 398, 618, 170, 778, 690, 316, 172, 180, 340, 376, 21, 69, 133, 81, 529, 321, 577, 385, 641, 769, 42, 138, 266, 522, 162, 546, 386, 642, 770, 44, 140, 268, 52, 84, 148, 276, 164, 324, 388, 312, 104, 168, 328, 584, 776, 112, 176, 560, 336, 656, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_85, vertices_661, vertices_453, vertices_841, vertices_625, vertices_398, vertices_618, vertices_170, vertices_778, vertices_690, vertices_316, vertices_172, vertices_180, vertices_340, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_133, vertices_81, vertices_529, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_42, vertices_138, vertices_266, vertices_522, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_268, vertices_52, vertices_84, vertices_148, vertices_276, vertices_164, vertices_324, vertices_388, vertices_312, vertices_104, vertices_168, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_560, vertices_336, vertices_656, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_85), (false, vertices_661), (false, vertices_453), (false, vertices_841), (false, vertices_625), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_162), (true, vertices_546), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_52), (true, vertices_276), (true, vertices_164), (true, vertices_312), (true, vertices_104), (true, vertices_168), (true, vertices_176), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_85) then 0 else
  if p.val = (false, vertices_661) then 20 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_841) then 23 else
  if p.val = (false, vertices_625) then 26 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_52) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_164) then 12 else
  if p.val = (true, vertices_312) then 24 else
  if p.val = (true, vertices_104) then 13 else
  if p.val = (true, vertices_168) then 14 else
  if p.val = (true, vertices_176) then 15 else
  if p.val = (true, vertices_336) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_312), by decide +kernel⟩
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
cert_row_4 0 0 1 2 6 7 398 138 1
cert_row_2 1 2 3 4 7 312
cert_row_4 2 0 2 4 5 8 618 42 3
cert_row_4 3 0 3 4 6 8 690 162 1
cert_rows
cert_pivot_2 1 7 2 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 138 398 1
cert_coverFacet 1 618
cert_cover_5 1 2 0 2 4 5 42 618 3
cert_coverFacet 2 170
cert_cover_2 2 2 0 4 6 42 170 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 690
cert_cover_5 4 3 0 3 4 6 162 690 1
cert_coverFacet 5 316
cert_cover_5 5 1 1 2 3 4 44 316 2
cert_coverFacet 6 172
cert_cover_2 6 2 1 4 6 44 172 3
cert_coverFacet 7 180
cert_cover_2 7 3 1 4 6 52 180 3
cert_coverFacet 8 340
cert_cover_2 8 3 1 5 7 84 340 3
cert_coverFacet 9 376
cert_cover_5 9 1 2 3 4 5 312 376 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0579

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0580.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0580

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 805, 665, 617, 169, 433, 214, 614, 390, 774, 602, 402, 364, 460, 216, 424, 41, 137, 521, 145, 273, 529, 161, 289, 545, 769, 70, 134, 262, 518, 82, 146, 274, 530, 578, 386, 770, 332, 100, 292, 548, 196, 388, 772, 88, 152, 536, 104, 168, 296, 200, 584, 392, 208, 400, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_805, vertices_665, vertices_617, vertices_169, vertices_433, vertices_214, vertices_614, vertices_390, vertices_774, vertices_602, vertices_402, vertices_364, vertices_460, vertices_216, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_521, vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_769, vertices_70, vertices_134, vertices_262, vertices_518, vertices_82, vertices_146, vertices_274, vertices_530, vertices_578, vertices_386, vertices_770, vertices_332, vertices_100, vertices_292, vertices_548, vertices_196, vertices_388, vertices_772, vertices_88, vertices_152, vertices_536, vertices_104, vertices_168, vertices_296, vertices_200, vertices_584, vertices_392, vertices_208, vertices_400, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_805), (false, vertices_665), (false, vertices_617), (false, vertices_169), (false, vertices_433), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_82), (true, vertices_146), (true, vertices_578), (true, vertices_386), (true, vertices_332), (true, vertices_100), (true, vertices_196), (true, vertices_388), (true, vertices_88), (true, vertices_296), (true, vertices_200), (true, vertices_392), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_665) then 23 else
  if p.val = (false, vertices_617) then 24 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (false, vertices_433) then 26 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_332) then 21 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_200) then 14 else
  if p.val = (true, vertices_392) then 15 else
  if p.val = (true, vertices_208) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
cert_row_2 0 1 2 5 7 332
cert_row_4 1 0 1 3 5 6 214 70 2
cert_row_4 2 0 1 4 5 8 614 70 2
cert_row_4 3 0 2 3 5 8 602 82 1
cert_rows
cert_pivot_2 7 6 1 0
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 1 0 1 3 5 70 214 2
cert_coverFacet 1 614
cert_cover_5 1 2 0 1 4 5 70 614 2
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 602
cert_cover_5 4 3 0 2 3 5 82 602 1
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 364
cert_cover_5 6 0 1 2 4 5 332 364 2
cert_coverFacet 7 460
cert_cover_5 7 0 1 2 5 6 332 460 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coverFacet 9 424
cert_cover_2 9 4 2 6 7 168 424 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0580

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0581.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0581

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 45, 653, 421, 569, 865, 454, 666, 626, 210, 834, 316, 348, 204, 216, 368, 13, 37, 133, 41, 521, 289, 545, 385, 641, 769, 82, 146, 530, 194, 322, 578, 386, 642, 770, 284, 44, 76, 140, 292, 196, 324, 388, 56, 88, 152, 536, 200, 648, 112, 304, 560, 208, 336, 352, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_45, vertices_653, vertices_421, vertices_569, vertices_865, vertices_454, vertices_666, vertices_626, vertices_210, vertices_834, vertices_316, vertices_348, vertices_204, vertices_216, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_133, vertices_41, vertices_521, vertices_289, vertices_545, vertices_385, vertices_641, vertices_769, vertices_82, vertices_146, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_284, vertices_44, vertices_76, vertices_140, vertices_292, vertices_196, vertices_324, vertices_388, vertices_56, vertices_88, vertices_152, vertices_536, vertices_200, vertices_648, vertices_112, vertices_304, vertices_560, vertices_208, vertices_336, vertices_352, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_45), (false, vertices_653), (false, vertices_421), (false, vertices_569), (false, vertices_865), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_284), (true, vertices_76), (true, vertices_196), (true, vertices_324), (true, vertices_88), (true, vertices_152), (true, vertices_200), (true, vertices_112), (true, vertices_304), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_45) then 0 else
  if p.val = (false, vertices_653) then 20 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_569) then 24 else
  if p.val = (false, vertices_865) then 27 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_284) then 22 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_336) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_284), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 8 626 82 2
cert_row_4 1 0 1 5 6 7 454 194 1
cert_row_2 2 1 2 3 7 284
cert_row_4 3 0 2 3 6 8 666 146 1
cert_rows
cert_pivot_2 4 5 1 0
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 1 0 1 5 6 194 454 1
cert_coverFacet 1 666
cert_cover_5 1 3 0 2 3 6 146 666 1
cert_coverFacet 2 626
cert_cover_5 2 0 0 3 4 5 82 626 2
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 316
cert_cover_5 5 2 1 2 3 4 284 316 3
cert_coverFacet 6 348
cert_cover_5 6 2 1 2 3 5 284 348 3
cert_coverFacet 7 204
cert_cover_2 7 2 1 5 6 76 204 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coverFacet 9 368
cert_cover_2 9 4 3 5 7 112 368 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0581

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0582.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0582

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 203, 787, 323, 565, 341, 197, 426, 330, 898, 620, 716, 116, 376, 680, 944, 67, 131, 259, 515, 21, 69, 133, 517, 273, 529, 193, 321, 74, 138, 266, 322, 386, 642, 770, 588, 52, 84, 100, 548, 196, 644, 104, 168, 296, 552, 200, 328, 648, 112, 304, 560, 336, 784, 416, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_203, vertices_787, vertices_323, vertices_565, vertices_341, vertices_197, vertices_426, vertices_330, vertices_898, vertices_620, vertices_716, vertices_116, vertices_376, vertices_680, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_21, vertices_69, vertices_133, vertices_517, vertices_273, vertices_529, vertices_193, vertices_321, vertices_74, vertices_138, vertices_266, vertices_322, vertices_386, vertices_642, vertices_770, vertices_588, vertices_52, vertices_84, vertices_100, vertices_548, vertices_196, vertices_644, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_648, vertices_112, vertices_304, vertices_560, vertices_336, vertices_784, vertices_416, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_203), (false, vertices_787), (false, vertices_323), (false, vertices_565), (false, vertices_341), (false, vertices_197), (true, vertices_266), (true, vertices_386), (true, vertices_588), (true, vertices_100), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_648), (true, vertices_112), (true, vertices_304), (true, vertices_416), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 24 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 17 else
  if p.val = (false, vertices_203) then 18 else
  if p.val = (false, vertices_787) then 19 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_565) then 21 else
  if p.val = (false, vertices_341) then 22 else
  if p.val = (false, vertices_197) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_588) then 23 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_672) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
cert_nodeAtPriority_6 323 197 266 386 100 104 168 296 552 328 648 112 304 416 672 896 647 203 787 565 341 588
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 8 588
cert_row_4 1 0 2 4 6 7 426 138 2
cert_row_4 2 2 3 4 5 7 376 104 1
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 426
cert_cover_5 0 1 0 2 4 6 138 426 2
cert_coverFacet 1 330
cert_cover_2 1 2 0 5 7 74 330 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 620
cert_cover_5 3 0 1 2 4 5 588 620 2
cert_coverFacet 4 716
cert_cover_5 4 0 1 2 5 6 588 716 3
cert_coverFacet 5 116
cert_cover_2 5 3 1 4 5 52 116 3
cert_coverFacet 6 376
cert_cover_5 6 2 2 3 4 5 104 376 1
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coverFacet 8 944
cert_cover_5 8 3 3 4 6 7 304 944 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0582

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0583.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0583

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 781, 309, 149, 709, 585, 465, 806, 186, 218, 554, 778, 306, 338, 692, 744, 21, 133, 261, 517, 73, 265, 521, 145, 273, 193, 321, 577, 154, 42, 74, 266, 522, 50, 82, 274, 290, 546, 322, 770, 52, 148, 292, 548, 644, 772, 168, 552, 200, 584, 776, 176, 304, 208, 336, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_781, vertices_309, vertices_149, vertices_709, vertices_585, vertices_465, vertices_806, vertices_186, vertices_218, vertices_554, vertices_778, vertices_306, vertices_338, vertices_692, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_145, vertices_273, vertices_193, vertices_321, vertices_577, vertices_154, vertices_42, vertices_74, vertices_266, vertices_522, vertices_50, vertices_82, vertices_274, vertices_290, vertices_546, vertices_322, vertices_770, vertices_52, vertices_148, vertices_292, vertices_548, vertices_644, vertices_772, vertices_168, vertices_552, vertices_200, vertices_584, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_781), (false, vertices_309), (false, vertices_149), (false, vertices_709), (false, vertices_585), (false, vertices_465), (true, vertices_154), (true, vertices_42), (true, vertices_522), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_548), (true, vertices_168), (true, vertices_552), (true, vertices_200), (true, vertices_176), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 17 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_309) then 21 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_585) then 1 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (true, vertices_154) then 18 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
cert_nodeAtPriority_21 0 149 1 585 42 522 50 82 274 290 546 770 548 168 552 200 176 672 331 154 781 309 709 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_2 1 0 2 3 6 154
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 2 4 5 6 8 744 168 2
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 186
cert_cover_5 1 1 0 2 3 4 154 186 3
cert_coverFacet 2 218
cert_cover_5 2 1 0 2 3 5 154 218 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 306
cert_cover_2 5 3 0 4 7 50 306 3
cert_coverFacet 6 338
cert_cover_2 6 3 0 5 7 82 338 3
cert_coverFacet 7 692
cert_cover_5 7 2 1 3 4 6 52 692 3
cert_coverFacet 8 744
cert_cover_5 8 3 2 4 5 6 168 744 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0583

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0584.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0584

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 781, 837, 313, 681, 625, 454, 714, 690, 594, 402, 172, 300, 204, 588, 436, 773, 41, 265, 521, 49, 81, 273, 545, 321, 577, 82, 146, 274, 530, 194, 322, 578, 386, 642, 44, 76, 140, 268, 524, 164, 292, 196, 324, 580, 388, 168, 296, 200, 584, 648, 176, 304, 560, 592, 400, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_781, vertices_837, vertices_313, vertices_681, vertices_625, vertices_454, vertices_714, vertices_690, vertices_594, vertices_402, vertices_172, vertices_300, vertices_204, vertices_588, vertices_436] (by decide +kernel)
  polygons := literalFinset [vertices_773, vertices_41, vertices_265, vertices_521, vertices_49, vertices_81, vertices_273, vertices_545, vertices_321, vertices_577, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_44, vertices_76, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_196, vertices_324, vertices_580, vertices_388, vertices_168, vertices_296, vertices_200, vertices_584, vertices_648, vertices_176, vertices_304, vertices_560, vertices_592, vertices_400, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_781), (false, vertices_837), (false, vertices_313), (false, vertices_681), (false, vertices_625), (true, vertices_146), (true, vertices_530), (true, vertices_194), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_44), (true, vertices_76), (true, vertices_140), (true, vertices_164), (true, vertices_292), (true, vertices_196), (true, vertices_388), (true, vertices_200), (true, vertices_584), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 18 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_313) then 23 else
  if p.val = (false, vertices_681) then 24 else
  if p.val = (false, vertices_625) then 26 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_584) then 14 else
  if p.val = (true, vertices_176) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
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
cert_row_4 0 0 2 5 6 8 714 194 1
cert_row_4 1 0 1 5 6 7 454 194 1
cert_row_4 2 0 3 4 6 8 690 146 2
cert_row_4 3 1 3 4 6 7 436 164 1
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 1 0 1 5 6 194 454 1
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 194 714 1
cert_coverFacet 2 690
cert_cover_5 2 2 0 3 4 6 146 690 2
cert_coverFacet 3 594
cert_cover_2 3 3 0 5 8 82 594 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 172
cert_cover_2 5 2 1 4 6 44 172 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 204
cert_cover_2 7 2 1 5 6 76 204 3
cert_coverFacet 8 588
cert_cover_2 8 2 1 5 8 76 588 3
cert_coverFacet 9 436
cert_cover_5 9 3 1 3 4 6 164 436 1
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0584

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0585.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0585

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 803, 707, 665, 817, 465, 302, 566, 582, 60, 540, 716, 332, 184, 488, 432, 67, 259, 515, 145, 273, 529, 801, 193, 321, 641, 38, 70, 262, 518, 290, 546, 578, 28, 44, 76, 268, 524, 52, 532, 324, 580, 56, 152, 536, 168, 296, 200, 328, 648, 176, 304, 560, 400, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_803, vertices_707, vertices_665, vertices_817, vertices_465, vertices_302, vertices_566, vertices_582, vertices_60, vertices_540, vertices_716, vertices_332, vertices_184, vertices_488, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_145, vertices_273, vertices_529, vertices_801, vertices_193, vertices_321, vertices_641, vertices_38, vertices_70, vertices_262, vertices_518, vertices_290, vertices_546, vertices_578, vertices_28, vertices_44, vertices_76, vertices_268, vertices_524, vertices_52, vertices_532, vertices_324, vertices_580, vertices_56, vertices_152, vertices_536, vertices_168, vertices_296, vertices_200, vertices_328, vertices_648, vertices_176, vertices_304, vertices_560, vertices_400, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_803), (false, vertices_707), (false, vertices_665), (false, vertices_817), (false, vertices_465), (true, vertices_38), (true, vertices_518), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_532), (true, vertices_580), (true, vertices_56), (true, vertices_168), (true, vertices_296), (true, vertices_200), (true, vertices_328), (true, vertices_176), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 21 23 25 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 18 else
  if p.val = (false, vertices_803) then 26 else
  if p.val = (false, vertices_707) then 19 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_817) then 27 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_328) then 14 else
  if p.val = (true, vertices_176) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 27 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 38 2
cert_row_4 1 0 1 2 4 7 302 38 2
cert_row_4 2 1 2 5 6 8 716 76 3
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 1 0 1 2 4 38 302 2
cert_coverFacet 1 566
cert_cover_5 1 0 0 1 3 4 38 566 2
cert_coverFacet 2 582
cert_cover_2 2 1 0 5 8 70 582 3
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 716
cert_cover_5 5 2 1 2 5 6 76 716 3
cert_coverFacet 6 332
cert_cover_2 6 2 1 5 7 76 332 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 168 488 2
cert_coverFacet 9 432
cert_cover_2 9 4 3 6 7 176 432 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0585

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0586.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0586

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 805, 313, 153, 233, 465, 609, 542, 302, 774, 282, 722, 338, 668, 172, 740, 25, 41, 137, 145, 273, 97, 289, 545, 193, 321, 577, 769, 14, 262, 518, 26, 266, 82, 274, 530, 322, 578, 770, 540, 44, 140, 164, 292, 548, 644, 772, 152, 280, 168, 296, 208, 336, 656, 224, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_805, vertices_313, vertices_153, vertices_233, vertices_465, vertices_609, vertices_542, vertices_302, vertices_774, vertices_282, vertices_722, vertices_338, vertices_668, vertices_172, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_137, vertices_145, vertices_273, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_769, vertices_14, vertices_262, vertices_518, vertices_26, vertices_266, vertices_82, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_540, vertices_44, vertices_140, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_152, vertices_280, vertices_168, vertices_296, vertices_208, vertices_336, vertices_656, vertices_224, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_805), (false, vertices_313), (false, vertices_153), (false, vertices_233), (false, vertices_465), (false, vertices_609), (true, vertices_14), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_266), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_540), (true, vertices_44), (true, vertices_140), (true, vertices_164), (true, vertices_644), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_153) then 0 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (false, vertices_609) then 1 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_82) then 7 else
  if p.val = (true, vertices_274) then 8 else
  if p.val = (true, vertices_530) then 9 else
  if p.val = (true, vertices_540) then 20 else
  if p.val = (true, vertices_44) then 10 else
  if p.val = (true, vertices_140) then 11 else
  if p.val = (true, vertices_164) then 12 else
  if p.val = (true, vertices_644) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_153), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_609), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_540), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 7 302 14 3
cert_row_2 1 1 2 3 8 540
cert_row_4 2 0 3 5 6 8 722 82 3
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 1 0 1 2 3 14 542 3
cert_coverFacet 1 302
cert_cover_5 1 0 0 1 2 4 14 302 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 722
cert_cover_5 4 2 0 3 5 6 82 722 3
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 668
cert_cover_5 6 1 1 2 3 6 540 668 3
cert_coverFacet 7 172
cert_cover_2 7 2 1 4 6 44 172 3
cert_coverFacet 8 740
cert_cover_5 8 3 1 4 5 6 164 740 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0586

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0587.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0587

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 157, 285, 805, 709, 401, 481, 302, 570, 282, 466, 594, 354, 556, 652, 728, 29, 133, 261, 517, 145, 273, 97, 289, 545, 193, 577, 385, 26, 42, 266, 82, 274, 530, 98, 290, 546, 322, 578, 44, 140, 268, 524, 292, 548, 644, 152, 280, 536, 552, 648, 208, 592, 400, 352, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_157, vertices_285, vertices_805, vertices_709, vertices_401, vertices_481, vertices_302, vertices_570, vertices_282, vertices_466, vertices_594, vertices_354, vertices_556, vertices_652, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_133, vertices_261, vertices_517, vertices_145, vertices_273, vertices_97, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_26, vertices_42, vertices_266, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_44, vertices_140, vertices_268, vertices_524, vertices_292, vertices_548, vertices_644, vertices_152, vertices_280, vertices_536, vertices_552, vertices_648, vertices_208, vertices_592, vertices_400, vertices_352, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_157), (false, vertices_285), (false, vertices_805), (false, vertices_709), (false, vertices_401), (false, vertices_481), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_322), (true, vertices_44), (true, vertices_524), (true, vertices_536), (true, vertices_552), (true, vertices_648), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 21 18 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_157) then 19 else
  if p.val = (false, vertices_285) then 20 else
  if p.val = (false, vertices_805) then 22 else
  if p.val = (false, vertices_709) then 23 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_592) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
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
cert_row_4 0 0 1 2 4 7 302 42 1
cert_row_4 1 0 2 3 4 8 570 26 3
cert_row_4 2 0 3 5 6 7 466 82 3
cert_row_4 3 2 3 5 6 8 728 152 2
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 4 42 302 1
cert_coverFacet 1 570
cert_cover_5 1 1 0 2 3 4 26 570 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 466
cert_cover_5 3 2 0 3 5 6 82 466 3
cert_coverFacet 4 594
cert_cover_2 4 3 0 5 8 82 594 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 728
cert_cover_5 8 3 2 3 5 6 152 728 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0587

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0588.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0588

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 141, 597, 229, 905, 113, 689, 286, 534, 778, 370, 562, 930, 348, 204, 488, 13, 69, 133, 517, 137, 521, 49, 81, 529, 97, 161, 641, 14, 22, 518, 266, 522, 50, 274, 530, 290, 546, 770, 284, 76, 140, 84, 532, 196, 200, 328, 392, 776, 112, 560, 336, 224, 352, 416, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_141, vertices_597, vertices_229, vertices_905, vertices_113, vertices_689, vertices_286, vertices_534, vertices_778, vertices_370, vertices_562, vertices_930, vertices_348, vertices_204, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_133, vertices_517, vertices_137, vertices_521, vertices_49, vertices_81, vertices_529, vertices_97, vertices_161, vertices_641, vertices_14, vertices_22, vertices_518, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_284, vertices_76, vertices_140, vertices_84, vertices_532, vertices_196, vertices_200, vertices_328, vertices_392, vertices_776, vertices_112, vertices_560, vertices_336, vertices_224, vertices_352, vertices_416, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_141), (false, vertices_597), (false, vertices_229), (false, vertices_905), (false, vertices_113), (false, vertices_689), (true, vertices_22), (true, vertices_266), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_284), (true, vertices_76), (true, vertices_200), (true, vertices_328), (true, vertices_336), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 17 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_229) then 20 else
  if p.val = (false, vertices_905) then 23 else
  if p.val = (false, vertices_113) then 1 else
  if p.val = (false, vertices_689) then 25 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_284) then 21 else
  if p.val = (true, vertices_76) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_284), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
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
cert_row_2 0 1 2 3 7 284
cert_row_4 1 0 3 4 5 7 370 50 3
cert_row_4 2 0 4 6 7 8 930 290 2
cert_row_4 3 2 4 5 6 7 488 200 1
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 14 286 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 370
cert_cover_5 3 1 0 3 4 5 50 370 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 930
cert_cover_5 5 2 0 4 6 7 290 930 2
cert_coverFacet 6 348
cert_cover_5 6 0 1 2 3 5 284 348 3
cert_coverFacet 7 204
cert_cover_2 7 2 1 5 6 76 204 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 200 488 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0588

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_4443 : Certifies 4443 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0559.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4444 : Certifies 4444 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0560.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4445 : Certifies 4445 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0561.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4446 : Certifies 4446 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0562.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4447 : Certifies 4447 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0563.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4448 : Certifies 4448 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0564.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4449 : Certifies 4449 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0565.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4450 : Certifies 4450 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0566.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4451 : Certifies 4451 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0567.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4452 : Certifies 4452 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0568.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4453 : Certifies 4453 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0569.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4454 : Certifies 4454 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0570.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4455 : Certifies 4455 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0571.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4456 : Certifies 4456 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0572.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4457 : Certifies 4457 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0573.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4458 : Certifies 4458 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0574.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4459 : Certifies 4459 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0575.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4460 : Certifies 4460 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0576.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4461 : Certifies 4461 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0577.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4462 : Certifies 4462 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0578.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4463 : Certifies 4463 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0579.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4464 : Certifies 4464 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0580.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4465 : Certifies 4465 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0581.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4466 : Certifies 4466 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0582.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4467 : Certifies 4467 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0583.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4468 : Certifies 4468 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0584.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4469 : Certifies 4469 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0585.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4470 : Certifies 4470 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0586.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4471 : Certifies 4471 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0587.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4472 : Certifies 4472 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0588.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B147 (j : Fin 30) :
    Certifies (4443 + j.val) := by
  fin_cases j
  · exact projection_4443
  · exact projection_4444
  · exact projection_4445
  · exact projection_4446
  · exact projection_4447
  · exact projection_4448
  · exact projection_4449
  · exact projection_4450
  · exact projection_4451
  · exact projection_4452
  · exact projection_4453
  · exact projection_4454
  · exact projection_4455
  · exact projection_4456
  · exact projection_4457
  · exact projection_4458
  · exact projection_4459
  · exact projection_4460
  · exact projection_4461
  · exact projection_4462
  · exact projection_4463
  · exact projection_4464
  · exact projection_4465
  · exact projection_4466
  · exact projection_4467
  · exact projection_4468
  · exact projection_4469
  · exact projection_4470
  · exact projection_4471
  · exact projection_4472

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
