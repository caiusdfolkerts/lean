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
/- Source: ProjectionCertificates/R_m14e10q1_0285.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0285

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 787, 643, 653, 85, 837, 369, 682, 178, 306, 866, 220, 620, 248, 19, 131, 515, 21, 69, 133, 517, 81, 273, 321, 641, 769, 50, 146, 274, 162, 290, 546, 642, 770, 76, 140, 524, 84, 148, 580, 216, 104, 168, 552, 648, 112, 176, 304, 352, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_787, vertices_643, vertices_653, vertices_85, vertices_837, vertices_369, vertices_682, vertices_178, vertices_306, vertices_866, vertices_220, vertices_620, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_515, vertices_21, vertices_69, vertices_133, vertices_517, vertices_81, vertices_273, vertices_321, vertices_641, vertices_769, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_84, vertices_148, vertices_580, vertices_216, vertices_104, vertices_168, vertices_552, vertices_648, vertices_112, vertices_176, vertices_304, vertices_352, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_787), (false, vertices_643), (false, vertices_653), (false, vertices_85), (false, vertices_837), (false, vertices_369), (true, vertices_50), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_76), (true, vertices_216), (true, vertices_104), (true, vertices_168), (true, vertices_552), (true, vertices_176), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 13 else
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_85) then 1 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_216) then 19 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_608) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
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
cert_row_2 0 2 3 5 6 216
cert_row_4 1 0 2 4 6 8 682 162 1
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 1 2 4 5 8 620 76 2
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 682
cert_cover_5 0 1 0 2 4 6 162 682 1
cert_coverFacet 1 178
cert_cover_2 1 3 0 4 6 50 178 3
cert_coverFacet 2 306
cert_cover_2 2 3 0 4 7 50 306 3
cert_coverFacet 3 866
cert_cover_5 3 2 0 4 5 7 290 866 2
cert_coverFacet 4 220
cert_cover_5 4 0 1 2 3 5 76 220 2
cert_coverFacet 5 620
cert_cover_5 5 3 1 2 4 5 76 620 2
cert_coverFacet 6 248
cert_cover_5 6 0 2 3 4 5 216 248 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0285

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m14e10q1_0303.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0303

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 613, 809, 713, 433, 225, 206, 590, 182, 534, 794, 402, 820, 228, 137, 265, 521, 97, 161, 289, 545, 193, 577, 385, 78, 22, 134, 518, 138, 266, 522, 146, 274, 530, 386, 52, 532, 100, 164, 548, 196, 580, 200, 584, 776, 176, 304, 400, 784, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_613, vertices_809, vertices_713, vertices_433, vertices_225, vertices_206, vertices_590, vertices_182, vertices_534, vertices_794, vertices_402, vertices_820, vertices_228] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_78, vertices_22, vertices_134, vertices_518, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_52, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_200, vertices_584, vertices_776, vertices_176, vertices_304, vertices_400, vertices_784, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_613), (false, vertices_809), (false, vertices_713), (false, vertices_433), (false, vertices_225), (true, vertices_78), (true, vertices_22), (true, vertices_134), (true, vertices_518), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_52), (true, vertices_532), (true, vertices_164), (true, vertices_196), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_809) then 19 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (false, vertices_225) then 0 else
  if p.val = (true, vertices_78) then 15 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_784) then 12 else
  0
cert_priority
cert_nodeAtPriority_37 225 22 134 518 522 146 274 530 52 532 164 196 784 395 78 613 809 713 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 1 3 4 6 182 22 3
cert_row_4 2 0 2 3 7 8 794 266 2
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 5 6 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 6 78 206 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 182
cert_cover_5 2 1 0 1 3 4 22 182 3
cert_coverFacet 3 534
cert_cover_2 3 1 0 3 8 22 534 3
cert_coverFacet 4 794
cert_cover_5 4 2 0 2 3 7 266 794 2
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 820
cert_cover_5 6 3 1 3 4 7 52 820 3
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0303

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m14e10q1_0304.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0304

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 453, 409, 617, 201, 849, 174, 558, 406, 838, 154, 786, 740, 232, 25, 73, 137, 521, 273, 529, 193, 321, 577, 385, 46, 134, 262, 518, 26, 138, 522, 146, 274, 530, 770, 164, 548, 196, 324, 580, 388, 152, 104, 168, 552, 200, 400, 784, 224, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_453, vertices_409, vertices_617, vertices_201, vertices_849, vertices_174, vertices_558, vertices_406, vertices_838, vertices_154, vertices_786, vertices_740, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_137, vertices_521, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_46, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_770, vertices_164, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_152, vertices_104, vertices_168, vertices_552, vertices_200, vertices_400, vertices_784, vertices_224, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_453), (false, vertices_409), (false, vertices_617), (false, vertices_201), (false, vertices_849), (true, vertices_46), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_146), (true, vertices_274), (true, vertices_770), (true, vertices_164), (true, vertices_548), (true, vertices_580), (true, vertices_168), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 14 else
  if p.val = (false, vertices_453) then 17 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (true, vertices_46) then 15 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_224) then 12 else
  0
cert_priority
cert_nodeAtPriority_37 201 134 262 518 138 146 274 770 164 548 580 168 224 539 46 453 409 617 849
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 1 3 6 7 406 134 2
cert_row_4 2 0 1 5 7 8 838 262 2
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 0 0 1 2 6 46 174 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 8 46 558 3
cert_coverFacet 2 406
cert_cover_5 2 1 0 1 3 6 134 406 2
cert_coverFacet 3 838
cert_cover_5 3 2 0 1 5 7 262 838 2
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 164 740 2
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0304

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m14e10q1_0305.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0305

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 787, 227, 547, 677, 713, 777, 566, 370, 124, 668, 236, 344, 792, 35, 67, 259, 515, 73, 265, 521, 161, 545, 193, 641, 769, 50, 274, 530, 98, 546, 322, 28, 108, 140, 52, 532, 164, 548, 644, 88, 280, 536, 200, 328, 648, 776, 112, 336, 784, 224]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_787, vertices_227, vertices_547, vertices_677, vertices_713, vertices_777, vertices_566, vertices_370, vertices_124, vertices_668, vertices_236, vertices_344, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_259, vertices_515, vertices_73, vertices_265, vertices_521, vertices_161, vertices_545, vertices_193, vertices_641, vertices_769, vertices_50, vertices_274, vertices_530, vertices_98, vertices_546, vertices_322, vertices_28, vertices_108, vertices_140, vertices_52, vertices_532, vertices_164, vertices_548, vertices_644, vertices_88, vertices_280, vertices_536, vertices_200, vertices_328, vertices_648, vertices_776, vertices_112, vertices_336, vertices_784, vertices_224] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_787), (false, vertices_227), (false, vertices_547), (false, vertices_677), (false, vertices_713), (false, vertices_777), (true, vertices_50), (true, vertices_28), (true, vertices_108), (true, vertices_140), (true, vertices_52), (true, vertices_532), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_112), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_227) then 15 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_108) then 18 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_336) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 16 => Sum.inl 1
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
cert_row_4 0 0 3 4 5 7 370 50 3
cert_row_2 1 1 2 4 5 108
cert_row_4 2 0 1 3 4 8 566 50 1
cert_row_4 3 1 2 3 6 8 668 28 3
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 2 0 1 3 4 50 566 1
cert_coverFacet 1 370
cert_cover_5 1 0 0 3 4 5 50 370 3
cert_coverFacet 2 124
cert_cover_5 2 1 1 2 3 4 28 124 3
cert_coverFacet 3 668
cert_cover_5 3 3 1 2 3 6 28 668 3
cert_coverFacet 4 236
cert_cover_5 4 1 1 2 4 6 108 236 3
cert_coverFacet 5 344
cert_cover_2 5 3 2 5 7 88 344 3
cert_coverFacet 6 792
cert_cover_2 6 3 2 7 8 280 792 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0305

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m14e10q1_0306.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0306

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 531, 771, 661, 453, 841, 737, 314, 618, 778, 690, 244, 372, 360, 19, 259, 515, 21, 133, 261, 529, 193, 321, 577, 641, 769, 42, 266, 522, 50, 274, 530, 546, 770, 116, 148, 276, 196, 324, 104, 296, 328, 584, 776, 176, 304, 656, 224, 352, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_531, vertices_771, vertices_661, vertices_453, vertices_841, vertices_737, vertices_314, vertices_618, vertices_778, vertices_690, vertices_244, vertices_372, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_259, vertices_515, vertices_21, vertices_133, vertices_261, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_546, vertices_770, vertices_116, vertices_148, vertices_276, vertices_196, vertices_324, vertices_104, vertices_296, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_656, vertices_224, vertices_352, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_531), (false, vertices_771), (false, vertices_661), (false, vertices_453), (false, vertices_841), (false, vertices_737), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_546), (true, vertices_116), (true, vertices_104), (true, vertices_296), (true, vertices_176), (true, vertices_304), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 13 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_661) then 15 else
  if p.val = (false, vertices_453) then 16 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (false, vertices_737) then 22 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_116) then 17 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
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
cert_row_2 0 1 3 4 5 116
cert_row_4 1 0 2 3 4 7 314 42 2
cert_row_4 2 0 2 4 5 8 618 42 3
cert_row_4 3 0 3 4 6 8 690 50 3
cert_rows
cert_pivot_2 1 7 2 0
cert_heightProof 4
cert_coverFacet 0 314
cert_cover_5 0 1 0 2 3 4 42 314 2
cert_coverFacet 1 618
cert_cover_5 1 2 0 2 4 5 42 618 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 690
cert_cover_5 3 3 0 3 4 6 50 690 3
cert_coverFacet 4 244
cert_cover_5 4 0 1 3 4 6 116 244 3
cert_coverFacet 5 372
cert_cover_5 5 0 1 3 4 7 116 372 3
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0306

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m14e10q1_0307.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0307

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 551, 781, 405, 689, 849, 142, 526, 234, 842, 626, 460, 240, 464, 39, 133, 261, 517, 145, 273, 529, 161, 545, 769, 14, 134, 518, 74, 138, 522, 98, 162, 546, 578, 140, 268, 524, 388, 200, 328, 776, 112, 176, 560, 208, 336, 592, 400, 224, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_551, vertices_781, vertices_405, vertices_689, vertices_849, vertices_142, vertices_526, vertices_234, vertices_842, vertices_626, vertices_460, vertices_240, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_39, vertices_133, vertices_261, vertices_517, vertices_145, vertices_273, vertices_529, vertices_161, vertices_545, vertices_769, vertices_14, vertices_134, vertices_518, vertices_74, vertices_138, vertices_522, vertices_98, vertices_162, vertices_546, vertices_578, vertices_140, vertices_268, vertices_524, vertices_388, vertices_200, vertices_328, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_336, vertices_592, vertices_400, vertices_224, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_551), (false, vertices_781), (false, vertices_405), (false, vertices_689), (false, vertices_849), (true, vertices_14), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_98), (true, vertices_578), (true, vertices_140), (true, vertices_200), (true, vertices_328), (true, vertices_112), (true, vertices_208), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 14 else
  if p.val = (false, vertices_551) then 15 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_167), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 8 626 98 1
cert_row_4 1 0 2 4 5 6 234 74 2
cert_row_4 2 0 2 5 7 8 842 74 3
cert_row_4 3 1 2 5 6 7 460 140 2
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 234
cert_cover_5 2 1 0 2 4 5 74 234 2
cert_coverFacet 3 842
cert_cover_5 3 2 0 2 5 7 74 842 3
cert_coverFacet 4 626
cert_cover_5 4 0 0 3 4 5 98 626 1
cert_coverFacet 5 460
cert_cover_5 5 3 1 2 5 6 140 460 2
cert_coverFacet 6 240
cert_cover_2 6 4 3 5 6 112 240 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0307

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m14e10q1_0308.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0308

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 677, 345, 617, 905, 225, 86, 534, 230, 902, 794, 338, 124, 572, 73, 265, 521, 97, 161, 545, 193, 321, 385, 641, 22, 70, 134, 518, 82, 274, 530, 194, 322, 386, 770, 60, 84, 532, 100, 164, 548, 644, 88, 280, 536, 104, 552, 776, 336, 224, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_677, vertices_345, vertices_617, vertices_905, vertices_225, vertices_86, vertices_534, vertices_230, vertices_902, vertices_794, vertices_338, vertices_124, vertices_572] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_22, vertices_70, vertices_134, vertices_518, vertices_82, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_770, vertices_60, vertices_84, vertices_532, vertices_100, vertices_164, vertices_548, vertices_644, vertices_88, vertices_280, vertices_536, vertices_104, vertices_552, vertices_776, vertices_336, vertices_224, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_677), (false, vertices_345), (false, vertices_617), (false, vertices_905), (false, vertices_225), (true, vertices_22), (true, vertices_70), (true, vertices_134), (true, vertices_518), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_770), (true, vertices_60), (true, vertices_84), (true, vertices_532), (true, vertices_100), (true, vertices_536)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_905) then 21 else
  if p.val = (false, vertices_225) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_60) then 17 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_536) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 6 230 70 2
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 1 6 7 8 902 134 3
cert_row_4 3 0 2 3 7 8 794 274 1
cert_rows
cert_pivot_2 5 4 1 0
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 230
cert_cover_5 2 0 0 1 4 5 70 230 2
cert_coverFacet 3 902
cert_cover_5 3 2 0 1 6 7 134 902 3
cert_coverFacet 4 794
cert_cover_5 4 3 0 2 3 7 274 794 1
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 124
cert_cover_5 6 1 1 2 3 5 60 124 3
cert_coverFacet 7 572
cert_cover_5 7 1 1 2 3 8 60 572 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0308

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m14e10q1_0312.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0312

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 535, 653, 229, 625, 961, 270, 526, 294, 906, 306, 850, 428, 496, 23, 37, 133, 517, 49, 529, 97, 193, 577, 641, 14, 38, 262, 518, 266, 522, 50, 274, 530, 290, 770, 140, 268, 524, 164, 292, 392, 648, 112, 304, 336, 592, 224, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_535, vertices_653, vertices_229, vertices_625, vertices_961, vertices_270, vertices_526, vertices_294, vertices_906, vertices_306, vertices_850, vertices_428, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_37, vertices_133, vertices_517, vertices_49, vertices_529, vertices_97, vertices_193, vertices_577, vertices_641, vertices_14, vertices_38, vertices_262, vertices_518, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_290, vertices_770, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_392, vertices_648, vertices_112, vertices_304, vertices_336, vertices_592, vertices_224, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_535), (false, vertices_653), (false, vertices_229), (false, vertices_625), (false, vertices_961), (true, vertices_14), (true, vertices_262), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_290), (true, vertices_770), (true, vertices_268), (true, vertices_292), (true, vertices_392), (true, vertices_304), (true, vertices_336), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 14 else
  if p.val = (false, vertices_535) then 15 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 6 7 428 140 2
cert_row_4 1 0 2 6 7 8 906 266 2
cert_row_4 2 0 3 5 7 8 850 274 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 294
cert_cover_2 2 1 0 4 7 38 294 3
cert_coverFacet 3 906
cert_cover_5 3 1 0 2 6 7 266 906 2
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 850
cert_cover_5 5 2 0 3 5 7 274 850 2
cert_coverFacet 6 428
cert_cover_5 6 0 1 2 4 6 140 428 2
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0312

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m14e10q1_0313.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0313

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 527, 357, 677, 345, 617, 406, 646, 602, 282, 690, 420, 880, 432, 15, 37, 261, 517, 73, 265, 521, 97, 545, 321, 134, 262, 518, 26, 266, 522, 146, 274, 530, 642, 164, 292, 388, 644, 88, 280, 584, 176, 304, 560, 336, 592, 400, 352, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_527, vertices_357, vertices_677, vertices_345, vertices_617, vertices_406, vertices_646, vertices_602, vertices_282, vertices_690, vertices_420, vertices_880, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_15, vertices_37, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_97, vertices_545, vertices_321, vertices_134, vertices_262, vertices_518, vertices_26, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_642, vertices_164, vertices_292, vertices_388, vertices_644, vertices_88, vertices_280, vertices_584, vertices_176, vertices_304, vertices_560, vertices_336, vertices_592, vertices_400, vertices_352, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_527), (false, vertices_357), (false, vertices_677), (false, vertices_345), (false, vertices_617), (true, vertices_134), (true, vertices_26), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_642), (true, vertices_388), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_592), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
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
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
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
cert_row_4 0 0 1 3 6 7 406 134 2
cert_row_4 1 0 2 3 5 8 602 26 3
cert_row_4 2 0 3 4 6 8 690 146 2
cert_row_4 3 3 4 5 7 8 880 304 2
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 134 406 2
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 602
cert_cover_5 2 1 0 2 3 5 26 602 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 690
cert_cover_5 4 2 0 3 4 6 146 690 2
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 304 880 2
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0313

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m14e10q1_0314.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0314

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 535, 653, 229, 369, 721, 270, 526, 294, 906, 306, 850, 428, 992, 23, 37, 133, 517, 49, 81, 529, 97, 193, 641, 14, 38, 262, 518, 266, 522, 50, 274, 530, 290, 770, 140, 268, 524, 164, 292, 392, 648, 304, 336, 592, 224, 352, 416, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_535, vertices_653, vertices_229, vertices_369, vertices_721, vertices_270, vertices_526, vertices_294, vertices_906, vertices_306, vertices_850, vertices_428, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_37, vertices_133, vertices_517, vertices_49, vertices_81, vertices_529, vertices_97, vertices_193, vertices_641, vertices_14, vertices_38, vertices_262, vertices_518, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_290, vertices_770, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_392, vertices_648, vertices_304, vertices_336, vertices_592, vertices_224, vertices_352, vertices_416, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_535), (false, vertices_653), (false, vertices_229), (false, vertices_369), (false, vertices_721), (true, vertices_14), (true, vertices_262), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_290), (true, vertices_770), (true, vertices_268), (true, vertices_292), (true, vertices_392), (true, vertices_416), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 14 else
  if p.val = (false, vertices_535) then 15 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 19 => Sum.inl 2
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
cert_row_4 0 0 3 5 7 8 850 274 2
cert_row_4 1 0 2 6 7 8 906 266 2
cert_row_4 2 1 2 4 6 7 428 140 2
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 3 0 1 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 294
cert_cover_2 2 1 0 4 7 38 294 3
cert_coverFacet 3 906
cert_cover_5 3 1 0 2 6 7 266 906 2
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 850
cert_cover_5 5 0 0 3 5 7 274 850 2
cert_coverFacet 6 428
cert_cover_5 6 2 1 2 4 6 140 428 2
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0314

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m14e10q1_0315.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0315

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 535, 395, 835, 709, 481, 154, 538, 810, 572, 244, 868, 184, 424, 23, 131, 259, 515, 133, 517, 193, 321, 577, 385, 26, 138, 266, 522, 146, 530, 770, 52, 148, 532, 100, 548, 196, 580, 56, 152, 536, 168, 296, 552, 392, 176, 224, 352, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_535, vertices_395, vertices_835, vertices_709, vertices_481, vertices_154, vertices_538, vertices_810, vertices_572, vertices_244, vertices_868, vertices_184, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_131, vertices_259, vertices_515, vertices_133, vertices_517, vertices_193, vertices_321, vertices_577, vertices_385, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_770, vertices_52, vertices_148, vertices_532, vertices_100, vertices_548, vertices_196, vertices_580, vertices_56, vertices_152, vertices_536, vertices_168, vertices_296, vertices_552, vertices_392, vertices_176, vertices_224, vertices_352, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_535), (false, vertices_395), (false, vertices_835), (false, vertices_709), (false, vertices_481), (true, vertices_26), (true, vertices_522), (true, vertices_52), (true, vertices_100), (true, vertices_548), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_176), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 13 20 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 14 else
  if p.val = (false, vertices_535) then 15 else
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_709) then 16 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 20 => Sum.inl 2
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
cert_row_4 0 0 2 4 7 8 810 266 2
cert_row_4 1 1 2 3 4 8 572 52 1
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 0 2 3 1
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
cert_coverFacet 5 868
cert_cover_5 5 3 1 4 5 7 100 868 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0315

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m14e10q1_0319.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0319

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 647, 563, 355, 665, 433, 590, 326, 610, 220, 652, 484, 632, 240, 135, 35, 259, 515, 49, 145, 529, 289, 385, 641, 70, 262, 518, 98, 546, 322, 578, 76, 140, 524, 196, 324, 388, 644, 88, 152, 536, 584, 648, 112, 176, 560, 208, 224, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_647, vertices_563, vertices_355, vertices_665, vertices_433, vertices_590, vertices_326, vertices_610, vertices_220, vertices_652, vertices_484, vertices_632, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_135, vertices_35, vertices_259, vertices_515, vertices_49, vertices_145, vertices_529, vertices_289, vertices_385, vertices_641, vertices_70, vertices_262, vertices_518, vertices_98, vertices_546, vertices_322, vertices_578, vertices_76, vertices_140, vertices_524, vertices_196, vertices_324, vertices_388, vertices_644, vertices_88, vertices_152, vertices_536, vertices_584, vertices_648, vertices_112, vertices_176, vertices_560, vertices_208, vertices_224, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_647), (false, vertices_563), (false, vertices_355), (false, vertices_665), (false, vertices_433), (true, vertices_70), (true, vertices_578), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_196), (true, vertices_324), (true, vertices_88), (true, vertices_584), (true, vertices_112), (true, vertices_208), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_563) then 17 else
  if p.val = (false, vertices_355) then 18 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 70 2
cert_row_4 1 1 4 5 6 7 484 196 1
cert_row_4 2 1 2 3 5 6 220 76 2
cert_row_4 3 2 3 4 5 8 632 88 2
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 70 590 2
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 610
cert_cover_2 2 4 0 5 8 98 610 3
cert_coverFacet 3 220
cert_cover_5 3 2 1 2 3 5 76 220 2
cert_coverFacet 4 652
cert_cover_2 4 2 1 6 8 140 652 3
cert_coverFacet 5 484
cert_cover_5 5 1 1 4 5 6 196 484 1
cert_coverFacet 6 632
cert_cover_5 6 3 2 3 4 5 88 632 2
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0319

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m14e10q1_0324.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0324

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 803, 387, 397, 613, 325, 849, 410, 626, 178, 786, 348, 236, 248, 35, 131, 259, 37, 69, 133, 261, 545, 321, 577, 385, 769, 50, 146, 274, 530, 162, 546, 386, 770, 76, 140, 268, 100, 164, 324, 88, 152, 280, 232, 392, 112, 176, 336, 592, 784, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_803, vertices_387, vertices_397, vertices_613, vertices_325, vertices_849, vertices_410, vertices_626, vertices_178, vertices_786, vertices_348, vertices_236, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_37, vertices_69, vertices_133, vertices_261, vertices_545, vertices_321, vertices_577, vertices_385, vertices_769, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_386, vertices_770, vertices_76, vertices_140, vertices_268, vertices_100, vertices_164, vertices_324, vertices_88, vertices_152, vertices_280, vertices_232, vertices_392, vertices_112, vertices_176, vertices_336, vertices_592, vertices_784, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_803), (false, vertices_387), (false, vertices_397), (false, vertices_613), (false, vertices_325), (false, vertices_849), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_76), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_232), (true, vertices_112), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 13 else
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_397) then 16 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_325) then 1 else
  if p.val = (false, vertices_849) then 21 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_232) then 19 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_167), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 8 626 50 3
cert_row_2 1 2 4 5 6 232
cert_row_4 2 0 2 3 6 7 410 146 1
cert_row_4 3 1 2 3 5 7 348 76 2
cert_rows
cert_pivot_2 8 4 0 1
cert_heightProof 4
cert_coverFacet 0 410
cert_cover_5 0 2 0 2 3 6 146 410 1
cert_coverFacet 1 626
cert_cover_5 1 0 0 3 4 5 50 626 3
cert_coverFacet 2 178
cert_cover_2 2 3 0 4 6 50 178 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 348
cert_cover_5 4 3 1 2 3 5 76 348 2
cert_coverFacet 5 236
cert_cover_5 5 1 1 2 4 5 76 236 2
cert_coverFacet 6 248
cert_cover_5 6 1 2 3 4 5 88 248 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0324

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m14e10q1_0338.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0338

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 421, 549, 709, 121, 313, 457, 806, 794, 114, 306, 594, 908, 728, 37, 133, 517, 57, 73, 265, 97, 289, 545, 193, 577, 385, 50, 82, 274, 530, 98, 290, 546, 578, 770, 292, 548, 388, 644, 772, 88, 280, 536, 200, 392, 648, 776, 112, 304, 592, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_421, vertices_549, vertices_709, vertices_121, vertices_313, vertices_457, vertices_806, vertices_794, vertices_114, vertices_306, vertices_594, vertices_908, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_57, vertices_73, vertices_265, vertices_97, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_50, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_88, vertices_280, vertices_536, vertices_200, vertices_392, vertices_648, vertices_776, vertices_112, vertices_304, vertices_592, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_421), (false, vertices_549), (false, vertices_709), (false, vertices_121), (false, vertices_313), (false, vertices_457), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_770), (true, vertices_772), (true, vertices_536), (true, vertices_648), (true, vertices_776), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 13 else
  if p.val = (false, vertices_421) then 15 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_709) then 16 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_313) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_592) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_549), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
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
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_4 1 0 2 3 7 8 794 274 1
cert_row_4 2 1 2 6 7 8 908 388 1
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 4 0 1 2
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 274 794 1
cert_coverFacet 2 114
cert_cover_2 2 3 0 4 5 50 114 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 594
cert_cover_2 4 3 0 5 8 82 594 3
cert_coverFacet 5 908
cert_cover_5 5 2 1 2 6 7 388 908 1
cert_coverFacet 6 728
cert_cover_5 6 3 2 3 5 6 88 728 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0338

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m14e10q1_0340.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0340

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 267, 803, 677, 713, 329, 849, 566, 58, 346, 786, 124, 236, 724, 11, 35, 259, 73, 137, 265, 161, 545, 321, 577, 641, 769, 26, 42, 266, 50, 274, 530, 546, 770, 108, 52, 84, 532, 164, 548, 196, 644, 56, 88, 168, 200, 328, 336, 592, 784, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_267, vertices_803, vertices_677, vertices_713, vertices_329, vertices_849, vertices_566, vertices_58, vertices_346, vertices_786, vertices_124, vertices_236, vertices_724] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_73, vertices_137, vertices_265, vertices_161, vertices_545, vertices_321, vertices_577, vertices_641, vertices_769, vertices_26, vertices_42, vertices_266, vertices_50, vertices_274, vertices_530, vertices_546, vertices_770, vertices_108, vertices_52, vertices_84, vertices_532, vertices_164, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_168, vertices_200, vertices_328, vertices_336, vertices_592, vertices_784, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_267), (false, vertices_803), (false, vertices_677), (false, vertices_713), (false, vertices_329), (false, vertices_849), (true, vertices_26), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_108), (true, vertices_52), (true, vertices_84), (true, vertices_532), (true, vertices_196), (true, vertices_56), (true, vertices_88)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 13 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (false, vertices_849) then 21 else
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
  if p.val = (true, vertices_88) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 7 346 26 3
cert_row_2 1 1 2 4 5 108
cert_row_4 2 0 1 3 4 8 566 50 1
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 2 0 1 3 4 50 566 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 5 26 346 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 124
cert_cover_5 4 1 1 2 3 4 108 124 2
cert_coverFacet 5 236
cert_cover_5 5 1 1 2 4 6 108 236 3
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 84 724 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0340

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m14e10q1_0341.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0341

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 327, 27, 211, 541, 709, 689, 282, 434, 962, 844, 312, 568, 936, 263, 11, 19, 67, 13, 69, 517, 25, 145, 529, 193, 641, 26, 266, 146, 274, 194, 322, 386, 268, 524, 324, 580, 56, 280, 536, 296, 552, 776, 176, 304, 560, 416, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_327, vertices_27, vertices_211, vertices_541, vertices_709, vertices_689, vertices_282, vertices_434, vertices_962, vertices_844, vertices_312, vertices_568, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_263, vertices_11, vertices_19, vertices_67, vertices_13, vertices_69, vertices_517, vertices_25, vertices_145, vertices_529, vertices_193, vertices_641, vertices_26, vertices_266, vertices_146, vertices_274, vertices_194, vertices_322, vertices_386, vertices_268, vertices_524, vertices_324, vertices_580, vertices_56, vertices_280, vertices_536, vertices_296, vertices_552, vertices_776, vertices_176, vertices_304, vertices_560, vertices_416, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_327), (false, vertices_27), (false, vertices_211), (false, vertices_541), (false, vertices_709), (false, vertices_689), (true, vertices_274), (true, vertices_386), (true, vertices_56), (true, vertices_280), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_304), (true, vertices_416), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 13 else
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_27) then 0 else
  if p.val = (false, vertices_211) then 15 else
  if p.val = (false, vertices_541) then 17 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_56) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_27), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 7 434 146 2
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 1 2 5 7 8 844 268 2
cert_row_4 3 2 4 6 7 8 936 296 2
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 282
cert_cover_2 0 2 0 3 7 26 282 3
cert_coverFacet 1 434
cert_cover_5 1 0 0 3 4 6 146 434 2
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 844
cert_cover_5 3 2 1 2 5 7 268 844 2
cert_coverFacet 4 312
cert_cover_2 4 3 2 4 7 56 312 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 936
cert_cover_5 6 3 2 4 6 7 296 936 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0341

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m14e10q1_0348.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0348

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 213, 405, 837, 313, 625, 902, 410, 682, 298, 716, 568, 216, 600, 149, 69, 261, 49, 81, 273, 289, 545, 577, 769, 42, 138, 266, 290, 546, 386, 642, 770, 196, 580, 388, 644, 772, 56, 88, 152, 280, 536, 296, 552, 200, 584, 648, 560, 208, 592, 400]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_213, vertices_405, vertices_837, vertices_313, vertices_625, vertices_902, vertices_410, vertices_682, vertices_298, vertices_716, vertices_568, vertices_216, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_149, vertices_69, vertices_261, vertices_49, vertices_81, vertices_273, vertices_289, vertices_545, vertices_577, vertices_769, vertices_42, vertices_138, vertices_266, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_196, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_296, vertices_552, vertices_200, vertices_584, vertices_648, vertices_560, vertices_208, vertices_592, vertices_400] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_213), (false, vertices_405), (false, vertices_837), (false, vertices_313), (false, vertices_625), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_386), (true, vertices_642), (true, vertices_644), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_552), (true, vertices_200), (true, vertices_584), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_213) then 16 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_313) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_648) then 12 else
  0
cert_priority
cert_nodeAtPriority_11 42 138 266 386 642 644 88 152 536 552 200 584 648 803 213 405 837 313 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 138 2
cert_row_4 1 0 1 6 7 8 902 386 1
cert_row_4 2 0 2 4 6 8 682 42 3
cert_row_4 3 1 2 5 6 8 716 196 1
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 6 138 410 2
cert_coverFacet 2 682
cert_cover_5 2 2 0 2 4 6 42 682 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 716
cert_cover_5 4 3 1 2 5 6 196 716 1
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0348

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m14e10q1_0349.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0349

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 299, 99, 707, 681, 393, 625, 118, 310, 198, 908, 852, 708, 824, 35, 67, 131, 259, 41, 137, 265, 97, 545, 577, 385, 641, 54, 70, 134, 262, 98, 290, 194, 84, 276, 196, 580, 388, 644, 772, 296, 552, 392, 648, 776, 112, 304, 560, 592, 784, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_299, vertices_99, vertices_707, vertices_681, vertices_393, vertices_625, vertices_118, vertices_310, vertices_198, vertices_908, vertices_852, vertices_708, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_131, vertices_259, vertices_41, vertices_137, vertices_265, vertices_97, vertices_545, vertices_577, vertices_385, vertices_641, vertices_54, vertices_70, vertices_134, vertices_262, vertices_98, vertices_290, vertices_194, vertices_84, vertices_276, vertices_196, vertices_580, vertices_388, vertices_644, vertices_772, vertices_296, vertices_552, vertices_392, vertices_648, vertices_776, vertices_112, vertices_304, vertices_560, vertices_592, vertices_784, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_299), (false, vertices_99), (false, vertices_707), (false, vertices_681), (false, vertices_393), (false, vertices_625), (true, vertices_54), (true, vertices_70), (true, vertices_84), (true, vertices_276), (true, vertices_196), (true, vertices_580), (true, vertices_644), (true, vertices_772), (true, vertices_776), (true, vertices_304), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_99) then 0 else
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (false, vertices_393) then 1 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (true, vertices_54) then 14 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_784) then 11 else
  0
cert_priority
cert_nodeAtPriority_67 1 99 0 393 70 84 276 196 580 644 772 776 304 784 391 54 299 707 681 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 1 2 6 7 8 908 388 1
cert_row_4 2 1 3 5 7 8 852 84 3
cert_row_4 3 2 3 4 7 8 824 296 1
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 0 0 1 3 5 54 118 3
cert_coverFacet 1 310
cert_cover_5 1 0 0 1 3 7 54 310 3
cert_coverFacet 2 198
cert_cover_2 2 1 0 5 6 70 198 3
cert_coverFacet 3 908
cert_cover_5 3 1 1 2 6 7 388 908 1
cert_coverFacet 4 852
cert_cover_5 4 2 1 3 5 7 84 852 3
cert_coverFacet 5 708
cert_cover_2 5 5 1 6 8 196 708 3
cert_coverFacet 6 824
cert_cover_5 6 3 2 3 4 7 296 824 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0349

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m14e10q1_0352.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0352

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 157, 789, 453, 537, 425, 838, 122, 602, 298, 482, 244, 596, 184, 21, 133, 261, 25, 137, 265, 521, 529, 385, 769, 90, 42, 266, 522, 98, 290, 322, 578, 770, 84, 148, 532, 196, 324, 580, 772, 56, 152, 536, 168, 296, 112, 176, 592, 224, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_157, vertices_789, vertices_453, vertices_537, vertices_425, vertices_838, vertices_122, vertices_602, vertices_298, vertices_482, vertices_244, vertices_596, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_25, vertices_137, vertices_265, vertices_521, vertices_529, vertices_385, vertices_769, vertices_90, vertices_42, vertices_266, vertices_522, vertices_98, vertices_290, vertices_322, vertices_578, vertices_770, vertices_84, vertices_148, vertices_532, vertices_196, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_536, vertices_168, vertices_296, vertices_112, vertices_176, vertices_592, vertices_224, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_157), (false, vertices_789), (false, vertices_453), (false, vertices_537), (false, vertices_425), (true, vertices_90), (true, vertices_42), (true, vertices_98), (true, vertices_290), (true, vertices_322), (true, vertices_578), (true, vertices_84), (true, vertices_580), (true, vertices_56), (true, vertices_112), (true, vertices_176), (true, vertices_592), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_157) then 17 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (true, vertices_90) then 15 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_224) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 4 5 6 7 482 98 3
cert_row_4 3 1 3 4 5 6 244 84 2
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 4 90 122 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 8 90 602 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 482
cert_cover_5 4 2 0 4 5 6 98 482 3
cert_coverFacet 5 244
cert_cover_5 5 3 1 3 4 5 84 244 2
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0352

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m14e10q1_0359.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0359

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 397, 181, 805, 561, 465, 782, 602, 458, 338, 236, 620, 240, 624, 37, 133, 261, 49, 145, 273, 529, 545, 385, 769, 74, 266, 522, 82, 274, 530, 322, 770, 108, 140, 268, 524, 164, 548, 772, 200, 584, 392, 112, 176, 560, 208, 336, 592, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_397, vertices_181, vertices_805, vertices_561, vertices_465, vertices_782, vertices_602, vertices_458, vertices_338, vertices_236, vertices_620, vertices_240, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_49, vertices_145, vertices_273, vertices_529, vertices_545, vertices_385, vertices_769, vertices_74, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_322, vertices_770, vertices_108, vertices_140, vertices_268, vertices_524, vertices_164, vertices_548, vertices_772, vertices_200, vertices_584, vertices_392, vertices_112, vertices_176, vertices_560, vertices_208, vertices_336, vertices_592, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_397), (false, vertices_181), (false, vertices_805), (false, vertices_561), (false, vertices_465), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_82), (true, vertices_322), (true, vertices_108), (true, vertices_524), (true, vertices_200), (true, vertices_584), (true, vertices_112), (true, vertices_592), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 18 15 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_397) then 16 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_108) then 17 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
cert_nodeAtPriority_2 0 561 2 74 1 266 3 522 82 322 524 200 584 112 592 224 608 787 397 108 181 805 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 2 3 5 8 602 74 2
cert_row_4 3 0 2 5 6 7 458 74 3
cert_rows
cert_pivot_2 4 1 3 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 602
cert_cover_5 1 2 0 2 3 5 74 602 2
cert_coverFacet 2 458
cert_cover_5 2 3 0 2 5 6 74 458 3
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 236
cert_cover_5 4 0 1 2 4 6 108 236 3
cert_coverFacet 5 620
cert_cover_5 5 0 1 2 4 8 108 620 3
cert_coverFacet 6 240
cert_cover_2 6 4 3 5 6 112 240 3
cert_coverFacet 7 624
cert_cover_2 7 4 3 5 8 112 624 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0359

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m14e10q1_0360.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0360

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 613, 121, 281, 681, 849, 398, 678, 838, 650, 372, 436, 184, 408, 25, 41, 265, 521, 81, 273, 97, 545, 577, 769, 134, 262, 518, 138, 266, 522, 642, 770, 308, 100, 164, 548, 324, 580, 388, 56, 152, 280, 168, 392, 648, 112, 176, 336, 400, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_613, vertices_121, vertices_281, vertices_681, vertices_849, vertices_398, vertices_678, vertices_838, vertices_650, vertices_372, vertices_436, vertices_184, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_521, vertices_81, vertices_273, vertices_97, vertices_545, vertices_577, vertices_769, vertices_134, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_642, vertices_770, vertices_308, vertices_100, vertices_164, vertices_548, vertices_324, vertices_580, vertices_388, vertices_56, vertices_152, vertices_280, vertices_168, vertices_392, vertices_648, vertices_112, vertices_176, vertices_336, vertices_400, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_613), (false, vertices_121), (false, vertices_281), (false, vertices_681), (false, vertices_849), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_642), (true, vertices_308), (true, vertices_164), (true, vertices_324), (true, vertices_388), (true, vertices_152), (true, vertices_392), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_613) then 16 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_308) then 17 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
cert_priority
cert_nodeAtPriority_2 0 281 1 134 2 262 3 518 138 642 164 324 388 152 392 176 400 779 613 308 121 681 849
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 4 7 308
cert_row_4 1 0 1 2 6 7 398 134 2
cert_row_4 2 0 1 4 6 8 678 134 2
cert_row_4 3 0 1 5 7 8 838 262 2
cert_rows
cert_pivot_2 3 2 4 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 134 398 2
cert_coverFacet 1 678
cert_cover_5 1 2 0 1 4 6 134 678 2
cert_coverFacet 2 838
cert_cover_5 2 3 0 1 5 7 262 838 2
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 372
cert_cover_5 4 0 1 3 4 5 308 372 3
cert_coverFacet 5 436
cert_cover_5 5 0 1 3 4 6 308 436 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0360

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m14e10q1_0362.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0362

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 93, 269, 661, 841, 625, 174, 302, 646, 690, 866, 156, 376, 184, 13, 21, 261, 517, 73, 265, 81, 529, 577, 769, 46, 134, 262, 518, 162, 290, 546, 642, 770, 28, 140, 268, 148, 644, 56, 88, 152, 168, 296, 328, 112, 176, 560, 656, 352, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_93, vertices_269, vertices_661, vertices_841, vertices_625, vertices_174, vertices_302, vertices_646, vertices_690, vertices_866, vertices_156, vertices_376, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_261, vertices_517, vertices_73, vertices_265, vertices_81, vertices_529, vertices_577, vertices_769, vertices_46, vertices_134, vertices_262, vertices_518, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_28, vertices_140, vertices_268, vertices_148, vertices_644, vertices_56, vertices_88, vertices_152, vertices_168, vertices_296, vertices_328, vertices_112, vertices_176, vertices_560, vertices_656, vertices_352, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_93), (false, vertices_269), (false, vertices_661), (false, vertices_841), (false, vertices_625), (true, vertices_46), (true, vertices_134), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_140), (true, vertices_56), (true, vertices_152), (true, vertices_168), (true, vertices_296), (true, vertices_176), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_625) then 22 else
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
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
cert_nodeAtPriority_17 269 134 162 290 546 642 140 56 152 168 296 176 352 775 46 93 661 841 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 3 4 6 8 690 162 1
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 2 3 4 5 7 376 56 3
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
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 56 376 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0362

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m14e10q1_0363.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0363

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 653, 213, 837, 153, 281, 369, 678, 186, 314, 650, 866, 628, 180, 69, 133, 517, 25, 137, 265, 521, 81, 145, 273, 321, 769, 58, 138, 266, 522, 162, 290, 546, 642, 770, 52, 84, 148, 164, 548, 580, 644, 152, 280, 648, 112, 176, 304, 352, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_653, vertices_213, vertices_837, vertices_153, vertices_281, vertices_369, vertices_678, vertices_186, vertices_314, vertices_650, vertices_866, vertices_628, vertices_180] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_25, vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_321, vertices_769, vertices_58, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_148, vertices_164, vertices_548, vertices_580, vertices_644, vertices_152, vertices_280, vertices_648, vertices_112, vertices_176, vertices_304, vertices_352, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_653), (false, vertices_213), (false, vertices_837), (false, vertices_153), (false, vertices_281), (false, vertices_369), (true, vertices_58), (true, vertices_138), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_52), (true, vertices_164), (true, vertices_548), (true, vertices_176), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_153) then 0 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_58) then 14 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_608) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_153), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
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
cert_row_2 0 0 2 3 4 58
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 186
cert_cover_5 1 0 0 2 3 6 58 186 3
cert_coverFacet 2 314
cert_cover_5 2 0 0 2 3 7 58 314 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 290 866 2
cert_coverFacet 5 628
cert_cover_5 5 3 1 3 4 5 52 628 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0363

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m14e10q1_0365.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0365

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 613, 569, 241, 401, 961, 174, 558, 406, 838, 154, 538, 484, 184, 49, 145, 273, 529, 97, 545, 193, 577, 385, 769, 46, 134, 262, 518, 26, 138, 522, 146, 274, 530, 770, 100, 164, 548, 324, 580, 388, 56, 152, 536, 168, 552, 176, 400, 224, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_613, vertices_569, vertices_241, vertices_401, vertices_961, vertices_174, vertices_558, vertices_406, vertices_838, vertices_154, vertices_538, vertices_484, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_273, vertices_529, vertices_97, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_46, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_770, vertices_100, vertices_164, vertices_548, vertices_324, vertices_580, vertices_388, vertices_56, vertices_152, vertices_536, vertices_168, vertices_552, vertices_176, vertices_400, vertices_224, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_613), (false, vertices_569), (false, vertices_241), (false, vertices_401), (false, vertices_961), (true, vertices_46), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_164), (true, vertices_324), (true, vertices_388), (true, vertices_152), (true, vertices_168)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_46) then 15 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_146) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_168) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 1 3 6 7 406 134 2
cert_row_4 2 0 1 5 7 8 838 262 2
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 0 0 1 2 6 46 174 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 8 46 558 3
cert_coverFacet 2 406
cert_cover_5 2 1 0 1 3 6 134 406 2
cert_coverFacet 3 838
cert_cover_5 3 2 0 1 5 7 262 838 2
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 538
cert_cover_2 5 2 0 3 8 26 538 3
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 100 484 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0365

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m14e10q1_0366.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0366

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 541, 409, 297, 721, 929, 110, 526, 598, 738, 284, 364, 340, 496, 25, 41, 265, 521, 145, 529, 289, 545, 385, 641, 14, 70, 518, 42, 522, 98, 546, 578, 28, 108, 268, 524, 84, 276, 532, 324, 280, 296, 208, 336, 592, 400, 224, 352, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_541, vertices_409, vertices_297, vertices_721, vertices_929, vertices_110, vertices_526, vertices_598, vertices_738, vertices_284, vertices_364, vertices_340, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_521, vertices_145, vertices_529, vertices_289, vertices_545, vertices_385, vertices_641, vertices_14, vertices_70, vertices_518, vertices_42, vertices_522, vertices_98, vertices_546, vertices_578, vertices_28, vertices_108, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_324, vertices_280, vertices_296, vertices_208, vertices_336, vertices_592, vertices_400, vertices_224, vertices_352, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_541), (false, vertices_409), (false, vertices_297), (false, vertices_721), (false, vertices_929), (true, vertices_14), (true, vertices_70), (true, vertices_518), (true, vertices_98), (true, vertices_578), (true, vertices_108), (true, vertices_268), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_336), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 14 else
  if p.val = (false, vertices_541) then 16 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_721) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_108) then 17 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 1 3 5 8 598 70 2
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 3 4 5 6 7 496 208 1
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 4 14 110 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 598
cert_cover_5 2 1 0 1 3 5 70 598 2
cert_coverFacet 3 738
cert_cover_5 3 2 0 4 5 6 98 738 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 364
cert_cover_5 5 0 1 2 4 7 108 364 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 208 496 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0366

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m14e10q1_0383.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0383

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 659, 163, 291, 597, 453, 217, 417, 810, 674, 348, 796, 696, 488, 35, 131, 259, 515, 69, 261, 517, 81, 145, 529, 161, 289, 193, 385, 162, 290, 546, 642, 770, 284, 84, 532, 324, 772, 88, 152, 536, 168, 296, 552, 200, 328, 776, 656, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_659, vertices_163, vertices_291, vertices_597, vertices_453, vertices_217, vertices_417, vertices_810, vertices_674, vertices_348, vertices_796, vertices_696, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_69, vertices_261, vertices_517, vertices_81, vertices_145, vertices_529, vertices_161, vertices_289, vertices_193, vertices_385, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_284, vertices_84, vertices_532, vertices_324, vertices_772, vertices_88, vertices_152, vertices_536, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_776, vertices_656, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_659), (false, vertices_163), (false, vertices_291), (false, vertices_597), (false, vertices_453), (false, vertices_217), (false, vertices_417), (true, vertices_546), (true, vertices_284), (true, vertices_536), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_776), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_659) then 13 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_291) then 1 else
  if p.val = (false, vertices_597) then 15 else
  if p.val = (false, vertices_453) then 16 else
  if p.val = (false, vertices_217) then 19 else
  if p.val = (false, vertices_417) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_284) then 17 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_284), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 7 284
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_4 2 2 3 4 6 8 696 152 2
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 1 0 3 2
cert_heightProof 4
cert_coverFacet 0 810
cert_cover_5 0 1 0 2 4 7 290 810 1
cert_coverFacet 1 674
cert_cover_2 1 4 0 6 8 162 674 3
cert_coverFacet 2 348
cert_cover_5 2 0 1 2 3 5 284 348 3
cert_coverFacet 3 796
cert_cover_5 3 0 1 2 3 8 284 796 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 152 696 2
cert_coverFacet 5 488
cert_cover_5 5 3 2 4 5 6 168 488 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0383

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m14e10q1_0384.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0384

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 779, 659, 227, 677, 617, 790, 210, 338, 812, 436, 660, 488, 464, 267, 67, 131, 515, 73, 521, 97, 161, 545, 641, 82, 146, 274, 530, 194, 322, 770, 148, 276, 532, 164, 292, 548, 644, 772, 104, 296, 552, 328, 776, 208, 336, 400, 656, 224, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_779, vertices_659, vertices_227, vertices_677, vertices_617, vertices_790, vertices_210, vertices_338, vertices_812, vertices_436, vertices_660, vertices_488, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_267, vertices_67, vertices_131, vertices_515, vertices_73, vertices_521, vertices_97, vertices_161, vertices_545, vertices_641, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_770, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_104, vertices_296, vertices_552, vertices_328, vertices_776, vertices_208, vertices_336, vertices_400, vertices_656, vertices_224, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_779), (false, vertices_659), (false, vertices_227), (false, vertices_677), (false, vertices_617), (true, vertices_82), (true, vertices_274), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_772), (true, vertices_296), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 13 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_659) then 20 else
  if p.val = (false, vertices_227) then 21 else
  if p.val = (false, vertices_677) then 14 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
cert_priority
cert_nodeAtPriority 1 82 2 274 0 148 276 532 292 772 296 208 336 400 416 448 677 331 779 617 659 227
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_4 1 1 2 4 7 8 812 292 1
cert_row_4 2 1 3 4 6 7 436 148 2
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 210
cert_cover_2 1 3 0 5 6 82 210 3
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 812
cert_cover_5 3 1 1 2 4 7 292 812 1
cert_coverFacet 4 436
cert_cover_5 4 2 1 3 4 6 148 436 2
cert_coverFacet 5 660
cert_cover_2 5 3 1 6 8 148 660 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 104 488 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0384

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m14e10q1_0385.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0385

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 781, 677, 185, 409, 617, 710, 774, 842, 466, 376, 624, 688, 720, 133, 261, 517, 153, 41, 265, 521, 161, 545, 385, 134, 262, 518, 194, 322, 578, 386, 770, 644, 772, 56, 280, 104, 328, 584, 776, 112, 176, 560, 208, 336, 592, 400, 656, 608, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_781, vertices_677, vertices_185, vertices_409, vertices_617, vertices_710, vertices_774, vertices_842, vertices_466, vertices_376, vertices_624, vertices_688, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_153, vertices_41, vertices_265, vertices_521, vertices_161, vertices_545, vertices_385, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_644, vertices_772, vertices_56, vertices_280, vertices_104, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_336, vertices_592, vertices_400, vertices_656, vertices_608, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_781), (false, vertices_677), (false, vertices_185), (false, vertices_409), (false, vertices_617), (true, vertices_518), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_328), (true, vertices_112), (true, vertices_560), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_185) then 19 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
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
cert_row_4 0 0 1 5 6 8 710 134 2
cert_row_4 1 0 2 5 7 8 842 322 1
cert_row_4 2 0 3 5 6 7 466 194 1
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 0 0 1 5 6 134 710 2
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 842
cert_cover_5 2 1 0 2 5 7 322 842 1
cert_coverFacet 3 466
cert_cover_5 3 2 0 3 5 6 194 466 1
cert_coverFacet 4 376
cert_cover_5 4 3 2 3 4 5 56 376 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 688
cert_cover_2 6 4 3 6 8 176 688 3
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0385

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m14e10q1_0386.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0386

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 395, 163, 653, 269, 613, 721, 225, 626, 818, 466, 226, 812, 920, 35, 131, 259, 13, 37, 261, 517, 137, 265, 97, 161, 193, 577, 641, 562, 82, 274, 98, 162, 290, 194, 386, 268, 524, 292, 548, 392, 648, 776, 208, 592, 400, 656, 784, 224, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_395, vertices_163, vertices_653, vertices_269, vertices_613, vertices_721, vertices_225, vertices_626, vertices_818, vertices_466, vertices_226, vertices_812, vertices_920] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_13, vertices_37, vertices_261, vertices_517, vertices_137, vertices_265, vertices_97, vertices_161, vertices_193, vertices_577, vertices_641, vertices_562, vertices_82, vertices_274, vertices_98, vertices_162, vertices_290, vertices_194, vertices_386, vertices_268, vertices_524, vertices_292, vertices_548, vertices_392, vertices_648, vertices_776, vertices_208, vertices_592, vertices_400, vertices_656, vertices_784, vertices_224, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_395), (false, vertices_163), (false, vertices_653), (false, vertices_269), (false, vertices_613), (false, vertices_721), (false, vertices_225), (true, vertices_562), (true, vertices_82), (true, vertices_274), (true, vertices_98), (true, vertices_194), (true, vertices_776), (true, vertices_400), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 12 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_269) then 1 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (false, vertices_225) then 2 else
  if p.val = (true, vertices_562) then 14 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_562), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 18 => Sum.inl 2
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
cert_row_4 0 0 3 5 6 7 466 82 3
cert_row_2 1 0 3 4 8 562
cert_row_4 2 1 2 4 7 8 812 268 2
cert_row_4 3 2 3 6 7 8 920 392 1
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 626
cert_cover_5 0 1 0 3 4 5 562 626 3
cert_coverFacet 1 818
cert_cover_5 1 1 0 3 4 7 562 818 3
cert_coverFacet 2 466
cert_cover_5 2 0 0 3 5 6 82 466 3
cert_coverFacet 3 226
cert_cover_2 3 4 0 5 6 98 226 3
cert_coverFacet 4 812
cert_cover_5 4 2 1 2 4 7 268 812 2
cert_coverFacet 5 920
cert_cover_5 5 3 2 3 6 7 392 920 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0386

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m14e10q1_0387.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0387

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 309, 405, 229, 713, 625, 154, 282, 842, 650, 818, 460, 868, 408, 277, 37, 133, 49, 145, 529, 97, 193, 577, 641, 26, 138, 266, 522, 146, 274, 530, 642, 770, 100, 292, 196, 324, 388, 152, 280, 200, 328, 584, 392, 648, 304, 560, 400, 608, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_309, vertices_405, vertices_229, vertices_713, vertices_625, vertices_154, vertices_282, vertices_842, vertices_650, vertices_818, vertices_460, vertices_868, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_277, vertices_37, vertices_133, vertices_49, vertices_145, vertices_529, vertices_97, vertices_193, vertices_577, vertices_641, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_100, vertices_292, vertices_196, vertices_324, vertices_388, vertices_152, vertices_280, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_304, vertices_560, vertices_400, vertices_608, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_309), (false, vertices_405), (false, vertices_229), (false, vertices_713), (false, vertices_625), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_770), (true, vertices_324), (true, vertices_152), (true, vertices_280), (true, vertices_328), (true, vertices_392), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_309) then 16 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
cert_nodeAtPriority_11 26 138 266 522 274 770 324 152 280 328 392 800 832 659 309 405 229 713 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 7 8 818 274 2
cert_row_4 1 0 2 5 7 8 842 266 2
cert_row_4 2 1 2 5 6 7 460 196 1
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 154
cert_cover_2 0 2 0 3 6 26 154 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 842
cert_cover_5 2 1 0 2 5 7 266 842 2
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 818
cert_cover_5 4 0 0 3 4 7 274 818 2
cert_coverFacet 5 460
cert_cover_5 5 2 1 2 5 6 196 460 1
cert_coverFacet 6 868
cert_cover_5 6 3 1 4 5 7 100 868 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0387

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2343 : Certifies 2343 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0285.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2344 : Certifies 2344 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0303.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2345 : Certifies 2345 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0304.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2346 : Certifies 2346 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0305.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2347 : Certifies 2347 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0306.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2348 : Certifies 2348 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0307.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2349 : Certifies 2349 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0308.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2350 : Certifies 2350 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0312.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2351 : Certifies 2351 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0313.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2352 : Certifies 2352 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0314.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2353 : Certifies 2353 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0315.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2354 : Certifies 2354 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0319.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2355 : Certifies 2355 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0324.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2356 : Certifies 2356 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0338.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2357 : Certifies 2357 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0340.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2358 : Certifies 2358 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0341.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2359 : Certifies 2359 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0348.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2360 : Certifies 2360 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0349.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2361 : Certifies 2361 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0352.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2362 : Certifies 2362 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0359.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2363 : Certifies 2363 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0360.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2364 : Certifies 2364 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0362.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2365 : Certifies 2365 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0363.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2366 : Certifies 2366 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0365.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2367 : Certifies 2367 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0366.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2368 : Certifies 2368 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0383.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2369 : Certifies 2369 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0384.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2370 : Certifies 2370 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0385.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2371 : Certifies 2371 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0386.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2372 : Certifies 2372 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0387.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B077 (j : Fin 30) :
    Certifies (2343 + j.val) := by
  fin_cases j
  · exact projection_2343
  · exact projection_2344
  · exact projection_2345
  · exact projection_2346
  · exact projection_2347
  · exact projection_2348
  · exact projection_2349
  · exact projection_2350
  · exact projection_2351
  · exact projection_2352
  · exact projection_2353
  · exact projection_2354
  · exact projection_2355
  · exact projection_2356
  · exact projection_2357
  · exact projection_2358
  · exact projection_2359
  · exact projection_2360
  · exact projection_2361
  · exact projection_2362
  · exact projection_2363
  · exact projection_2364
  · exact projection_2365
  · exact projection_2366
  · exact projection_2367
  · exact projection_2368
  · exact projection_2369
  · exact projection_2370
  · exact projection_2371
  · exact projection_2372

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
