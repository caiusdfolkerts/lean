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
/- Source: ProjectionCertificates/P0_231.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_231

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 229, 613, 601, 809, 457, 166, 806, 646, 794, 466, 658, 724, 344, 101, 73, 265, 521, 161, 289, 545, 193, 577, 385, 38, 134, 518, 146, 274, 530, 162, 290, 386, 642, 770, 164, 548, 196, 580, 644, 88, 280, 536, 328, 776, 208, 336, 592, 656, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_229, vertices_613, vertices_601, vertices_809, vertices_457, vertices_166, vertices_806, vertices_646, vertices_794, vertices_466, vertices_658, vertices_724, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_101, vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_38, vertices_134, vertices_518, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_88, vertices_280, vertices_536, vertices_328, vertices_776, vertices_208, vertices_336, vertices_592, vertices_656, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_229), (false, vertices_613), (false, vertices_601), (false, vertices_809), (false, vertices_457), (true, vertices_38), (true, vertices_134), (true, vertices_518), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_642), (true, vertices_770), (true, vertices_644), (true, vertices_280), (true, vertices_208), (true, vertices_336), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 14 else
  if p.val = (false, vertices_229) then 16 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_656) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_4 0 0 1 7 8 4 806 518 2
cert_row_4 1 0 3 7 8 2 794 274 3
cert_row_4 2 3 5 6 7 0 466 208 3
cert_row_4 3 3 5 6 8 1 724 208 3
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 166
cert_cover_2 0 1 0 4 6 38 166 3
cert_coverFacet 1 806
cert_cover_5 1 0 0 1 4 7 38 806 3
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 794
cert_cover_5 3 1 0 2 3 7 274 794 1
cert_coverFacet 4 466
cert_cover_5 4 2 0 3 5 6 146 466 2
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 196 724 1
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_231

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/P0_232.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_232

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 341, 101, 805, 457, 737, 790, 346, 666, 394, 92, 540, 236, 684, 37, 69, 261, 97, 545, 193, 321, 385, 641, 769, 26, 138, 266, 274, 530, 386, 642, 770, 28, 172, 76, 524, 84, 276, 532, 100, 548, 772, 88, 536, 200, 328, 392, 648, 336, 224, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_341, vertices_101, vertices_805, vertices_457, vertices_737, vertices_790, vertices_346, vertices_666, vertices_394, vertices_92, vertices_540, vertices_236, vertices_684] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_261, vertices_97, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_28, vertices_172, vertices_76, vertices_524, vertices_84, vertices_276, vertices_532, vertices_100, vertices_548, vertices_772, vertices_88, vertices_536, vertices_200, vertices_328, vertices_392, vertices_648, vertices_336, vertices_224, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_341), (false, vertices_101), (false, vertices_805), (false, vertices_457), (false, vertices_737), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_274), (true, vertices_530), (true, vertices_28), (true, vertices_172), (true, vertices_76), (true, vertices_524), (true, vertices_532), (true, vertices_88), (true, vertices_536), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 18 15 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_101) then 12 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_457) then 16 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_172) then 17 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_648) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_101), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_172), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
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
cert_row_4 0 0 2 3 7 5 346 26 3
cert_row_4 1 0 1 3 8 7 790 530 1
cert_row_4 2 2 3 6 8 0 666 536 2
cert_row_2 3 2 4 6 1 172
cert_rows
cert_pivot_2 5 7 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 274 790 1
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 5 26 346 3
cert_coverFacet 2 666
cert_cover_5 2 2 0 2 3 6 26 666 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 92
cert_cover_2 4 2 1 3 5 28 92 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 236
cert_cover_5 6 3 1 2 4 5 172 236 3
cert_coverFacet 7 684
cert_cover_5 7 3 1 2 4 8 172 684 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_232

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/P0_233.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_233

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 837, 361, 169, 713, 689, 566, 342, 774, 426, 178, 466, 724, 456, 41, 73, 137, 161, 289, 545, 321, 577, 641, 769, 22, 262, 518, 50, 338, 146, 162, 290, 546, 386, 770, 84, 532, 324, 580, 772, 168, 296, 200, 328, 392, 176, 560, 208, 656, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_837, vertices_361, vertices_169, vertices_713, vertices_689, vertices_566, vertices_342, vertices_774, vertices_426, vertices_178, vertices_466, vertices_724, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_137, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_641, vertices_769, vertices_22, vertices_262, vertices_518, vertices_50, vertices_338, vertices_146, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_84, vertices_532, vertices_324, vertices_580, vertices_772, vertices_168, vertices_296, vertices_200, vertices_328, vertices_392, vertices_176, vertices_560, vertices_208, vertices_656, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_837), (false, vertices_361), (false, vertices_169), (false, vertices_713), (false, vertices_689), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_338), (true, vertices_146), (true, vertices_162), (true, vertices_386), (true, vertices_84), (true, vertices_532), (true, vertices_392), (true, vertices_208), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_169) then 12 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_338) then 15 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
cert_priority
cert_nodeAtPriority_56 22 262 518 50 146 162 386 84 532 392 208 448 169 803 338 837 361 713 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 6 7 2 426 162 3
cert_row_4 1 0 1 3 8 4 566 22 3
cert_row_4 2 3 5 6 8 1 724 208 3
cert_row_2 3 3 5 7 0 338
cert_rows
cert_pivot_2 2 4 1 0
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 1 0 1 3 4 22 566 3
cert_coverFacet 1 342
cert_cover_5 1 3 0 1 3 5 22 342 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 426
cert_cover_5 3 0 0 2 4 6 162 426 1
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 466
cert_cover_5 5 3 0 3 5 6 338 466 3
cert_coverFacet 6 724
cert_cover_5 6 2 1 3 5 6 84 724 3
cert_coverFacet 7 456
cert_cover_2 7 5 2 6 7 200 456 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_233

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/P0_246.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_246

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 805, 713, 913, 481, 30, 110, 790, 550, 666, 586, 284, 364, 472, 97, 289, 545, 193, 577, 385, 641, 769, 14, 22, 38, 518, 26, 74, 522, 530, 98, 546, 578, 28, 108, 268, 276, 292, 548, 772, 152, 280, 200, 328, 584, 648, 400, 656, 784, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_805, vertices_713, vertices_913, vertices_481, vertices_30, vertices_110, vertices_790, vertices_550, vertices_666, vertices_586, vertices_284, vertices_364, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_97, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_38, vertices_518, vertices_26, vertices_74, vertices_522, vertices_530, vertices_98, vertices_546, vertices_578, vertices_28, vertices_108, vertices_268, vertices_276, vertices_292, vertices_548, vertices_772, vertices_152, vertices_280, vertices_200, vertices_328, vertices_584, vertices_648, vertices_400, vertices_656, vertices_784, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_805), (false, vertices_713), (false, vertices_913), (false, vertices_481), (true, vertices_14), (true, vertices_22), (true, vertices_38), (true, vertices_518), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_530), (true, vertices_28), (true, vertices_108), (true, vertices_268), (true, vertices_276), (true, vertices_152), (true, vertices_280), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 15 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_913) then 22 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_108) then 18 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_328) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 4 108
cert_row_4 1 0 3 7 8 1 790 530 2
cert_row_4 2 2 3 6 8 0 666 152 3
cert_row_4 3 3 5 6 7 2 472 400 1
cert_rows
cert_pivot_2 4 1 0 2
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 110
cert_cover_5 1 0 0 1 2 4 14 110 3
cert_coverFacet 2 790
cert_cover_5 2 1 0 1 3 7 22 790 3
cert_coverFacet 3 550
cert_cover_2 3 1 0 4 8 38 550 3
cert_coverFacet 4 666
cert_cover_5 4 2 0 2 3 6 26 666 3
cert_coverFacet 5 586
cert_cover_2 5 2 0 5 8 74 586 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 364
cert_cover_5 7 0 1 2 4 7 108 364 3
cert_coverFacet 8 472
cert_cover_5 8 3 2 3 5 6 152 472 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_246

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/P0_247.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_247

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 901, 313, 689, 481, 590, 122, 282, 778, 626, 460, 780, 740, 360, 49, 273, 529, 161, 289, 385, 641, 769, 26, 74, 266, 522, 114, 274, 530, 578, 770, 76, 268, 524, 196, 580, 388, 644, 772, 56, 280, 104, 296, 328, 776, 560, 224, 352, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_901, vertices_313, vertices_689, vertices_481, vertices_590, vertices_122, vertices_282, vertices_778, vertices_626, vertices_460, vertices_780, vertices_740, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_273, vertices_529, vertices_161, vertices_289, vertices_385, vertices_641, vertices_769, vertices_26, vertices_74, vertices_266, vertices_522, vertices_114, vertices_274, vertices_530, vertices_578, vertices_770, vertices_76, vertices_268, vertices_524, vertices_196, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_280, vertices_104, vertices_296, vertices_328, vertices_776, vertices_560, vertices_224, vertices_352, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_901), (false, vertices_313), (false, vertices_689), (false, vertices_481), (true, vertices_26), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_114), (true, vertices_578), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_196), (true, vertices_580), (true, vertices_104), (true, vertices_328), (true, vertices_776), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_901) then 18 else
  if p.val = (false, vertices_313) then 20 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_114) then 16 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_114), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 5 6 7 460 76 3
cert_row_4 1 0 1 5 8 2 590 578 1
cert_row_4 2 4 5 6 8 1 740 224 3
cert_row_2 3 3 4 5 0 114
cert_rows
cert_pivot_2 7 2 1 0
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 74 590 1
cert_coverFacet 1 122
cert_cover_5 1 3 0 2 3 4 26 122 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 626
cert_cover_5 4 3 0 3 4 8 114 626 3
cert_coverFacet 5 460
cert_cover_5 5 0 1 2 5 6 76 460 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 740
cert_cover_5 7 2 1 4 5 6 196 740 1
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_247

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/P0_248.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_248

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 147, 787, 781, 213, 581, 625, 242, 306, 418, 620, 460, 824, 488, 19, 131, 259, 69, 133, 261, 517, 81, 145, 529, 577, 769, 50, 146, 274, 162, 290, 386, 76, 268, 524, 196, 580, 388, 104, 296, 552, 456, 776, 112, 304, 560, 208, 784, 224, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_147, vertices_787, vertices_781, vertices_213, vertices_581, vertices_625, vertices_242, vertices_306, vertices_418, vertices_620, vertices_460, vertices_824, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_69, vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_529, vertices_577, vertices_769, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_386, vertices_76, vertices_268, vertices_524, vertices_196, vertices_580, vertices_388, vertices_104, vertices_296, vertices_552, vertices_456, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_784, vertices_224, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_147), (false, vertices_787), (false, vertices_781), (false, vertices_213), (false, vertices_581), (false, vertices_625), (true, vertices_50), (true, vertices_162), (true, vertices_290), (true, vertices_76), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_456), (true, vertices_304), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_147) then 10 else
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_581) then 11 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_456) then 19 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_416) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_456), by decide +kernel⟩
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
cert_row_4 0 3 4 5 6 0 242 112 3
cert_row_4 1 2 4 5 8 1 620 104 3
cert_row_4 2 2 4 7 8 3 824 296 3
cert_row_2 3 5 6 7 2 456
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 242
cert_cover_5 0 0 0 3 4 5 50 242 3
cert_coverFacet 1 306
cert_cover_2 1 3 0 4 7 50 306 3
cert_coverFacet 2 418
cert_cover_2 2 4 0 6 7 162 418 3
cert_coverFacet 3 620
cert_cover_5 3 1 1 2 4 5 76 620 2
cert_coverFacet 4 460
cert_cover_5 4 3 1 2 5 6 76 460 3
cert_coverFacet 5 824
cert_cover_5 5 2 2 3 4 7 296 824 1
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 104 488 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_248

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/P0_249.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_249

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 837, 665, 617, 457, 785, 790, 614, 166, 390, 682, 658, 364, 428, 73, 137, 521, 145, 273, 529, 321, 577, 385, 769, 38, 134, 262, 518, 146, 274, 530, 162, 546, 386, 642, 300, 100, 164, 324, 580, 388, 772, 104, 168, 552, 328, 392, 648, 656, 784, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_837, vertices_665, vertices_617, vertices_457, vertices_785, vertices_790, vertices_614, vertices_166, vertices_390, vertices_682, vertices_658, vertices_364, vertices_428] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_521, vertices_145, vertices_273, vertices_529, vertices_321, vertices_577, vertices_385, vertices_769, vertices_38, vertices_134, vertices_262, vertices_518, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_386, vertices_642, vertices_300, vertices_100, vertices_164, vertices_324, vertices_580, vertices_388, vertices_772, vertices_104, vertices_168, vertices_552, vertices_328, vertices_392, vertices_648, vertices_656, vertices_784, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_837), (false, vertices_665), (false, vertices_617), (false, vertices_457), (false, vertices_785), (true, vertices_38), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_642), (true, vertices_300), (true, vertices_100), (true, vertices_164), (true, vertices_388), (true, vertices_168)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 14 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_665) then 19 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_785) then 12 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_300) then 17 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_168) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_300), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
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
cert_row_4 0 0 1 7 8 3 790 262 3
cert_row_4 1 0 1 4 8 5 614 38 3
cert_row_4 2 2 4 6 8 0 682 168 3
cert_row_2 3 2 4 7 1 300
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 262 790 2
cert_coverFacet 1 614
cert_cover_5 1 1 0 1 4 5 38 614 3
cert_coverFacet 2 166
cert_cover_2 2 1 0 4 6 38 166 3
cert_coverFacet 3 390
cert_cover_2 3 1 0 6 7 134 390 3
cert_coverFacet 4 682
cert_cover_5 4 2 0 2 4 6 162 682 1
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 364
cert_cover_5 6 3 1 2 4 5 300 364 3
cert_coverFacet 7 428
cert_cover_5 7 3 1 2 4 6 300 428 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_249

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/P0_250.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_250

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 397, 713, 777, 625, 465, 782, 566, 422, 114, 338, 482, 652, 740, 137, 265, 521, 81, 273, 529, 193, 577, 385, 769, 38, 262, 518, 50, 82, 274, 530, 98, 418, 322, 770, 140, 268, 524, 164, 548, 388, 644, 648, 776, 112, 560, 336, 224, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_397, vertices_713, vertices_777, vertices_625, vertices_465, vertices_782, vertices_566, vertices_422, vertices_114, vertices_338, vertices_482, vertices_652, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_81, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_769, vertices_38, vertices_262, vertices_518, vertices_50, vertices_82, vertices_274, vertices_530, vertices_98, vertices_418, vertices_322, vertices_770, vertices_140, vertices_268, vertices_524, vertices_164, vertices_548, vertices_388, vertices_644, vertices_648, vertices_776, vertices_112, vertices_560, vertices_336, vertices_224, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_397), (false, vertices_713), (false, vertices_777), (false, vertices_625), (false, vertices_465), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_82), (true, vertices_98), (true, vertices_418), (true, vertices_322), (true, vertices_524), (true, vertices_164), (true, vertices_548), (true, vertices_644), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_777) then 12 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_418) then 15 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_418), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 7 8 2 782 262 3
cert_row_4 1 0 1 4 8 3 566 38 3
cert_row_4 2 4 5 6 8 1 740 224 3
cert_row_2 3 4 6 7 0 418
cert_rows
cert_pivot_2 2 3 1 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 262 782 2
cert_coverFacet 1 566
cert_cover_5 1 1 0 1 3 4 38 566 2
cert_coverFacet 2 422
cert_cover_5 2 3 0 1 4 6 38 422 3
cert_coverFacet 3 114
cert_cover_2 3 3 0 4 5 50 114 3
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 482
cert_cover_5 5 3 0 4 5 6 98 482 3
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 740
cert_cover_5 7 2 1 4 5 6 164 740 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_250

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/P0_251.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_251

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 709, 313, 617, 457, 433, 790, 454, 646, 570, 178, 402, 844, 792, 41, 73, 265, 305, 161, 545, 193, 577, 385, 641, 134, 262, 518, 50, 146, 274, 530, 162, 546, 386, 642, 196, 324, 580, 644, 772, 56, 280, 536, 552, 328, 584, 776, 176, 400, 784, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_709, vertices_313, vertices_617, vertices_457, vertices_433, vertices_790, vertices_454, vertices_646, vertices_570, vertices_178, vertices_402, vertices_844, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_305, vertices_161, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_134, vertices_262, vertices_518, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_386, vertices_642, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_56, vertices_280, vertices_536, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_400, vertices_784, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_709), (false, vertices_313), (false, vertices_617), (false, vertices_457), (false, vertices_433), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_324), (true, vertices_772), (true, vertices_536), (true, vertices_776), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 17 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_709) then 16 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_784) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 7 6 454 262 2
cert_row_4 1 0 2 3 8 4 570 530 1
cert_row_4 2 1 3 7 8 0 790 772 1
cert_row_4 3 2 5 7 8 1 844 328 3
cert_rows
cert_pivot_2 6 4 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 262 790 2
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 134 454 2
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 570
cert_cover_5 3 1 0 2 3 4 50 570 1
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 844
cert_cover_5 6 3 1 2 5 7 324 844 1
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_251

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/P0_252.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_252

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 397, 525, 709, 313, 617, 369, 902, 570, 114, 338, 786, 738, 796, 13, 133, 517, 41, 265, 521, 305, 97, 193, 321, 577, 385, 50, 82, 274, 530, 98, 546, 194, 322, 386, 642, 770, 268, 524, 388, 644, 772, 56, 280, 536, 552, 112, 336, 784, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_397, vertices_525, vertices_709, vertices_313, vertices_617, vertices_369, vertices_902, vertices_570, vertices_114, vertices_338, vertices_786, vertices_738, vertices_796] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_41, vertices_265, vertices_521, vertices_305, vertices_97, vertices_193, vertices_321, vertices_577, vertices_385, vertices_50, vertices_82, vertices_274, vertices_530, vertices_98, vertices_546, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_268, vertices_524, vertices_388, vertices_644, vertices_772, vertices_56, vertices_280, vertices_536, vertices_552, vertices_112, vertices_336, vertices_784, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_397), (false, vertices_525), (false, vertices_709), (false, vertices_313), (false, vertices_617), (false, vertices_369), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_546), (true, vertices_642), (true, vertices_770), (true, vertices_772), (true, vertices_536), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 13 else
  if p.val = (false, vertices_397) then 15 else
  if p.val = (false, vertices_525) then 11 else
  if p.val = (false, vertices_709) then 16 else
  if p.val = (false, vertices_313) then 20 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_784) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 6 8 5 738 546 2
cert_row_4 1 0 1 7 8 6 902 770 1
cert_row_4 2 2 3 4 8 0 570 56 3
cert_row_4 3 2 3 7 8 1 796 280 3
cert_rows
cert_pivot_2 5 6 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 570
cert_cover_5 1 2 0 2 3 4 50 570 1
cert_coverFacet 2 114
cert_cover_2 2 3 0 4 5 50 114 3
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 738
cert_cover_5 5 0 0 4 5 6 98 738 3
cert_coverFacet 6 796
cert_cover_5 6 3 1 2 3 7 268 796 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_252

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/P0_255.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_255

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [405, 665, 617, 425, 817, 206, 654, 790, 326, 586, 866, 660, 484, 232, 41, 137, 521, 145, 273, 529, 289, 545, 385, 142, 70, 262, 518, 74, 522, 322, 578, 770, 148, 276, 532, 196, 324, 388, 644, 104, 168, 200, 584, 648, 656, 784, 224, 352, 608, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_405, vertices_665, vertices_617, vertices_425, vertices_817, vertices_206, vertices_654, vertices_790, vertices_326, vertices_586, vertices_866, vertices_660, vertices_484, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_521, vertices_145, vertices_273, vertices_529, vertices_289, vertices_545, vertices_385, vertices_142, vertices_70, vertices_262, vertices_518, vertices_74, vertices_522, vertices_322, vertices_578, vertices_770, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_388, vertices_644, vertices_104, vertices_168, vertices_200, vertices_584, vertices_648, vertices_656, vertices_784, vertices_224, vertices_352, vertices_608, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_405), (false, vertices_665), (false, vertices_617), (false, vertices_425), (false, vertices_817), (true, vertices_142), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_74), (true, vertices_522), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_532), (true, vertices_196), (true, vertices_324), (true, vertices_644), (true, vertices_200), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 19 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_142) then 16 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(true, vertices_142), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 7 8 3 790 262 3
cert_row_4 1 0 4 5 7 8 866 322 1
cert_row_4 2 1 5 6 7 4 484 196 3
cert_row_2 3 1 2 6 0 142
cert_rows
cert_pivot_2 3 8 4 0
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 3 0 1 2 5 142 206 3
cert_coverFacet 1 654
cert_cover_5 1 3 0 1 2 8 142 654 3
cert_coverFacet 2 790
cert_cover_5 2 0 0 1 3 7 262 790 2
cert_coverFacet 3 326
cert_cover_2 3 1 0 5 7 70 326 3
cert_coverFacet 4 586
cert_cover_2 4 2 0 5 8 74 586 3
cert_coverFacet 5 866
cert_cover_5 5 1 0 4 5 7 322 866 1
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 484
cert_cover_5 7 2 1 4 5 6 196 484 1
cert_coverFacet 8 232
cert_cover_2 8 4 2 5 6 104 232 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_255

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/P0_256.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_256

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 405, 805, 709, 425, 225, 790, 346, 362, 722, 802, 660, 248, 408, 133, 261, 517, 97, 161, 289, 545, 193, 577, 385, 330, 82, 274, 530, 98, 290, 546, 578, 770, 148, 276, 532, 644, 772, 88, 152, 280, 104, 168, 296, 392, 208, 400, 656, 224, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_405, vertices_805, vertices_709, vertices_425, vertices_225, vertices_790, vertices_346, vertices_362, vertices_722, vertices_802, vertices_660, vertices_248, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_330, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_148, vertices_276, vertices_532, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_392, vertices_208, vertices_400, vertices_656, vertices_224, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_405), (false, vertices_805), (false, vertices_709), (false, vertices_425), (false, vertices_225), (true, vertices_330), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_770), (true, vertices_532), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_104), (true, vertices_208), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 14 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_225) then 12 else
  if p.val = (true, vertices_330) then 15 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_656) then 11 else
  0
cert_priority
cert_nodeAtPriority_57 82 274 530 290 770 532 88 152 280 104 208 656 225 611 330 405 805 709 425
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 7 8 1 790 274 3
cert_row_4 1 0 3 5 6 8 722 82 3
cert_row_4 2 2 4 5 6 3 248 104 3
cert_row_2 3 2 5 7 0 330
cert_rows
cert_pivot_2 1 8 3 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 346
cert_cover_5 1 3 0 2 3 5 330 346 2
cert_coverFacet 2 362
cert_cover_5 2 3 0 2 4 5 330 362 2
cert_coverFacet 3 722
cert_cover_5 3 1 0 3 5 6 82 722 3
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 660
cert_cover_2 5 3 1 6 8 148 660 3
cert_coverFacet 6 248
cert_cover_5 6 2 2 3 4 5 88 248 2
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_256

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/P0_257.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_257

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 805, 793, 425, 713, 566, 86, 422, 454, 602, 706, 348, 788, 456, 137, 265, 521, 161, 289, 545, 641, 769, 22, 38, 70, 390, 82, 530, 162, 546, 194, 578, 642, 84, 276, 532, 292, 548, 324, 772, 88, 280, 536, 200, 328, 584, 392, 784, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_805, vertices_793, vertices_425, vertices_713, vertices_566, vertices_86, vertices_422, vertices_454, vertices_602, vertices_706, vertices_348, vertices_788, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_22, vertices_38, vertices_70, vertices_390, vertices_82, vertices_530, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_84, vertices_276, vertices_532, vertices_292, vertices_548, vertices_324, vertices_772, vertices_88, vertices_280, vertices_536, vertices_200, vertices_328, vertices_584, vertices_392, vertices_784, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_805), (false, vertices_793), (false, vertices_425), (false, vertices_713), (true, vertices_22), (true, vertices_38), (true, vertices_70), (true, vertices_390), (true, vertices_82), (true, vertices_530), (true, vertices_194), (true, vertices_578), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_324), (true, vertices_88), (true, vertices_328), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_390) then 16 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 8 4 566 22 3
cert_row_4 1 0 2 3 5 8 602 82 1
cert_row_4 2 1 3 5 7 2 348 84 3
cert_row_2 3 1 6 7 0 390
cert_rows
cert_pivot_2 4 8 2 0
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 22 566 3
cert_coverFacet 1 86
cert_cover_2 1 1 0 3 5 22 86 3
cert_coverFacet 2 422
cert_cover_5 2 3 0 1 4 6 38 422 3
cert_coverFacet 3 454
cert_cover_5 3 3 0 1 5 6 70 454 3
cert_coverFacet 4 602
cert_cover_5 4 1 0 2 3 5 82 602 1
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 348
cert_cover_5 6 2 1 2 3 5 84 348 1
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_257

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/P0_258.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_258

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 837, 713, 817, 481, 286, 590, 566, 314, 170, 650, 460, 788, 424, 161, 289, 545, 193, 321, 577, 641, 769, 14, 22, 518, 282, 42, 138, 522, 50, 162, 546, 642, 76, 268, 276, 532, 324, 580, 772, 168, 296, 200, 584, 392, 648, 304, 560, 784, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_837, vertices_713, vertices_817, vertices_481, vertices_286, vertices_590, vertices_566, vertices_314, vertices_170, vertices_650, vertices_460, vertices_788, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_518, vertices_282, vertices_42, vertices_138, vertices_522, vertices_50, vertices_162, vertices_546, vertices_642, vertices_76, vertices_268, vertices_276, vertices_532, vertices_324, vertices_580, vertices_772, vertices_168, vertices_296, vertices_200, vertices_584, vertices_392, vertices_648, vertices_304, vertices_560, vertices_784, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_837), (false, vertices_713), (false, vertices_817), (false, vertices_481), (true, vertices_14), (true, vertices_22), (true, vertices_518), (true, vertices_282), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_50), (true, vertices_76), (true, vertices_268), (true, vertices_276), (true, vertices_532), (true, vertices_168), (true, vertices_296), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_817) then 22 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_282) then 16 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_50) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_392) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_282), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 8 4 566 22 3
cert_row_4 1 0 1 2 5 8 590 14 3
cert_row_4 2 2 5 6 7 1 460 200 3
cert_row_2 3 2 3 7 0 282
cert_rows
cert_pivot_2 4 8 1 0
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 3 0 1 2 3 14 286 3
cert_coverFacet 1 590
cert_cover_5 1 1 0 1 2 5 14 590 3
cert_coverFacet 2 566
cert_cover_5 2 0 0 1 3 4 22 566 3
cert_coverFacet 3 314
cert_cover_5 3 3 0 2 3 4 282 314 3
cert_coverFacet 4 170
cert_cover_2 4 2 0 4 6 42 170 3
cert_coverFacet 5 650
cert_cover_2 5 2 0 6 8 138 650 3
cert_coverFacet 6 460
cert_cover_5 6 2 1 2 5 6 76 460 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_258

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/P0_260.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_260

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 397, 661, 805, 713, 310, 218, 410, 618, 114, 802, 628, 404, 720, 133, 261, 517, 137, 265, 521, 641, 769, 154, 74, 266, 522, 50, 82, 274, 98, 290, 546, 770, 52, 148, 276, 532, 292, 548, 388, 200, 584, 392, 112, 208, 592, 400, 656, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_397, vertices_661, vertices_805, vertices_713, vertices_310, vertices_218, vertices_410, vertices_618, vertices_114, vertices_802, vertices_628, vertices_404, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_641, vertices_769, vertices_154, vertices_74, vertices_266, vertices_522, vertices_50, vertices_82, vertices_274, vertices_98, vertices_290, vertices_546, vertices_770, vertices_52, vertices_148, vertices_276, vertices_532, vertices_292, vertices_548, vertices_388, vertices_200, vertices_584, vertices_392, vertices_112, vertices_208, vertices_592, vertices_400, vertices_656, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_397), (false, vertices_661), (false, vertices_805), (false, vertices_713), (true, vertices_154), (true, vertices_74), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_52), (true, vertices_276), (true, vertices_112), (true, vertices_208), (true, vertices_592), (true, vertices_400), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (true, vertices_154) then 16 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 50 1
cert_row_4 1 3 4 5 8 1 628 112 3
cert_row_4 2 0 2 5 8 4 618 74 3
cert_row_2 3 2 3 6 0 154
cert_rows
cert_pivot_2 7 1 4 0
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 50 310 1
cert_coverFacet 1 218
cert_cover_5 1 3 0 2 3 5 154 218 3
cert_coverFacet 2 410
cert_cover_5 2 3 0 2 3 7 154 410 3
cert_coverFacet 3 618
cert_cover_5 3 2 0 2 4 5 74 618 2
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 628
cert_cover_5 6 1 1 3 4 5 52 628 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 720
cert_cover_2 8 5 3 6 8 208 720 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_260

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/P0_261.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_261

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 613, 793, 361, 713, 182, 566, 410, 786, 482, 668, 228, 708, 456, 73, 265, 521, 97, 289, 545, 577, 769, 54, 146, 274, 530, 162, 290, 546, 386, 770, 148, 532, 100, 164, 548, 196, 580, 644, 152, 280, 536, 200, 328, 392, 648, 784, 224, 352, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_613, vertices_793, vertices_361, vertices_713, vertices_182, vertices_566, vertices_410, vertices_786, vertices_482, vertices_668, vertices_228, vertices_708, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_97, vertices_289, vertices_545, vertices_577, vertices_769, vertices_54, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_152, vertices_280, vertices_536, vertices_200, vertices_328, vertices_392, vertices_648, vertices_784, vertices_224, vertices_352, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_613), (false, vertices_793), (false, vertices_361), (false, vertices_713), (true, vertices_54), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_386), (true, vertices_148), (true, vertices_532), (true, vertices_164), (true, vertices_196), (true, vertices_644), (true, vertices_152), (true, vertices_392), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (true, vertices_54) then 16 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 6 7 5 482 162 3
cert_row_4 1 0 2 3 6 7 410 146 1
cert_row_4 2 1 3 6 8 2 668 148 3
cert_row_2 3 1 3 4 0 54
cert_rows
cert_pivot_2 5 7 2 0
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 3 0 1 3 6 54 182 3
cert_coverFacet 1 566
cert_cover_5 1 3 0 1 3 8 54 566 3
cert_coverFacet 2 410
cert_cover_5 2 1 0 2 3 6 146 410 1
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 482
cert_cover_5 4 0 0 4 5 6 162 482 2
cert_coverFacet 5 668
cert_cover_5 5 2 1 2 3 6 148 668 1
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_261

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/P0_262.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_262

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 405, 837, 665, 817, 206, 614, 570, 362, 650, 460, 312, 408, 864, 133, 261, 517, 145, 273, 529, 641, 769, 70, 134, 518, 42, 74, 138, 522, 98, 546, 642, 204, 324, 580, 388, 56, 152, 280, 536, 296, 328, 392, 648, 304, 560, 400, 352, 608, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_405, vertices_837, vertices_665, vertices_817, vertices_206, vertices_614, vertices_570, vertices_362, vertices_650, vertices_460, vertices_312, vertices_408, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_145, vertices_273, vertices_529, vertices_641, vertices_769, vertices_70, vertices_134, vertices_518, vertices_42, vertices_74, vertices_138, vertices_522, vertices_98, vertices_546, vertices_642, vertices_204, vertices_324, vertices_580, vertices_388, vertices_56, vertices_152, vertices_280, vertices_536, vertices_296, vertices_328, vertices_392, vertices_648, vertices_304, vertices_560, vertices_400, vertices_352, vertices_608, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_405), (false, vertices_837), (false, vertices_665), (false, vertices_817), (true, vertices_70), (true, vertices_42), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_98), (true, vertices_546), (true, vertices_204), (true, vertices_56), (true, vertices_280), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 19 16 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_665) then 17 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_204) then 18 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 8 3 570 42 3
cert_row_4 1 0 1 4 5 8 614 70 2
cert_row_4 2 2 4 5 7 0 362 296 2
cert_row_2 3 2 5 6 1 204
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 3 0 1 2 5 70 206 2
cert_coverFacet 1 614
cert_cover_5 1 1 0 1 4 5 70 614 2
cert_coverFacet 2 570
cert_cover_5 2 0 0 2 3 4 42 570 2
cert_coverFacet 3 362
cert_cover_5 3 2 0 2 4 5 42 362 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 460
cert_cover_5 5 3 1 2 5 7 204 460 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 864
cert_cover_2 8 5 4 7 8 352 864 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_262

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/P0_263.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_263

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 285, 665, 841, 433, 801, 590, 662, 230, 866, 540, 332, 404, 484, 25, 265, 521, 145, 273, 161, 289, 545, 641, 769, 70, 134, 518, 98, 162, 546, 578, 642, 28, 76, 268, 524, 148, 276, 532, 228, 324, 388, 536, 328, 584, 400, 656, 352, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_285, vertices_665, vertices_841, vertices_433, vertices_801, vertices_590, vertices_662, vertices_230, vertices_866, vertices_540, vertices_332, vertices_404, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_265, vertices_521, vertices_145, vertices_273, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_70, vertices_134, vertices_518, vertices_98, vertices_162, vertices_546, vertices_578, vertices_642, vertices_28, vertices_76, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_228, vertices_324, vertices_388, vertices_536, vertices_328, vertices_584, vertices_400, vertices_656, vertices_352, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_285), (false, vertices_665), (false, vertices_841), (false, vertices_433), (false, vertices_801), (true, vertices_70), (true, vertices_134), (true, vertices_518), (true, vertices_98), (true, vertices_578), (true, vertices_76), (true, vertices_524), (true, vertices_148), (true, vertices_532), (true, vertices_228), (true, vertices_324), (true, vertices_388), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_285) then 16 else
  if p.val = (false, vertices_665) then 19 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (false, vertices_801) then 12 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_228) then 17 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_228), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
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
cert_row_4 0 0 1 5 8 2 590 70 3
cert_row_4 1 0 1 6 8 3 662 134 3
cert_row_4 2 4 5 7 8 0 866 352 3
cert_row_2 3 4 5 6 1 228
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 70 590 2
cert_coverFacet 1 662
cert_cover_5 1 1 0 1 3 6 134 662 2
cert_coverFacet 2 230
cert_cover_5 2 3 0 1 4 5 70 230 2
cert_coverFacet 3 866
cert_cover_5 3 2 0 4 5 7 98 866 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 7 228 484 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_263

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/P0_264.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_264

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 837, 793, 465, 737, 542, 302, 614, 154, 426, 674, 780, 484, 408, 145, 273, 529, 193, 321, 577, 641, 769, 14, 38, 518, 26, 298, 138, 146, 530, 162, 546, 642, 268, 524, 100, 292, 324, 580, 772, 152, 280, 536, 392, 776, 400, 224, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_837, vertices_793, vertices_465, vertices_737, vertices_542, vertices_302, vertices_614, vertices_154, vertices_426, vertices_674, vertices_780, vertices_484, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_14, vertices_38, vertices_518, vertices_26, vertices_298, vertices_138, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_268, vertices_524, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_536, vertices_392, vertices_776, vertices_400, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_837), (false, vertices_793), (false, vertices_465), (false, vertices_737), (true, vertices_14), (true, vertices_38), (true, vertices_518), (true, vertices_26), (true, vertices_298), (true, vertices_138), (true, vertices_162), (true, vertices_546), (true, vertices_268), (true, vertices_524), (true, vertices_100), (true, vertices_292), (true, vertices_152), (true, vertices_392), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_298) then 16 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_298), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 8 3 542 14 3
cert_row_4 1 0 1 4 5 8 614 38 3
cert_row_4 2 4 5 6 7 1 484 224 3
cert_row_2 3 2 4 7 0 298
cert_rows
cert_pivot_2 3 8 1 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 14 542 3
cert_coverFacet 1 302
cert_cover_5 1 3 0 1 2 4 14 302 3
cert_coverFacet 2 614
cert_cover_5 2 1 0 1 4 5 38 614 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 426
cert_cover_5 4 3 0 2 4 6 298 426 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 484
cert_cover_5 7 2 1 4 5 6 100 484 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_264

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/P0_265.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_265

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 597, 841, 369, 689, 590, 142, 678, 394, 778, 434, 348, 412, 660, 49, 81, 529, 289, 545, 321, 577, 769, 14, 134, 518, 138, 266, 522, 162, 290, 546, 386, 770, 284, 76, 140, 84, 148, 532, 580, 644, 328, 584, 392, 776, 176, 304, 336, 400, 656, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_597, vertices_841, vertices_369, vertices_689, vertices_590, vertices_142, vertices_678, vertices_394, vertices_778, vertices_434, vertices_348, vertices_412, vertices_660] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_529, vertices_289, vertices_545, vertices_321, vertices_577, vertices_769, vertices_14, vertices_134, vertices_518, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_284, vertices_76, vertices_140, vertices_84, vertices_148, vertices_532, vertices_580, vertices_644, vertices_328, vertices_584, vertices_392, vertices_776, vertices_176, vertices_304, vertices_336, vertices_400, vertices_656, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_597), (false, vertices_841), (false, vertices_369), (false, vertices_689), (true, vertices_14), (true, vertices_134), (true, vertices_518), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_162), (true, vertices_386), (true, vertices_284), (true, vertices_76), (true, vertices_140), (true, vertices_148), (true, vertices_644), (true, vertices_392), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 21 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_284) then 18 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_284), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 8 5 590 14 3
cert_row_4 1 0 1 4 6 8 678 134 2
cert_row_4 2 3 4 6 7 0 434 176 3
cert_row_2 3 2 3 7 1 284
cert_rows
cert_pivot_2 5 8 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 142
cert_cover_2 1 1 0 2 6 14 142 3
cert_coverFacet 2 678
cert_cover_5 2 1 0 1 4 6 134 678 2
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 434
cert_cover_5 5 2 0 3 4 6 162 434 1
cert_coverFacet 6 348
cert_cover_5 6 3 1 2 3 5 284 348 3
cert_coverFacet 7 412
cert_cover_5 7 3 1 2 3 6 284 412 3
cert_coverFacet 8 660
cert_cover_2 8 3 1 6 8 148 660 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_265

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/P0_266.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_266

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [199, 331, 787, 643, 77, 781, 677, 690, 466, 236, 556, 872, 496, 816, 67, 131, 259, 515, 13, 69, 133, 517, 73, 265, 641, 769, 146, 274, 530, 194, 322, 642, 44, 76, 524, 164, 548, 196, 104, 552, 328, 776, 176, 304, 560, 464, 784, 224, 352, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_199, vertices_331, vertices_787, vertices_643, vertices_77, vertices_781, vertices_677, vertices_690, vertices_466, vertices_236, vertices_556, vertices_872, vertices_496, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_13, vertices_69, vertices_133, vertices_517, vertices_73, vertices_265, vertices_641, vertices_769, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_642, vertices_44, vertices_76, vertices_524, vertices_164, vertices_548, vertices_196, vertices_104, vertices_552, vertices_328, vertices_776, vertices_176, vertices_304, vertices_560, vertices_464, vertices_784, vertices_224, vertices_352, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_199), (false, vertices_331), (false, vertices_787), (false, vertices_643), (false, vertices_77), (false, vertices_781), (false, vertices_677), (true, vertices_146), (true, vertices_44), (true, vertices_104), (true, vertices_552), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_464), (true, vertices_224), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_643) then 10 else
  if p.val = (false, vertices_77) then 11 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_44) then 1 else
  if p.val = (true, vertices_104) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_464) then 21 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_77), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_464), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 3 4 6 8 0 690 176 3
cert_row_4 1 2 4 5 6 1 236 104 3
cert_row_4 2 4 5 7 8 2 872 352 3
cert_row_2 3 5 6 7 3 464
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 690
cert_cover_5 0 0 0 3 4 6 146 690 2
cert_coverFacet 1 466
cert_cover_5 1 3 0 3 5 6 146 466 2
cert_coverFacet 2 236
cert_cover_5 2 1 1 2 4 5 44 236 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 872
cert_cover_5 4 2 2 4 5 7 104 872 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 176 496 2
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_266

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/P0_267.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_267

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 781, 661, 389, 617, 457, 225, 790, 362, 810, 242, 338, 658, 468, 133, 261, 517, 73, 265, 521, 97, 161, 545, 193, 385, 641, 298, 82, 146, 274, 530, 98, 162, 546, 322, 642, 770, 148, 276, 532, 388, 772, 104, 552, 328, 776, 208, 336, 656, 224, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_781, vertices_661, vertices_389, vertices_617, vertices_457, vertices_225, vertices_790, vertices_362, vertices_810, vertices_242, vertices_338, vertices_658, vertices_468] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_193, vertices_385, vertices_641, vertices_298, vertices_82, vertices_146, vertices_274, vertices_530, vertices_98, vertices_162, vertices_546, vertices_322, vertices_642, vertices_770, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_104, vertices_552, vertices_328, vertices_776, vertices_208, vertices_336, vertices_656, vertices_224, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_781), (false, vertices_661), (false, vertices_389), (false, vertices_617), (false, vertices_457), (false, vertices_225), (true, vertices_298), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_322), (true, vertices_770), (true, vertices_276), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 13 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_389) then 10 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_225) then 11 else
  if p.val = (true, vertices_298) then 14 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_336) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_298), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_4 1 3 5 6 7 1 468 208 3
cert_row_4 2 0 4 5 6 3 242 98 3
cert_row_2 3 2 4 7 0 298
cert_rows
cert_pivot_2 8 1 3 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 362
cert_cover_5 1 3 0 2 4 5 298 362 3
cert_coverFacet 2 810
cert_cover_5 2 3 0 2 4 8 298 810 3
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 82 242 2
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 468
cert_cover_5 6 1 1 3 5 6 148 468 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_267

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/P0_268.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_268

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 341, 661, 197, 793, 425, 649, 230, 614, 810, 850, 418, 684, 596, 21, 69, 133, 137, 265, 521, 273, 529, 193, 321, 385, 641, 102, 162, 290, 546, 194, 322, 578, 386, 770, 84, 532, 164, 548, 196, 580, 644, 168, 296, 552, 648, 776, 336, 592, 784, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_341, vertices_661, vertices_197, vertices_793, vertices_425, vertices_649, vertices_230, vertices_614, vertices_810, vertices_850, vertices_418, vertices_684, vertices_596] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_133, vertices_137, vertices_265, vertices_521, vertices_273, vertices_529, vertices_193, vertices_321, vertices_385, vertices_641, vertices_102, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_84, vertices_532, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_336, vertices_592, vertices_784, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_341), (false, vertices_661), (false, vertices_197), (false, vertices_793), (false, vertices_425), (false, vertices_649), (true, vertices_102), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_578), (true, vertices_770), (true, vertices_164), (true, vertices_548), (true, vertices_580), (true, vertices_552), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 13 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_197) then 10 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_649) then 11 else
  if p.val = (true, vertices_102) then 14 else
  if p.val = (true, vertices_162) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_592) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 7 8 3 850 322 3
cert_row_4 1 0 2 4 8 7 810 546 1
cert_row_4 2 1 4 6 8 2 684 164 3
cert_row_2 3 1 4 5 0 102
cert_rows
cert_pivot_2 3 7 2 0
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 3 0 1 4 6 102 230 3
cert_coverFacet 1 614
cert_cover_5 1 3 0 1 4 8 102 614 3
cert_coverFacet 2 810
cert_cover_5 2 1 0 2 4 7 290 810 1
cert_coverFacet 3 850
cert_cover_5 3 0 0 3 5 7 322 850 1
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 684
cert_cover_5 5 2 1 2 4 6 164 684 1
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_268

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/P0_270.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_270

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 147, 275, 803, 661, 613, 793, 242, 370, 716, 228, 472, 664, 872, 19, 35, 131, 259, 37, 133, 517, 145, 273, 529, 545, 769, 114, 146, 274, 162, 290, 100, 164, 196, 580, 644, 152, 280, 536, 200, 328, 584, 648, 776, 208, 336, 656, 224, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_147, vertices_275, vertices_803, vertices_661, vertices_613, vertices_793, vertices_242, vertices_370, vertices_716, vertices_228, vertices_472, vertices_664, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_259, vertices_37, vertices_133, vertices_517, vertices_145, vertices_273, vertices_529, vertices_545, vertices_769, vertices_114, vertices_146, vertices_274, vertices_162, vertices_290, vertices_100, vertices_164, vertices_196, vertices_580, vertices_644, vertices_152, vertices_280, vertices_536, vertices_200, vertices_328, vertices_584, vertices_648, vertices_776, vertices_208, vertices_336, vertices_656, vertices_224, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_147), (false, vertices_275), (false, vertices_803), (false, vertices_661), (false, vertices_613), (false, vertices_793), (true, vertices_114), (true, vertices_196), (true, vertices_152), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_648), (true, vertices_208), (true, vertices_336), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 12 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 13 else
  if p.val = (false, vertices_147) then 10 else
  if p.val = (false, vertices_275) then 11 else
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_661) then 14 else
  if p.val = (false, vertices_613) then 15 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (true, vertices_114) then 18 else
  if p.val = (true, vertices_196) then 0 else
  if p.val = (true, vertices_152) then 1 else
  if p.val = (true, vertices_200) then 2 else
  if p.val = (true, vertices_328) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_352) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_167), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_114), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 5 6 8 1 716 200 3
cert_row_4 1 2 3 5 7 6 472 280 2
cert_row_4 2 4 5 7 8 2 872 352 3
cert_row_2 3 3 4 5 0 114
cert_rows
cert_pivot_2 1 6 2 0
cert_heightProof 4
cert_coverFacet 0 242
cert_cover_5 0 3 0 3 4 6 114 242 3
cert_coverFacet 1 370
cert_cover_5 1 3 0 3 4 7 114 370 3
cert_coverFacet 2 716
cert_cover_5 2 0 1 2 5 6 196 716 1
cert_coverFacet 3 228
cert_cover_2 3 4 1 5 6 100 228 3
cert_coverFacet 4 472
cert_cover_5 4 1 2 3 5 6 152 472 2
cert_coverFacet 5 664
cert_cover_2 5 3 2 6 8 152 664 3
cert_coverFacet 6 872
cert_cover_5 6 2 2 4 5 7 328 872 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_270

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/P0_271.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_271

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 661, 409, 841, 817, 230, 678, 202, 586, 866, 460, 372, 564, 404, 137, 265, 521, 145, 273, 529, 641, 769, 166, 74, 138, 522, 98, 546, 194, 578, 642, 52, 148, 276, 532, 100, 548, 196, 324, 388, 644, 200, 328, 584, 392, 304, 560, 400, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_661, vertices_409, vertices_841, vertices_817, vertices_230, vertices_678, vertices_202, vertices_586, vertices_866, vertices_460, vertices_372, vertices_564, vertices_404] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_641, vertices_769, vertices_166, vertices_74, vertices_138, vertices_522, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_52, vertices_148, vertices_276, vertices_532, vertices_100, vertices_548, vertices_196, vertices_324, vertices_388, vertices_644, vertices_200, vertices_328, vertices_584, vertices_392, vertices_304, vertices_560, vertices_400, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_661), (false, vertices_409), (false, vertices_841), (false, vertices_817), (true, vertices_166), (true, vertices_74), (true, vertices_98), (true, vertices_546), (true, vertices_194), (true, vertices_578), (true, vertices_52), (true, vertices_276), (true, vertices_100), (true, vertices_548), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_200), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (true, vertices_166) then 16 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_166), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 7 8 866 98 3
cert_row_4 1 1 5 6 7 2 460 196 3
cert_row_4 2 1 4 5 7 3 372 100 3
cert_row_2 3 1 4 6 0 166
cert_rows
cert_pivot_2 8 2 3 0
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 3 0 1 4 5 166 230 3
cert_coverFacet 1 678
cert_cover_5 1 3 0 1 4 8 166 678 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 586
cert_cover_2 3 2 0 5 8 74 586 3
cert_coverFacet 4 866
cert_cover_5 4 0 0 4 5 7 98 866 3
cert_coverFacet 5 460
cert_cover_5 5 1 1 2 5 6 196 460 1
cert_coverFacet 6 372
cert_cover_5 6 2 1 3 4 5 52 372 3
cert_coverFacet 7 564
cert_cover_2 7 3 1 4 8 52 564 3
cert_coverFacet 8 404
cert_cover_2 8 3 1 6 7 148 404 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_271

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/P0_273.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_273

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 901, 361, 465, 737, 782, 122, 538, 298, 626, 412, 540, 724, 344, 97, 289, 545, 193, 321, 385, 641, 769, 26, 42, 266, 522, 114, 530, 290, 546, 770, 28, 268, 524, 148, 532, 388, 644, 772, 88, 280, 536, 104, 296, 328, 208, 336, 592, 400, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_901, vertices_361, vertices_465, vertices_737, vertices_782, vertices_122, vertices_538, vertices_298, vertices_626, vertices_412, vertices_540, vertices_724, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_266, vertices_522, vertices_114, vertices_530, vertices_290, vertices_546, vertices_770, vertices_28, vertices_268, vertices_524, vertices_148, vertices_532, vertices_388, vertices_644, vertices_772, vertices_88, vertices_280, vertices_536, vertices_104, vertices_296, vertices_328, vertices_208, vertices_336, vertices_592, vertices_400, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_901), (false, vertices_361), (false, vertices_465), (false, vertices_737), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_114), (true, vertices_530), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_532), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_901) then 18 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_114) then 16 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_592) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_114), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 4 114
cert_row_4 1 1 2 7 8 0 782 268 3
cert_row_4 2 1 3 6 7 2 412 148 3
cert_row_4 3 3 5 6 8 1 724 208 3
cert_rows
cert_pivot_2 4 0 2 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 4 26 122 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 626
cert_cover_5 4 0 0 3 4 8 114 626 3
cert_coverFacet 5 412
cert_cover_5 5 2 1 2 3 6 28 412 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 724
cert_cover_5 7 3 1 3 5 6 148 724 2
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_273

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/P0_274.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_274

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 789, 905, 433, 737, 334, 526, 118, 534, 714, 610, 780, 372, 488, 49, 273, 529, 161, 545, 385, 641, 769, 14, 22, 70, 518, 74, 522, 50, 530, 98, 546, 578, 268, 524, 116, 276, 532, 324, 772, 200, 328, 392, 648, 776, 304, 224, 352, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_789, vertices_905, vertices_433, vertices_737, vertices_334, vertices_526, vertices_118, vertices_534, vertices_714, vertices_610, vertices_780, vertices_372, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_273, vertices_529, vertices_161, vertices_545, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_70, vertices_518, vertices_74, vertices_522, vertices_50, vertices_530, vertices_98, vertices_546, vertices_578, vertices_268, vertices_524, vertices_116, vertices_276, vertices_532, vertices_324, vertices_772, vertices_200, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_224, vertices_352, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_789), (false, vertices_905), (false, vertices_433), (false, vertices_737), (true, vertices_14), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_74), (true, vertices_522), (true, vertices_98), (true, vertices_578), (true, vertices_268), (true, vertices_524), (true, vertices_116), (true, vertices_324), (true, vertices_200), (true, vertices_328), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 15 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_905) then 20 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_116) then 18 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_116), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 74 3
cert_row_4 1 1 2 5 7 0 334 268 2
cert_row_4 2 4 5 6 7 2 488 224 3
cert_row_2 3 3 4 5 1 116
cert_rows
cert_pivot_2 8 0 2 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 1 0 1 2 5 14 334 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 118
cert_cover_5 2 3 0 1 3 4 22 118 3
cert_coverFacet 3 534
cert_cover_2 3 1 0 3 8 22 534 3
cert_coverFacet 4 714
cert_cover_5 4 0 0 2 5 6 74 714 3
cert_coverFacet 5 610
cert_cover_2 5 4 0 5 8 98 610 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 372
cert_cover_5 7 3 1 3 4 7 116 372 3
cert_coverFacet 8 488
cert_cover_5 8 2 2 4 5 6 200 488 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_274

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/P0_275.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_275

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 787, 355, 661, 357, 389, 409, 810, 738, 428, 228, 708, 696, 792, 67, 259, 515, 69, 133, 261, 517, 145, 273, 529, 353, 385, 98, 290, 546, 578, 770, 100, 164, 292, 196, 580, 388, 644, 152, 280, 536, 168, 296, 552, 392, 776, 656, 784, 224, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_787, vertices_355, vertices_661, vertices_357, vertices_389, vertices_409, vertices_810, vertices_738, vertices_428, vertices_228, vertices_708, vertices_696, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_69, vertices_133, vertices_261, vertices_517, vertices_145, vertices_273, vertices_529, vertices_353, vertices_385, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_100, vertices_164, vertices_292, vertices_196, vertices_580, vertices_388, vertices_644, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_392, vertices_776, vertices_656, vertices_784, vertices_224, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_787), (false, vertices_355), (false, vertices_661), (false, vertices_357), (false, vertices_389), (false, vertices_409), (true, vertices_546), (true, vertices_164), (true, vertices_196), (true, vertices_536), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_224), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 19 20 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 13 else
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_355) then 21 else
  if p.val = (false, vertices_661) then 16 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_389) then 11 else
  if p.val = (false, vertices_409) then 18 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_164) then 1 else
  if p.val = (true, vertices_196) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 6 8 5 738 546 2
cert_row_4 1 2 4 7 8 0 810 296 3
cert_row_4 2 2 4 6 7 1 428 168 3
cert_row_4 3 3 4 6 8 2 696 656 1
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 810
cert_cover_5 0 1 0 2 4 7 290 810 1
cert_coverFacet 1 738
cert_cover_5 1 0 0 4 5 6 98 738 3
cert_coverFacet 2 428
cert_cover_5 2 2 1 2 4 6 164 428 1
cert_coverFacet 3 228
cert_cover_2 3 4 1 5 6 100 228 3
cert_coverFacet 4 708
cert_cover_2 4 5 1 6 8 196 708 3
cert_coverFacet 5 696
cert_cover_5 5 3 2 3 4 6 152 696 2
cert_coverFacet 6 792
cert_cover_2 6 3 2 7 8 280 792 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_275

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/P0_276.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_276

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [263, 519, 787, 341, 709, 665, 241, 358, 614, 810, 440, 792, 744, 368, 7, 259, 515, 69, 261, 517, 81, 145, 273, 529, 193, 641, 102, 262, 518, 290, 546, 770, 324, 580, 152, 280, 536, 168, 296, 552, 648, 776, 112, 176, 304, 336, 784, 224, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_263, vertices_519, vertices_787, vertices_341, vertices_709, vertices_665, vertices_241, vertices_358, vertices_614, vertices_810, vertices_440, vertices_792, vertices_744, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_259, vertices_515, vertices_69, vertices_261, vertices_517, vertices_81, vertices_145, vertices_273, vertices_529, vertices_193, vertices_641, vertices_102, vertices_262, vertices_518, vertices_290, vertices_546, vertices_770, vertices_324, vertices_580, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_336, vertices_784, vertices_224, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_263), (false, vertices_519), (false, vertices_787), (false, vertices_341), (false, vertices_709), (false, vertices_665), (false, vertices_241), (true, vertices_102), (true, vertices_290), (true, vertices_546), (true, vertices_280), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_304), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_263) then 10 else
  if p.val = (false, vertices_519) then 11 else
  if p.val = (false, vertices_787) then 13 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_709) then 17 else
  if p.val = (false, vertices_665) then 19 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_102) then 14 else
  if p.val = (true, vertices_290) then 0 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_608) then 9 else
  0
cert_priority
cert_nodeAtPriority_7 0 290 1 546 2 280 168 296 552 776 304 352 608 263 519 787 102 341 709 665 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 4 6 7 3 440 168 3
cert_row_4 1 0 2 4 8 7 810 546 1
cert_row_4 2 4 5 6 8 2 744 224 3
cert_row_2 3 1 4 5 0 102
cert_rows
cert_pivot_2 3 7 2 0
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 3 0 1 4 7 102 358 3
cert_coverFacet 1 614
cert_cover_5 1 3 0 1 4 8 102 614 3
cert_coverFacet 2 810
cert_cover_5 2 1 0 2 4 7 290 810 1
cert_coverFacet 3 440
cert_cover_5 3 0 2 3 4 6 152 440 2
cert_coverFacet 4 792
cert_cover_2 4 3 2 7 8 280 792 3
cert_coverFacet 5 744
cert_cover_5 5 2 2 4 5 6 168 744 2
cert_coverFacet 6 368
cert_cover_2 6 4 3 5 7 112 368 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_276

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/P0_277.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_277

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 789, 613, 421, 345, 361, 902, 410, 210, 786, 738, 676, 248, 424, 37, 261, 517, 329, 81, 273, 529, 97, 289, 577, 82, 146, 274, 530, 194, 578, 386, 642, 770, 164, 548, 388, 644, 772, 88, 152, 280, 104, 168, 296, 392, 208, 784, 224, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_789, vertices_613, vertices_421, vertices_345, vertices_361, vertices_902, vertices_410, vertices_210, vertices_786, vertices_738, vertices_676, vertices_248, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_329, vertices_81, vertices_273, vertices_529, vertices_97, vertices_289, vertices_577, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_164, vertices_548, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_392, vertices_208, vertices_784, vertices_224, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_789), (false, vertices_613), (false, vertices_421), (false, vertices_345), (false, vertices_361), (true, vertices_146), (true, vertices_274), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_644), (true, vertices_152), (true, vertices_168), (true, vertices_392), (true, vertices_208), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_789) then 16 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_421) then 18 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
cert_nodeAtPriority 0 146 1 274 2 194 386 642 770 644 152 168 392 208 224 672 595 789 613 421 345 361
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 6 7 8 1 902 386 3
cert_row_4 1 0 2 3 6 7 410 146 1
cert_row_4 2 4 5 6 8 0 738 224 3
cert_row_4 3 3 4 5 6 2 248 208 1
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 410
cert_cover_5 1 1 0 2 3 6 146 410 1
cert_coverFacet 2 210
cert_cover_2 2 3 0 5 6 82 210 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 194 738 1
cert_coverFacet 5 676
cert_cover_2 5 4 1 6 8 164 676 3
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 88 248 2
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_277

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2163 : Certifies 2163 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_231.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2164 : Certifies 2164 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_232.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2165 : Certifies 2165 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_233.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2166 : Certifies 2166 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_246.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2167 : Certifies 2167 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_247.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2168 : Certifies 2168 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_248.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2169 : Certifies 2169 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_249.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2170 : Certifies 2170 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_250.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2171 : Certifies 2171 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_251.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2172 : Certifies 2172 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_252.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2173 : Certifies 2173 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_255.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2174 : Certifies 2174 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_256.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2175 : Certifies 2175 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_257.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2176 : Certifies 2176 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_258.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2177 : Certifies 2177 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_260.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2178 : Certifies 2178 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_261.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2179 : Certifies 2179 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_262.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2180 : Certifies 2180 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_263.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2181 : Certifies 2181 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_264.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2182 : Certifies 2182 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_265.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2183 : Certifies 2183 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_266.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2184 : Certifies 2184 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_267.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2185 : Certifies 2185 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_268.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2186 : Certifies 2186 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_270.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2187 : Certifies 2187 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_271.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2188 : Certifies 2188 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_273.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2189 : Certifies 2189 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_274.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2190 : Certifies 2190 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_275.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2191 : Certifies 2191 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_276.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2192 : Certifies 2192 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_277.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B071 (j : Fin 30) :
    Certifies (2163 + j.val) := by
  fin_cases j
  · exact projection_2163
  · exact projection_2164
  · exact projection_2165
  · exact projection_2166
  · exact projection_2167
  · exact projection_2168
  · exact projection_2169
  · exact projection_2170
  · exact projection_2171
  · exact projection_2172
  · exact projection_2173
  · exact projection_2174
  · exact projection_2175
  · exact projection_2176
  · exact projection_2177
  · exact projection_2178
  · exact projection_2179
  · exact projection_2180
  · exact projection_2181
  · exact projection_2182
  · exact projection_2183
  · exact projection_2184
  · exact projection_2185
  · exact projection_2186
  · exact projection_2187
  · exact projection_2188
  · exact projection_2189
  · exact projection_2190
  · exact projection_2191
  · exact projection_2192

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
