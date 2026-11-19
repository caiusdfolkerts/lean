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
/- Source: ProjectionCertificates/R_m15e10q1_0972.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0972

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 653, 453, 773, 369, 737, 158, 558, 406, 774, 122, 306, 472, 616, 712, 133, 261, 517, 97, 289, 545, 193, 321, 641, 769, 14, 150, 262, 518, 26, 42, 50, 274, 290, 546, 770, 140, 524, 388, 772, 88, 152, 104, 552, 200, 584, 648, 112, 304, 336, 400, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_653, vertices_453, vertices_773, vertices_369, vertices_737, vertices_158, vertices_558, vertices_406, vertices_774, vertices_122, vertices_306, vertices_472, vertices_616, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_150, vertices_262, vertices_518, vertices_26, vertices_42, vertices_50, vertices_274, vertices_290, vertices_546, vertices_770, vertices_140, vertices_524, vertices_388, vertices_772, vertices_88, vertices_152, vertices_104, vertices_552, vertices_200, vertices_584, vertices_648, vertices_112, vertices_304, vertices_336, vertices_400, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_653), (false, vertices_453), (false, vertices_773), (false, vertices_369), (false, vertices_737), (true, vertices_14), (true, vertices_150), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_42), (true, vertices_50), (true, vertices_274), (true, vertices_88), (true, vertices_152), (true, vertices_104), (true, vertices_552), (true, vertices_200), (true, vertices_584), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_150) then 17 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_50) then 6 else
  if p.val = (true, vertices_274) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_150), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 14 3
cert_row_2 1 0 1 3 6 150
cert_row_4 2 0 2 3 4 5 122 26 3
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 8 1 0 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 14 158 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 4 14 558 3
cert_coverFacet 2 406
cert_cover_5 2 1 0 1 3 7 150 406 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 122
cert_cover_5 4 2 0 2 3 4 26 122 3
cert_coverFacet 5 306
cert_cover_2 5 3 0 4 7 50 306 3
cert_coverFacet 6 472
cert_cover_5 6 3 2 3 5 6 88 472 3
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coverFacet 8 712
cert_cover_2 8 5 2 6 8 200 712 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0972

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0973.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0973

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 395, 563, 771, 453, 201, 865, 790, 58, 282, 412, 724, 836, 696, 744, 11, 35, 259, 515, 73, 137, 97, 545, 193, 321, 385, 769, 26, 42, 266, 50, 274, 530, 770, 148, 276, 532, 196, 324, 580, 388, 772, 56, 152, 280, 104, 680, 200, 392, 560, 656, 608, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_395, vertices_563, vertices_771, vertices_453, vertices_201, vertices_865, vertices_790, vertices_58, vertices_282, vertices_412, vertices_724, vertices_836, vertices_696, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_515, vertices_73, vertices_137, vertices_97, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_26, vertices_42, vertices_266, vertices_50, vertices_274, vertices_530, vertices_770, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_56, vertices_152, vertices_280, vertices_104, vertices_680, vertices_200, vertices_392, vertices_560, vertices_656, vertices_608, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_395), (false, vertices_563), (false, vertices_771), (false, vertices_453), (false, vertices_201), (false, vertices_865), (true, vertices_26), (true, vertices_274), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_580), (true, vertices_772), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_680), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 15 else
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_563) then 17 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (false, vertices_865) then 24 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_680) then 21 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_680), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 6 8 680
cert_row_4 1 0 1 3 7 8 790 274 1
cert_row_4 2 1 2 3 6 7 412 148 1
cert_row_4 3 1 3 5 6 8 724 148 2
cert_rows
cert_pivot_2 4 0 2 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 274 790 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 412
cert_cover_5 3 2 1 2 3 6 148 412 1
cert_coverFacet 4 724
cert_cover_5 4 3 1 3 5 6 148 724 2
cert_coverFacet 5 836
cert_cover_2 5 5 1 7 8 324 836 3
cert_coverFacet 6 696
cert_cover_5 6 0 2 3 4 6 56 696 3
cert_coverFacet 7 744
cert_cover_5 7 0 2 4 5 6 104 744 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0973

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0974.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0974

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 147, 451, 357, 409, 817, 609, 230, 678, 666, 610, 796, 460, 652, 804, 19, 67, 131, 145, 273, 529, 97, 289, 545, 321, 577, 385, 166, 146, 530, 98, 546, 194, 578, 642, 140, 268, 524, 100, 292, 548, 196, 324, 644, 772, 152, 280, 536, 392, 648, 784, 608, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_147, vertices_451, vertices_357, vertices_409, vertices_817, vertices_609, vertices_230, vertices_678, vertices_666, vertices_610, vertices_796, vertices_460, vertices_652, vertices_804] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_131, vertices_145, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_166, vertices_146, vertices_530, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_140, vertices_268, vertices_524, vertices_100, vertices_292, vertices_548, vertices_196, vertices_324, vertices_644, vertices_772, vertices_152, vertices_280, vertices_536, vertices_392, vertices_648, vertices_784, vertices_608, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_147), (false, vertices_451), (false, vertices_357), (false, vertices_409), (false, vertices_817), (false, vertices_609), (true, vertices_166), (true, vertices_98), (true, vertices_546), (true, vertices_642), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_548), (true, vertices_196), (true, vertices_644), (true, vertices_772), (true, vertices_536), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (false, vertices_609) then 1 else
  if p.val = (true, vertices_166) then 17 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_648) then 13 else
  0
cert_priority
cert_nodeAtPriority_23 147 609 98 546 642 140 268 524 548 196 644 772 536 648 595 451 166 357 409 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 6 166
cert_row_4 1 0 2 3 6 8 666 146 1
cert_row_4 2 1 2 3 7 8 796 268 2
cert_row_4 3 1 2 5 6 7 460 140 2
cert_rows
cert_pivot_2 4 0 3 1
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 0 0 1 4 5 166 230 3
cert_coverFacet 1 678
cert_cover_5 1 0 0 1 4 8 166 678 3
cert_coverFacet 2 666
cert_cover_5 2 1 0 2 3 6 146 666 1
cert_coverFacet 3 610
cert_cover_2 3 4 0 5 8 98 610 3
cert_coverFacet 4 796
cert_cover_5 4 2 1 2 3 7 268 796 2
cert_coverFacet 5 460
cert_cover_5 5 3 1 2 5 6 140 460 2
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0974

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0975.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0975

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 397, 597, 229, 773, 865, 790, 602, 410, 682, 802, 92, 284, 204, 744, 69, 133, 261, 517, 97, 161, 289, 577, 385, 769, 26, 138, 522, 274, 530, 162, 290, 546, 386, 770, 28, 76, 140, 268, 84, 276, 532, 196, 772, 88, 280, 680, 200, 584, 392, 592, 224, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_397, vertices_597, vertices_229, vertices_773, vertices_865, vertices_790, vertices_602, vertices_410, vertices_682, vertices_802, vertices_92, vertices_284, vertices_204, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_769, vertices_26, vertices_138, vertices_522, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_28, vertices_76, vertices_140, vertices_268, vertices_84, vertices_276, vertices_532, vertices_196, vertices_772, vertices_88, vertices_280, vertices_680, vertices_200, vertices_584, vertices_392, vertices_592, vertices_224, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_397), (false, vertices_597), (false, vertices_229), (false, vertices_773), (false, vertices_865), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_770), (true, vertices_28), (true, vertices_76), (true, vertices_276), (true, vertices_88), (true, vertices_280), (true, vertices_680), (true, vertices_200), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_229) then 20 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_680) then 22 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_584) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(true, vertices_680), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 6 8 680
cert_row_4 1 0 1 3 7 8 790 274 1
cert_row_4 2 0 2 3 5 8 602 26 3
cert_row_4 3 0 2 3 6 7 410 26 3
cert_rows
cert_pivot_2 4 1 5 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 274 790 1
cert_coverFacet 1 602
cert_cover_5 1 2 0 2 3 5 26 602 3
cert_coverFacet 2 410
cert_cover_5 2 3 0 2 3 6 26 410 3
cert_coverFacet 3 682
cert_cover_5 3 0 0 2 4 6 138 682 2
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 92
cert_cover_2 5 2 1 3 5 28 92 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 204
cert_cover_2 7 2 1 5 6 76 204 3
cert_coverFacet 8 744
cert_cover_5 8 0 2 4 5 6 680 744 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0975

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0976.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0976

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [103, 213, 677, 905, 465, 865, 30, 46, 86, 538, 682, 626, 412, 172, 856, 37, 69, 133, 209, 97, 545, 321, 385, 641, 769, 14, 22, 38, 70, 26, 42, 522, 82, 530, 98, 546, 28, 44, 140, 84, 148, 164, 280, 536, 168, 392, 648, 776, 336, 592, 400, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_103, vertices_213, vertices_677, vertices_905, vertices_465, vertices_865, vertices_30, vertices_46, vertices_86, vertices_538, vertices_682, vertices_626, vertices_412, vertices_172, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_133, vertices_209, vertices_97, vertices_545, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_38, vertices_70, vertices_26, vertices_42, vertices_522, vertices_82, vertices_530, vertices_98, vertices_546, vertices_28, vertices_44, vertices_140, vertices_84, vertices_148, vertices_164, vertices_280, vertices_536, vertices_168, vertices_392, vertices_648, vertices_776, vertices_336, vertices_592, vertices_400, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_103), (false, vertices_213), (false, vertices_677), (false, vertices_905), (false, vertices_465), (false, vertices_865), (true, vertices_14), (true, vertices_22), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_82), (true, vertices_530), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_140), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 19 21 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_103) then 16 else
  if p.val = (false, vertices_213) then 22 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_905) then 20 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_103), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 6 7 412 28 3
cert_row_4 1 0 2 4 6 8 682 42 3
cert_row_4 2 0 3 4 5 8 626 82 2
cert_row_4 3 2 3 5 7 8 856 280 2
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 46
cert_cover_2 1 1 0 2 4 14 46 3
cert_coverFacet 2 86
cert_cover_2 2 1 0 3 5 22 86 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 682
cert_cover_5 4 1 0 2 4 6 42 682 3
cert_coverFacet 5 626
cert_cover_5 5 2 0 3 4 5 82 626 2
cert_coverFacet 6 412
cert_cover_5 6 0 1 2 3 6 28 412 3
cert_coverFacet 7 172
cert_cover_2 7 2 1 4 6 44 172 3
cert_coverFacet 8 856
cert_cover_5 8 3 2 3 5 7 280 856 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0976

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0977.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0977

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 173, 333, 405, 569, 601, 177, 678, 842, 626, 178, 402, 898, 812, 900, 13, 133, 261, 537, 41, 73, 49, 81, 145, 273, 161, 321, 50, 82, 146, 274, 162, 546, 322, 578, 386, 642, 770, 44, 268, 164, 548, 388, 644, 772, 552, 328, 584, 776, 176, 560, 592, 400, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_173, vertices_333, vertices_405, vertices_569, vertices_601, vertices_177, vertices_678, vertices_842, vertices_626, vertices_178, vertices_402, vertices_898, vertices_812, vertices_900] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_537, vertices_41, vertices_73, vertices_49, vertices_81, vertices_145, vertices_273, vertices_161, vertices_321, vertices_50, vertices_82, vertices_146, vertices_274, vertices_162, vertices_546, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_164, vertices_548, vertices_388, vertices_644, vertices_772, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_560, vertices_592, vertices_400, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_173), (false, vertices_333), (false, vertices_405), (false, vertices_569), (false, vertices_601), (false, vertices_177), (true, vertices_50), (true, vertices_146), (true, vertices_162), (true, vertices_546), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_776), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 15 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_601) then 22 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 162 1
cert_row_4 1 0 3 4 5 8 626 50 3
cert_row_4 2 0 2 5 7 8 842 322 1
cert_row_4 3 1 2 4 7 8 812 44 3
cert_rows
cert_pivot_2 6 3 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 162 678 1
cert_coverFacet 1 842
cert_cover_5 1 2 0 2 5 7 322 842 1
cert_coverFacet 2 626
cert_cover_5 2 1 0 3 4 5 50 626 3
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 812
cert_cover_5 6 3 1 2 4 7 44 812 3
cert_coverFacet 7 900
cert_cover_2 7 6 1 7 8 388 900 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0977

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0978.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0978

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [115, 787, 355, 205, 85, 661, 961, 566, 810, 60, 92, 556, 908, 120, 488, 19, 99, 259, 21, 69, 133, 81, 529, 193, 321, 641, 769, 50, 530, 290, 546, 770, 28, 44, 76, 140, 524, 52, 84, 532, 548, 644, 56, 88, 104, 296, 552, 200, 392, 776, 112, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_115, vertices_787, vertices_355, vertices_205, vertices_85, vertices_661, vertices_961, vertices_566, vertices_810, vertices_60, vertices_92, vertices_556, vertices_908, vertices_120, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_99, vertices_259, vertices_21, vertices_69, vertices_133, vertices_81, vertices_529, vertices_193, vertices_321, vertices_641, vertices_769, vertices_50, vertices_530, vertices_290, vertices_546, vertices_770, vertices_28, vertices_44, vertices_76, vertices_140, vertices_524, vertices_52, vertices_84, vertices_532, vertices_548, vertices_644, vertices_56, vertices_88, vertices_104, vertices_296, vertices_552, vertices_200, vertices_392, vertices_776, vertices_112, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_115), (false, vertices_787), (false, vertices_355), (false, vertices_205), (false, vertices_85), (false, vertices_661), (false, vertices_961), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_524), (true, vertices_52), (true, vertices_548), (true, vertices_56), (true, vertices_88), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_392), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 22 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_115) then 15 else
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_355) then 17 else
  if p.val = (false, vertices_205) then 19 else
  if p.val = (false, vertices_85) then 0 else
  if p.val = (false, vertices_661) then 20 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_776) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 50 1
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_4 2 1 2 6 7 8 908 140 3
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 50 566 1
cert_coverFacet 1 810
cert_cover_5 1 1 0 2 4 7 290 810 1
cert_coverFacet 2 60
cert_cover_2 2 2 1 3 4 28 60 3
cert_coverFacet 3 92
cert_cover_2 3 2 1 3 5 28 92 3
cert_coverFacet 4 556
cert_cover_2 4 2 1 4 8 44 556 3
cert_coverFacet 5 908
cert_cover_5 5 2 1 2 6 7 140 908 3
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0978

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0979.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0979

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 285, 181, 805, 665, 841, 454, 602, 210, 658, 866, 418, 348, 212, 420, 21, 37, 261, 25, 265, 521, 145, 161, 545, 641, 769, 82, 146, 530, 162, 290, 546, 194, 322, 578, 386, 642, 284, 84, 148, 164, 292, 196, 324, 388, 88, 536, 328, 584, 208, 656, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_285, vertices_181, vertices_805, vertices_665, vertices_841, vertices_454, vertices_602, vertices_210, vertices_658, vertices_866, vertices_418, vertices_348, vertices_212, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_261, vertices_25, vertices_265, vertices_521, vertices_145, vertices_161, vertices_545, vertices_641, vertices_769, vertices_82, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_284, vertices_84, vertices_148, vertices_164, vertices_292, vertices_196, vertices_324, vertices_388, vertices_88, vertices_536, vertices_328, vertices_584, vertices_208, vertices_656, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_285), (false, vertices_181), (false, vertices_805), (false, vertices_665), (false, vertices_841), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_290), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_84), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_88), (true, vertices_208), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_841) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 82 1 146 2 530 290 194 322 578 386 84 196 324 388 88 208 416 675 285 181 805 665 841
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 194 1
cert_row_2 1 1 2 3 7 284
cert_row_4 2 0 2 3 5 8 602 82 1
cert_row_4 3 0 4 5 7 8 866 290 2
cert_rows
cert_pivot_2 6 1 2 0
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 0 0 1 5 6 194 454 1
cert_coverFacet 1 602
cert_cover_5 1 2 0 2 3 5 82 602 1
cert_coverFacet 2 210
cert_cover_2 2 3 0 5 6 82 210 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 866
cert_cover_5 4 3 0 4 5 7 290 866 2
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 348
cert_cover_5 6 1 1 2 3 5 284 348 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coverFacet 8 420
cert_cover_2 8 4 1 6 7 164 420 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0979

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0980.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0980

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 295, 659, 419, 61, 537, 241, 902, 300, 844, 312, 728, 344, 368, 992, 7, 291, 131, 515, 13, 37, 25, 521, 49, 145, 529, 161, 262, 518, 386, 642, 44, 268, 524, 292, 772, 56, 88, 280, 536, 296, 328, 584, 112, 304, 208, 336, 656, 224, 352, 416, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_295, vertices_659, vertices_419, vertices_61, vertices_537, vertices_241, vertices_902, vertices_300, vertices_844, vertices_312, vertices_728, vertices_344, vertices_368, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_291, vertices_131, vertices_515, vertices_13, vertices_37, vertices_25, vertices_521, vertices_49, vertices_145, vertices_529, vertices_161, vertices_262, vertices_518, vertices_386, vertices_642, vertices_44, vertices_268, vertices_524, vertices_292, vertices_772, vertices_56, vertices_88, vertices_280, vertices_536, vertices_296, vertices_328, vertices_584, vertices_112, vertices_304, vertices_208, vertices_336, vertices_656, vertices_224, vertices_352, vertices_416, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_295), (false, vertices_659), (false, vertices_419), (false, vertices_61), (false, vertices_537), (false, vertices_241), (true, vertices_268), (true, vertices_772), (true, vertices_88), (true, vertices_280), (true, vertices_296), (true, vertices_328), (true, vertices_584), (true, vertices_304), (true, vertices_336), (true, vertices_352), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 15 else
  if p.val = (false, vertices_295) then 18 else
  if p.val = (false, vertices_659) then 19 else
  if p.val = (false, vertices_419) then 20 else
  if p.val = (false, vertices_61) then 16 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_772) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 262 2
cert_row_4 1 1 2 5 7 8 844 268 2
cert_row_4 2 2 3 5 6 8 728 88 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 262 902 2
cert_coverFacet 1 300
cert_cover_2 1 2 1 4 7 44 300 3
cert_coverFacet 2 844
cert_cover_5 2 1 1 2 5 7 268 844 2
cert_coverFacet 3 312
cert_cover_2 3 3 2 4 7 56 312 3
cert_coverFacet 4 728
cert_cover_5 4 2 2 3 5 6 88 728 3
cert_coverFacet 5 344
cert_cover_2 5 3 2 5 7 88 344 3
cert_coverFacet 6 368
cert_cover_2 6 4 3 5 7 112 368 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0980

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0981.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0981

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 339, 803, 643, 653, 85, 837, 682, 402, 418, 220, 620, 248, 880, 432, 19, 131, 259, 515, 21, 69, 133, 517, 81, 321, 641, 769, 146, 274, 162, 290, 546, 386, 642, 76, 140, 524, 84, 148, 580, 216, 104, 168, 552, 648, 112, 176, 304, 336, 400, 608, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_339, vertices_803, vertices_643, vertices_653, vertices_85, vertices_837, vertices_682, vertices_402, vertices_418, vertices_220, vertices_620, vertices_248, vertices_880, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_21, vertices_69, vertices_133, vertices_517, vertices_81, vertices_321, vertices_641, vertices_769, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_76, vertices_140, vertices_524, vertices_84, vertices_148, vertices_580, vertices_216, vertices_104, vertices_168, vertices_552, vertices_648, vertices_112, vertices_176, vertices_304, vertices_336, vertices_400, vertices_608, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_339), (false, vertices_803), (false, vertices_643), (false, vertices_653), (false, vertices_85), (false, vertices_837), (true, vertices_162), (true, vertices_386), (true, vertices_76), (true, vertices_216), (true, vertices_104), (true, vertices_168), (true, vertices_552), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_400), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 15 else
  if p.val = (false, vertices_339) then 16 else
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_85) then 1 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_216) then 22 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 162 1
cert_row_2 1 2 3 5 6 216
cert_row_4 2 1 2 4 5 8 620 76 2
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 6 1 3
cert_heightProof 4
cert_coverFacet 0 682
cert_cover_5 0 0 0 2 4 6 162 682 1
cert_coverFacet 1 402
cert_cover_2 1 3 0 6 7 146 402 3
cert_coverFacet 2 418
cert_cover_2 2 4 0 6 7 162 418 3
cert_coverFacet 3 220
cert_cover_5 3 1 1 2 3 5 76 220 2
cert_coverFacet 4 620
cert_cover_5 4 2 1 2 4 5 76 620 2
cert_coverFacet 5 248
cert_cover_5 5 1 2 3 4 5 216 248 2
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0981

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0982.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0982

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 653, 217, 777, 369, 961, 62, 270, 678, 774, 306, 866, 188, 780, 752, 25, 137, 265, 521, 81, 273, 193, 321, 641, 769, 14, 38, 262, 518, 26, 266, 50, 274, 290, 546, 770, 60, 140, 268, 524, 164, 644, 772, 152, 776, 112, 176, 304, 208, 352, 608, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_653, vertices_217, vertices_777, vertices_369, vertices_961, vertices_62, vertices_270, vertices_678, vertices_774, vertices_306, vertices_866, vertices_188, vertices_780, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_521, vertices_81, vertices_273, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_38, vertices_262, vertices_518, vertices_26, vertices_266, vertices_50, vertices_274, vertices_290, vertices_546, vertices_770, vertices_60, vertices_140, vertices_268, vertices_524, vertices_164, vertices_644, vertices_772, vertices_152, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_352, vertices_608, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_653), (false, vertices_217), (false, vertices_777), (false, vertices_369), (false, vertices_961), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_60), (true, vertices_268), (true, vertices_164), (true, vertices_772), (true, vertices_176), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 25 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 16 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_961) then 26 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_60) then 19 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 1 4 6 8 678 38 3
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 14 62 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 678
cert_cover_5 2 1 0 1 4 6 38 678 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 866
cert_cover_5 5 2 0 4 5 7 290 866 2
cert_coverFacet 6 188
cert_cover_5 6 0 1 2 3 6 60 188 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 112 752 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0982

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0983.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0983

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 109, 345, 553, 905, 481, 558, 118, 662, 242, 92, 284, 780, 788, 976, 41, 73, 265, 521, 97, 161, 545, 321, 385, 641, 22, 38, 518, 114, 146, 162, 546, 642, 28, 44, 76, 268, 524, 84, 276, 532, 100, 772, 88, 280, 552, 776, 208, 336, 656, 784, 224, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_109, vertices_345, vertices_553, vertices_905, vertices_481, vertices_558, vertices_118, vertices_662, vertices_242, vertices_92, vertices_284, vertices_780, vertices_788, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_321, vertices_385, vertices_641, vertices_22, vertices_38, vertices_518, vertices_114, vertices_146, vertices_162, vertices_546, vertices_642, vertices_28, vertices_44, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_100, vertices_772, vertices_88, vertices_280, vertices_552, vertices_776, vertices_208, vertices_336, vertices_656, vertices_784, vertices_224, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_109), (false, vertices_345), (false, vertices_553), (false, vertices_905), (false, vertices_481), (true, vertices_22), (true, vertices_38), (true, vertices_518), (true, vertices_114), (true, vertices_146), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_772), (true, vertices_208), (true, vertices_656), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_109) then 19 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_905) then 22 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_114) then 17 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_784) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 553 22 38 518 146 28 268 524 84 276 532 772 208 656 784 675 114 109 345 905 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 38 2
cert_row_2 1 0 3 4 5 114
cert_row_4 2 0 1 3 6 8 662 22 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 2 4 0 3
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 38 558 2
cert_coverFacet 1 118
cert_cover_5 1 1 0 1 3 4 22 118 3
cert_coverFacet 2 662
cert_cover_5 2 2 0 1 3 6 22 662 3
cert_coverFacet 3 242
cert_cover_5 3 1 0 3 4 6 114 242 3
cert_coverFacet 4 92
cert_cover_2 4 2 1 3 5 28 92 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 976
cert_cover_5 8 3 3 5 6 7 208 976 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0983

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0984.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0984

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [87, 539, 195, 899, 533, 805, 453, 218, 682, 60, 540, 556, 372, 248, 992, 19, 67, 131, 515, 21, 69, 261, 517, 529, 193, 385, 769, 26, 138, 522, 82, 194, 642, 28, 44, 524, 52, 84, 532, 292, 548, 324, 56, 216, 536, 168, 552, 112, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_87, vertices_539, vertices_195, vertices_899, vertices_533, vertices_805, vertices_453, vertices_218, vertices_682, vertices_60, vertices_540, vertices_556, vertices_372, vertices_248, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_131, vertices_515, vertices_21, vertices_69, vertices_261, vertices_517, vertices_529, vertices_193, vertices_385, vertices_769, vertices_26, vertices_138, vertices_522, vertices_82, vertices_194, vertices_642, vertices_28, vertices_44, vertices_524, vertices_52, vertices_84, vertices_532, vertices_292, vertices_548, vertices_324, vertices_56, vertices_216, vertices_536, vertices_168, vertices_552, vertices_112, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_87), (false, vertices_539), (false, vertices_195), (false, vertices_899), (false, vertices_533), (false, vertices_805), (false, vertices_453), (true, vertices_138), (true, vertices_28), (true, vertices_44), (true, vertices_524), (true, vertices_52), (true, vertices_56), (true, vertices_216), (true, vertices_168), (true, vertices_552), (true, vertices_112), (true, vertices_224), (true, vertices_352), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_87) then 15 else
  if p.val = (false, vertices_539) then 16 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_216) then 22 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_87), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 138 2
cert_row_2 1 2 3 5 6 216
cert_row_4 2 1 3 4 5 7 372 52 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 2 1 4
cert_heightProof 4
cert_coverFacet 0 218
cert_cover_5 0 1 0 2 3 5 26 218 3
cert_coverFacet 1 682
cert_cover_5 1 0 0 2 4 6 138 682 2
cert_coverFacet 2 60
cert_cover_2 2 2 1 3 4 28 60 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 556
cert_cover_2 4 2 1 4 8 44 556 3
cert_coverFacet 5 372
cert_cover_5 5 2 1 3 4 5 52 372 3
cert_coverFacet 6 248
cert_cover_5 6 1 2 3 4 5 56 248 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0984

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0985.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0985

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 173, 269, 789, 665, 281, 737, 358, 774, 346, 722, 786, 610, 364, 248, 13, 37, 261, 517, 25, 137, 265, 273, 529, 161, 545, 641, 38, 262, 518, 82, 274, 530, 98, 546, 322, 578, 770, 44, 268, 356, 772, 88, 152, 280, 104, 168, 328, 208, 656, 784, 224, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_173, vertices_269, vertices_789, vertices_665, vertices_281, vertices_737, vertices_358, vertices_774, vertices_346, vertices_722, vertices_786, vertices_610, vertices_364, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_261, vertices_517, vertices_25, vertices_137, vertices_265, vertices_273, vertices_529, vertices_161, vertices_545, vertices_641, vertices_38, vertices_262, vertices_518, vertices_82, vertices_274, vertices_530, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_44, vertices_268, vertices_356, vertices_772, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_328, vertices_208, vertices_656, vertices_784, vertices_224, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_173), (false, vertices_269), (false, vertices_789), (false, vertices_665), (false, vertices_281), (false, vertices_737), (true, vertices_262), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_356), (true, vertices_88), (true, vertices_104), (true, vertices_328), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 15 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_356) then 19 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_208) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_356), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 7 356
cert_row_4 1 0 2 3 5 7 346 82 1
cert_row_4 2 0 3 5 6 8 722 82 3
cert_row_4 3 2 3 4 5 6 248 88 2
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 0 0 1 4 5 38 358 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 346
cert_cover_5 2 1 0 2 3 5 82 346 1
cert_coverFacet 3 722
cert_cover_5 3 2 0 3 5 6 82 722 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 610
cert_cover_2 5 4 0 5 8 98 610 3
cert_coverFacet 6 364
cert_cover_5 6 0 1 2 4 5 44 364 3
cert_coverFacet 7 248
cert_cover_5 7 3 2 3 4 5 88 248 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0985

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0986.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0986

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 779, 307, 643, 109, 653, 361, 242, 402, 898, 844, 724, 228, 880, 912, 35, 131, 259, 515, 13, 37, 133, 105, 265, 521, 289, 641, 50, 146, 274, 162, 386, 642, 770, 76, 524, 100, 164, 196, 580, 644, 328, 776, 112, 304, 208, 592, 400, 656, 784, 224, 352, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_779, vertices_307, vertices_643, vertices_109, vertices_653, vertices_361, vertices_242, vertices_402, vertices_898, vertices_844, vertices_724, vertices_228, vertices_880, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_13, vertices_37, vertices_133, vertices_105, vertices_265, vertices_521, vertices_289, vertices_641, vertices_50, vertices_146, vertices_274, vertices_162, vertices_386, vertices_642, vertices_770, vertices_76, vertices_524, vertices_100, vertices_164, vertices_196, vertices_580, vertices_644, vertices_328, vertices_776, vertices_112, vertices_304, vertices_208, vertices_592, vertices_400, vertices_656, vertices_784, vertices_224, vertices_352, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_779), (false, vertices_307), (false, vertices_643), (false, vertices_109), (false, vertices_653), (false, vertices_361), (true, vertices_146), (true, vertices_386), (true, vertices_196), (true, vertices_580), (true, vertices_112), (true, vertices_208), (true, vertices_592), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_224), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 15 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_307) then 17 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_109) then 21 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_832) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_167), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 6 242 50 3
cert_row_4 1 1 2 5 7 8 844 76 3
cert_row_4 2 1 3 5 6 8 724 196 1
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 242
cert_cover_5 0 0 0 3 4 5 50 242 3
cert_coverFacet 1 402
cert_cover_2 1 3 0 6 7 146 402 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 844
cert_cover_5 3 1 1 2 5 7 76 844 3
cert_coverFacet 4 724
cert_cover_5 4 2 1 3 5 6 196 724 1
cert_coverFacet 5 228
cert_cover_2 5 4 1 5 6 100 228 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coverFacet 7 912
cert_cover_2 7 6 3 7 8 400 912 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0986

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0987.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0987

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 117, 217, 561, 913, 481, 110, 270, 566, 774, 362, 92, 668, 780, 968, 49, 81, 145, 529, 97, 289, 545, 193, 385, 769, 14, 38, 262, 518, 106, 266, 290, 546, 770, 28, 76, 268, 524, 52, 84, 532, 100, 772, 88, 152, 200, 328, 648, 776, 560, 656, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_117, vertices_217, vertices_561, vertices_913, vertices_481, vertices_110, vertices_270, vertices_566, vertices_774, vertices_362, vertices_92, vertices_668, vertices_780, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_145, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_385, vertices_769, vertices_14, vertices_38, vertices_262, vertices_518, vertices_106, vertices_266, vertices_290, vertices_546, vertices_770, vertices_28, vertices_76, vertices_268, vertices_524, vertices_52, vertices_84, vertices_532, vertices_100, vertices_772, vertices_88, vertices_152, vertices_200, vertices_328, vertices_648, vertices_776, vertices_560, vertices_656, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_117), (false, vertices_217), (false, vertices_561), (false, vertices_913), (false, vertices_481), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_106), (true, vertices_266), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_532), (true, vertices_772), (true, vertices_328), (true, vertices_648), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_117) then 19 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (false, vertices_913) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_106) then 17 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_776) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 561 14 38 262 518 266 28 76 268 524 532 772 328 648 776 803 106 117 217 913 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 5 6 7 8 968 200 3
cert_row_2 1 0 2 4 5 106
cert_row_4 2 0 1 3 4 8 566 38 2
cert_row_4 3 1 2 3 6 8 668 28 3
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 566
cert_cover_5 2 2 0 1 3 4 38 566 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 362
cert_cover_5 4 1 0 2 4 7 106 362 3
cert_coverFacet 5 92
cert_cover_2 5 2 1 3 5 28 92 3
cert_coverFacet 6 668
cert_cover_5 6 3 1 2 3 6 28 668 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 968
cert_cover_5 8 0 2 5 6 7 200 968 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0987

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0988.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0988

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 677, 345, 625, 433, 705, 558, 398, 710, 602, 330, 428, 792, 808, 816, 49, 81, 273, 161, 545, 193, 321, 577, 385, 641, 14, 134, 518, 74, 266, 522, 194, 322, 578, 386, 44, 396, 164, 548, 644, 88, 280, 536, 296, 552, 328, 776, 304, 560, 592, 784, 416, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_677, vertices_345, vertices_625, vertices_433, vertices_705, vertices_558, vertices_398, vertices_710, vertices_602, vertices_330, vertices_428, vertices_792, vertices_808, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_273, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_14, vertices_134, vertices_518, vertices_74, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_44, vertices_396, vertices_164, vertices_548, vertices_644, vertices_88, vertices_280, vertices_536, vertices_296, vertices_552, vertices_328, vertices_776, vertices_304, vertices_560, vertices_592, vertices_784, vertices_416, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_677), (false, vertices_345), (false, vertices_625), (false, vertices_433), (false, vertices_705), (true, vertices_14), (true, vertices_134), (true, vertices_518), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_578), (true, vertices_44), (true, vertices_396), (true, vertices_536), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_396) then 19 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
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
cert_coverFacet 6 792
cert_cover_2 6 3 2 7 8 280 792 3
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coverFacet 8 816
cert_cover_2 8 4 3 7 8 304 816 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0988

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0989.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0989

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 205, 613, 421, 601, 905, 406, 666, 370, 626, 898, 212, 340, 356, 216, 37, 69, 133, 73, 137, 521, 289, 545, 577, 385, 769, 114, 146, 274, 530, 290, 546, 386, 642, 770, 84, 148, 276, 100, 292, 196, 324, 388, 88, 152, 536, 200, 648, 208, 336, 592, 352, 608, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_205, vertices_613, vertices_421, vertices_601, vertices_905, vertices_406, vertices_666, vertices_370, vertices_626, vertices_898, vertices_212, vertices_340, vertices_356, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_133, vertices_73, vertices_137, vertices_521, vertices_289, vertices_545, vertices_577, vertices_385, vertices_769, vertices_114, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_84, vertices_148, vertices_276, vertices_100, vertices_292, vertices_196, vertices_324, vertices_388, vertices_88, vertices_152, vertices_536, vertices_200, vertices_648, vertices_208, vertices_336, vertices_592, vertices_352, vertices_608, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_205), (false, vertices_613), (false, vertices_421), (false, vertices_601), (false, vertices_905), (true, vertices_114), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_324), (true, vertices_152), (true, vertices_208), (true, vertices_336), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_905) then 22 else
  if p.val = (true, vertices_114) then 15 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_114), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 5 114
cert_row_4 1 0 1 3 6 7 406 146 1
cert_row_4 2 0 2 3 6 8 666 146 1
cert_rows_3
cert_pivot_3 1 4 0
cert_heightProof 3
cert_coverFacet 0 406
cert_cover_5 0 1 0 1 3 6 146 406 1
cert_coverFacet 1 666
cert_cover_5 1 2 0 2 3 6 146 666 1
cert_coverFacet 2 370
cert_cover_5 2 0 0 3 4 7 114 370 3
cert_coverFacet 3 626
cert_cover_5 3 0 0 3 4 8 114 626 3
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 212
cert_cover_2 5 3 1 5 6 84 212 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 356
cert_cover_2 7 4 1 5 7 100 356 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 3 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0989

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0990.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0990

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 659, 771, 157, 85, 357, 849, 426, 682, 866, 92, 620, 300, 396, 728, 131, 259, 515, 21, 69, 133, 261, 81, 145, 529, 321, 769, 170, 290, 546, 386, 642, 770, 28, 44, 76, 140, 268, 84, 100, 292, 388, 88, 152, 296, 552, 584, 392, 648, 592, 656, 352, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_659, vertices_771, vertices_157, vertices_85, vertices_357, vertices_849, vertices_426, vertices_682, vertices_866, vertices_92, vertices_620, vertices_300, vertices_396, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_21, vertices_69, vertices_133, vertices_261, vertices_81, vertices_145, vertices_529, vertices_321, vertices_769, vertices_170, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_76, vertices_140, vertices_268, vertices_84, vertices_100, vertices_292, vertices_388, vertices_88, vertices_152, vertices_296, vertices_552, vertices_584, vertices_392, vertices_648, vertices_592, vertices_656, vertices_352, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_659), (false, vertices_771), (false, vertices_157), (false, vertices_85), (false, vertices_357), (false, vertices_849), (true, vertices_170), (true, vertices_290), (true, vertices_546), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_88), (true, vertices_296), (true, vertices_552), (true, vertices_584), (true, vertices_392), (true, vertices_648), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 14 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 15 else
  if p.val = (false, vertices_659) then 19 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_157) then 16 else
  if p.val = (false, vertices_85) then 1 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_849) then 23 else
  if p.val = (true, vertices_170) then 20 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_170), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 7 8 866 290 2
cert_row_2 1 0 2 4 6 170
cert_row_4 2 1 2 4 5 8 620 44 3
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 426
cert_cover_5 0 1 0 2 4 7 170 426 3
cert_coverFacet 1 682
cert_cover_5 1 1 0 2 4 8 170 682 3
cert_coverFacet 2 866
cert_cover_5 2 0 0 4 5 7 290 866 2
cert_coverFacet 3 92
cert_cover_2 3 2 1 3 5 28 92 3
cert_coverFacet 4 620
cert_cover_5 4 2 1 2 4 5 44 620 3
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 728
cert_cover_5 7 3 2 3 5 6 88 728 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0990

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0991.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0991

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 93, 405, 613, 773, 721, 558, 426, 778, 738, 284, 108, 780, 376, 496, 21, 69, 261, 517, 81, 145, 577, 385, 641, 769, 42, 266, 522, 162, 546, 386, 642, 770, 28, 44, 76, 268, 524, 276, 100, 548, 772, 88, 280, 104, 296, 776, 368, 208, 400, 224, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_93, vertices_405, vertices_613, vertices_773, vertices_721, vertices_558, vertices_426, vertices_778, vertices_738, vertices_284, vertices_108, vertices_780, vertices_376, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_261, vertices_517, vertices_81, vertices_145, vertices_577, vertices_385, vertices_641, vertices_769, vertices_42, vertices_266, vertices_522, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_76, vertices_268, vertices_524, vertices_276, vertices_100, vertices_548, vertices_772, vertices_88, vertices_280, vertices_104, vertices_296, vertices_776, vertices_368, vertices_208, vertices_400, vertices_224, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_93), (false, vertices_405), (false, vertices_613), (false, vertices_773), (false, vertices_721), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_162), (true, vertices_546), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_776), (true, vertices_368), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_368) then 24 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_368), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 7 368
cert_row_4 1 0 1 2 4 8 558 42 1
cert_row_4 2 0 2 4 6 7 426 42 3
cert_row_4 3 0 4 5 6 8 738 162 2
cert_rows
cert_pivot_2 3 1 2 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 42 558 1
cert_coverFacet 1 426
cert_cover_5 1 2 0 2 4 6 42 426 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 738
cert_cover_5 3 3 0 4 5 6 162 738 2
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 376
cert_cover_5 7 0 2 3 4 5 88 376 2
cert_coverFacet 8 496
cert_cover_5 8 0 3 4 5 6 368 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0991

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0992.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0992

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 357, 681, 241, 913, 801, 654, 270, 598, 326, 810, 786, 236, 300, 724, 81, 145, 273, 97, 161, 289, 545, 321, 641, 769, 14, 70, 262, 518, 266, 522, 82, 274, 530, 322, 770, 44, 140, 268, 596, 100, 292, 196, 324, 644, 168, 296, 552, 648, 208, 656, 784, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_357, vertices_681, vertices_241, vertices_913, vertices_801, vertices_654, vertices_270, vertices_598, vertices_326, vertices_810, vertices_786, vertices_236, vertices_300, vertices_724] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_273, vertices_97, vertices_161, vertices_289, vertices_545, vertices_321, vertices_641, vertices_769, vertices_14, vertices_70, vertices_262, vertices_518, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_322, vertices_770, vertices_44, vertices_140, vertices_268, vertices_596, vertices_100, vertices_292, vertices_196, vertices_324, vertices_644, vertices_168, vertices_296, vertices_552, vertices_648, vertices_208, vertices_656, vertices_784, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_357), (false, vertices_681), (false, vertices_241), (false, vertices_913), (false, vertices_801), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_522), (true, vertices_530), (true, vertices_770), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_596), (true, vertices_196), (true, vertices_644), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 16 else
  if p.val = (false, vertices_357) then 18 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_913) then 24 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_268) then 11 else
  if p.val = (true, vertices_596) then 19 else
  if p.val = (true, vertices_196) then 12 else
  if p.val = (true, vertices_644) then 13 else
  if p.val = (true, vertices_296) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 5 8 596
cert_row_4 1 0 2 4 7 8 810 266 2
cert_row_4 2 0 1 2 6 8 654 14 3
cert_row_4 3 1 2 4 5 6 236 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 14 654 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 598
cert_cover_5 2 0 0 1 3 5 70 598 2
cert_coverFacet 3 326
cert_cover_2 3 1 0 5 7 70 326 3
cert_coverFacet 4 810
cert_cover_5 4 1 0 2 4 7 266 810 2
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 236
cert_cover_5 6 3 1 2 4 5 44 236 3
cert_coverFacet 7 300
cert_cover_2 7 2 1 4 7 44 300 3
cert_coverFacet 8 724
cert_cover_5 8 0 1 3 5 6 596 724 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0992

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0993.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0993

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [227, 789, 185, 281, 617, 777, 721, 598, 806, 454, 426, 610, 468, 408, 808, 25, 41, 265, 521, 145, 273, 529, 97, 161, 193, 577, 769, 70, 262, 518, 98, 162, 290, 546, 194, 578, 386, 84, 276, 532, 452, 772, 152, 280, 168, 296, 552, 392, 776, 208, 592, 400, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_789, vertices_185, vertices_281, vertices_617, vertices_777, vertices_721, vertices_598, vertices_806, vertices_454, vertices_426, vertices_610, vertices_468, vertices_408, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_193, vertices_577, vertices_769, vertices_70, vertices_262, vertices_518, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_578, vertices_386, vertices_84, vertices_276, vertices_532, vertices_452, vertices_772, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_392, vertices_776, vertices_208, vertices_592, vertices_400, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_789), (false, vertices_185), (false, vertices_281), (false, vertices_617), (false, vertices_777), (false, vertices_721), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_290), (true, vertices_546), (true, vertices_578), (true, vertices_386), (true, vertices_84), (true, vertices_452), (true, vertices_296), (true, vertices_392), (true, vertices_400), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 15 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_185) then 20 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_452) then 18 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_452), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 70 2
cert_row_2 1 1 5 6 7 452
cert_row_4 2 0 1 4 7 8 806 262 2
cert_row_4 3 0 2 4 6 7 426 162 1
cert_rows
cert_pivot_2 3 5 1 0
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 70 598 2
cert_coverFacet 1 806
cert_cover_5 1 2 0 1 4 7 262 806 2
cert_coverFacet 2 454
cert_cover_5 2 1 0 1 5 6 70 454 3
cert_coverFacet 3 426
cert_cover_5 3 3 0 2 4 6 162 426 1
cert_coverFacet 4 610
cert_cover_2 4 4 0 5 8 98 610 3
cert_coverFacet 5 468
cert_cover_5 5 1 1 3 5 6 84 468 3
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0993

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0994.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0994

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 531, 675, 387, 565, 457, 241, 790, 906, 316, 236, 652, 780, 676, 376, 19, 131, 259, 515, 49, 81, 529, 161, 545, 193, 321, 385, 274, 530, 386, 642, 770, 44, 140, 268, 524, 52, 276, 532, 164, 548, 644, 772, 312, 104, 200, 328, 392, 648, 776, 112, 336, 224, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_531, vertices_675, vertices_387, vertices_565, vertices_457, vertices_241, vertices_790, vertices_906, vertices_316, vertices_236, vertices_652, vertices_780, vertices_676, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_49, vertices_81, vertices_529, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_164, vertices_548, vertices_644, vertices_772, vertices_312, vertices_104, vertices_200, vertices_328, vertices_392, vertices_648, vertices_776, vertices_112, vertices_336, vertices_224, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_531), (false, vertices_675), (false, vertices_387), (false, vertices_565), (false, vertices_457), (false, vertices_241), (true, vertices_770), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_164), (true, vertices_644), (true, vertices_772), (true, vertices_312), (true, vertices_104), (true, vertices_648), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 15 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_565) then 18 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_312) then 21 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_776) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_312), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 5 6 236 44 3
cert_row_2 1 2 3 4 7 312
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 0 2 6 7 8 906 386 1
cert_rows
cert_pivot_2 5 4 1 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 906
cert_cover_5 1 3 0 2 6 7 386 906 1
cert_coverFacet 2 316
cert_cover_5 2 1 1 2 3 4 44 316 2
cert_coverFacet 3 236
cert_cover_5 3 0 1 2 4 5 44 236 3
cert_coverFacet 4 652
cert_cover_2 4 2 1 6 8 140 652 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 376
cert_cover_5 7 1 2 3 4 5 312 376 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0994

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0995.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0995

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 547, 707, 387, 405, 617, 241, 902, 810, 604, 364, 780, 372, 660, 720, 35, 131, 259, 515, 49, 145, 273, 97, 545, 193, 577, 385, 290, 546, 386, 642, 770, 76, 268, 524, 84, 148, 276, 532, 356, 388, 644, 772, 104, 296, 552, 584, 776, 112, 304, 208, 592, 656, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_547, vertices_707, vertices_387, vertices_405, vertices_617, vertices_241, vertices_902, vertices_810, vertices_604, vertices_364, vertices_780, vertices_372, vertices_660, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_49, vertices_145, vertices_273, vertices_97, vertices_545, vertices_193, vertices_577, vertices_385, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_356, vertices_388, vertices_644, vertices_772, vertices_104, vertices_296, vertices_552, vertices_584, vertices_776, vertices_112, vertices_304, vertices_208, vertices_592, vertices_656, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_547), (false, vertices_707), (false, vertices_387), (false, vertices_405), (false, vertices_617), (false, vertices_241), (true, vertices_770), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_532), (true, vertices_356), (true, vertices_644), (true, vertices_772), (true, vertices_296), (true, vertices_776), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 15 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_356) then 19 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_656) then 13 else
  0
cert_priority
cert_nodeAtPriority_44 547 387 770 76 268 524 84 532 644 772 296 776 592 656 307 707 405 356 617 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_2 2 1 4 5 7 356
cert_row_4 3 1 2 3 5 8 604 76 2
cert_rows
cert_pivot_2 6 0 4 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 810
cert_cover_5 1 1 0 2 4 7 290 810 1
cert_coverFacet 2 604
cert_cover_5 2 3 1 2 3 5 76 604 2
cert_coverFacet 3 364
cert_cover_5 3 2 1 2 4 5 76 364 2
cert_coverFacet 4 780
cert_cover_2 4 2 1 7 8 268 780 3
cert_coverFacet 5 372
cert_cover_5 5 2 1 3 4 5 84 372 2
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0995

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0996.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0996

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 229, 601, 425, 201, 865, 118, 406, 806, 282, 538, 626, 220, 420, 408, 73, 137, 265, 521, 97, 161, 289, 193, 577, 769, 22, 38, 262, 26, 266, 522, 114, 274, 530, 546, 770, 84, 148, 100, 164, 292, 196, 388, 88, 152, 280, 536, 200, 392, 592, 400, 608, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_229, vertices_601, vertices_425, vertices_201, vertices_865, vertices_118, vertices_406, vertices_806, vertices_282, vertices_538, vertices_626, vertices_220, vertices_420, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_193, vertices_577, vertices_769, vertices_22, vertices_38, vertices_262, vertices_26, vertices_266, vertices_522, vertices_114, vertices_274, vertices_530, vertices_546, vertices_770, vertices_84, vertices_148, vertices_100, vertices_164, vertices_292, vertices_196, vertices_388, vertices_88, vertices_152, vertices_280, vertices_536, vertices_200, vertices_392, vertices_592, vertices_400, vertices_608, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_229), (false, vertices_601), (false, vertices_425), (false, vertices_201), (false, vertices_865), (true, vertices_22), (true, vertices_38), (true, vertices_262), (true, vertices_26), (true, vertices_114), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_84), (true, vertices_148), (true, vertices_292), (true, vertices_388), (true, vertices_152), (true, vertices_280), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_114) then 17 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 201 22 38 262 26 274 530 546 84 148 292 388 152 280 400 779 114 229 601 425 865
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 38 3
cert_row_2 1 0 3 4 5 114
cert_row_4 2 0 1 3 6 7 406 22 3
cert_row_4 3 1 2 3 5 6 220 84 1
cert_rows
cert_pivot_2 8 4 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 1 0 1 3 4 22 118 3
cert_coverFacet 1 406
cert_cover_5 1 2 0 1 3 6 22 406 3
cert_coverFacet 2 806
cert_cover_5 2 0 0 1 4 7 38 806 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 626
cert_cover_5 5 1 0 3 4 8 114 626 3
cert_coverFacet 6 220
cert_cover_5 6 3 1 2 3 5 84 220 1
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0996

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0997.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0997

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 341, 313, 689, 593, 481, 206, 526, 598, 426, 554, 674, 572, 284, 460, 49, 81, 273, 529, 161, 289, 193, 321, 577, 641, 14, 70, 518, 42, 138, 522, 162, 546, 194, 578, 642, 28, 204, 268, 524, 84, 276, 532, 324, 56, 280, 296, 552, 392, 560, 592, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_341, vertices_313, vertices_689, vertices_593, vertices_481, vertices_206, vertices_526, vertices_598, vertices_426, vertices_554, vertices_674, vertices_572, vertices_284, vertices_460] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_273, vertices_529, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_641, vertices_14, vertices_70, vertices_518, vertices_42, vertices_138, vertices_522, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_204, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_324, vertices_56, vertices_280, vertices_296, vertices_552, vertices_392, vertices_560, vertices_592, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_341), (false, vertices_313), (false, vertices_689), (false, vertices_593), (false, vertices_481), (true, vertices_14), (true, vertices_70), (true, vertices_518), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_162), (true, vertices_546), (true, vertices_28), (true, vertices_204), (true, vertices_268), (true, vertices_524), (true, vertices_532), (true, vertices_552), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (false, vertices_593) then 0 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_162) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_204) then 19 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
cert_nodeAtPriority_9 0 593 1 14 70 518 42 138 522 162 546 28 268 524 532 552 392 707 341 204 313 689 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 42 3
cert_row_2 1 1 2 5 6 204
cert_row_4 2 0 1 3 5 8 598 70 2
cert_row_4 3 1 2 3 4 8 572 28 3
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 598
cert_cover_5 2 2 0 1 3 5 70 598 2
cert_coverFacet 3 426
cert_cover_5 3 0 0 2 4 6 42 426 3
cert_coverFacet 4 554
cert_cover_2 4 2 0 4 8 42 554 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 572
cert_cover_5 6 3 1 2 3 4 28 572 3
cert_coverFacet 7 284
cert_cover_2 7 2 1 3 7 28 284 3
cert_coverFacet 8 460
cert_cover_5 8 1 1 2 5 7 204 460 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0997

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0998.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0998

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 597, 357, 677, 713, 449, 790, 806, 570, 282, 170, 458, 348, 600, 680, 37, 69, 517, 161, 289, 193, 321, 577, 385, 641, 774, 26, 42, 138, 266, 274, 530, 162, 290, 546, 386, 84, 276, 532, 292, 548, 324, 88, 280, 536, 168, 552, 200, 328, 584, 648, 592, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_597, vertices_357, vertices_677, vertices_713, vertices_449, vertices_790, vertices_806, vertices_570, vertices_282, vertices_170, vertices_458, vertices_348, vertices_600, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_774, vertices_26, vertices_42, vertices_138, vertices_266, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_84, vertices_276, vertices_532, vertices_292, vertices_548, vertices_324, vertices_88, vertices_280, vertices_536, vertices_168, vertices_552, vertices_200, vertices_328, vertices_584, vertices_648, vertices_592, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_597), (false, vertices_357), (false, vertices_677), (false, vertices_713), (false, vertices_449), (true, vertices_774), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_276), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_552), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_713) then 23 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_774) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_328) then 14 else
  0
cert_priority
cert_nodeAtPriority_51 449 26 42 138 266 274 530 546 276 88 280 536 168 552 328 419 774 597 357 677 713
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 26 3
cert_row_2 1 0 1 7 8 774
cert_row_4 2 0 2 5 6 7 458 138 2
cert_row_4 3 1 2 3 5 7 348 84 1
cert_rows
cert_pivot_2 4 8 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 774 790 2
cert_coverFacet 1 806
cert_cover_5 1 1 0 1 4 7 774 806 2
cert_coverFacet 2 570
cert_cover_5 2 0 0 2 3 4 26 570 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 170
cert_cover_2 4 2 0 4 6 42 170 3
cert_coverFacet 5 458
cert_cover_5 5 2 0 2 5 6 138 458 2
cert_coverFacet 6 348
cert_cover_5 6 3 1 2 3 5 84 348 1
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coverFacet 8 680
cert_cover_2 8 4 2 6 8 168 680 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0998

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0999.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0999

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 333, 229, 549, 217, 681, 777, 566, 358, 666, 282, 778, 370, 344, 752, 37, 69, 261, 517, 73, 137, 265, 521, 161, 545, 193, 769, 38, 262, 518, 26, 266, 522, 50, 274, 530, 354, 770, 100, 548, 324, 88, 152, 280, 328, 648, 776, 112, 560, 208, 336, 656, 224, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_333, vertices_229, vertices_549, vertices_217, vertices_681, vertices_777, vertices_566, vertices_358, vertices_666, vertices_282, vertices_778, vertices_370, vertices_344, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_521, vertices_161, vertices_545, vertices_193, vertices_769, vertices_38, vertices_262, vertices_518, vertices_26, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_354, vertices_770, vertices_100, vertices_548, vertices_324, vertices_88, vertices_152, vertices_280, vertices_328, vertices_648, vertices_776, vertices_112, vertices_560, vertices_208, vertices_336, vertices_656, vertices_224, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_333), (false, vertices_229), (false, vertices_549), (false, vertices_217), (false, vertices_681), (false, vertices_777), (true, vertices_38), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_354), (true, vertices_280), (true, vertices_112), (true, vertices_560), (true, vertices_336), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_50) then 6 else
  if p.val = (true, vertices_274) then 7 else
  if p.val = (true, vertices_530) then 8 else
  if p.val = (true, vertices_354) then 16 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_656) then 13 else
  0
cert_priority
cert_nodeAtPriority_25 0 549 1 777 38 26 266 522 50 274 530 280 112 560 336 656 775 354 333 229 217 681
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 5 7 354
cert_row_4 1 0 1 3 4 8 566 38 2
cert_row_4 2 0 2 3 6 8 666 26 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 7 1 0 3
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 1 0 1 3 4 38 566 2
cert_coverFacet 1 358
cert_cover_5 1 0 0 1 4 5 38 358 3
cert_coverFacet 2 666
cert_cover_5 2 2 0 2 3 6 26 666 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 370
cert_cover_5 5 0 0 3 4 5 50 370 3
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0999

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_1000.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1000

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 541, 45, 101, 313, 913, 865, 206, 526, 186, 538, 658, 962, 236, 496, 13, 37, 69, 517, 25, 41, 273, 529, 97, 289, 577, 769, 14, 70, 518, 26, 138, 522, 146, 530, 194, 578, 642, 44, 204, 524, 100, 56, 536, 168, 176, 304, 400, 656, 224, 352, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_541, vertices_45, vertices_101, vertices_313, vertices_913, vertices_865, vertices_206, vertices_526, vertices_186, vertices_538, vertices_658, vertices_962, vertices_236, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_517, vertices_25, vertices_41, vertices_273, vertices_529, vertices_97, vertices_289, vertices_577, vertices_769, vertices_14, vertices_70, vertices_518, vertices_26, vertices_138, vertices_522, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_44, vertices_204, vertices_524, vertices_100, vertices_56, vertices_536, vertices_168, vertices_176, vertices_304, vertices_400, vertices_656, vertices_224, vertices_352, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_541), (false, vertices_45), (false, vertices_101), (false, vertices_313), (false, vertices_913), (false, vertices_865), (true, vertices_14), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_194), (true, vertices_642), (true, vertices_204), (true, vertices_168), (true, vertices_176), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 15 else
  if p.val = (false, vertices_541) then 17 else
  if p.val = (false, vertices_45) then 0 else
  if p.val = (false, vertices_101) then 1 else
  if p.val = (false, vertices_313) then 20 else
  if p.val = (false, vertices_913) then 22 else
  if p.val = (false, vertices_865) then 24 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_194) then 8 else
  if p.val = (true, vertices_642) then 9 else
  if p.val = (true, vertices_204) then 18 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_101), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 6 204
cert_row_4 1 0 2 3 4 6 186 26 3
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 186
cert_cover_5 2 1 0 2 3 4 26 186 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 962
cert_cover_5 5 2 0 5 6 7 194 962 3
cert_coverFacet 6 236
cert_cover_5 6 0 1 2 4 5 44 236 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 176 496 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1000

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_1001.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1001

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 181, 341, 677, 121, 865, 398, 646, 186, 618, 778, 674, 404, 856, 408, 21, 165, 261, 517, 49, 81, 97, 545, 321, 769, 134, 262, 518, 42, 138, 266, 522, 162, 546, 642, 770, 148, 276, 388, 644, 56, 88, 152, 280, 104, 584, 392, 776, 176, 336, 400, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_181, vertices_341, vertices_677, vertices_121, vertices_865, vertices_398, vertices_646, vertices_186, vertices_618, vertices_778, vertices_674, vertices_404, vertices_856, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_165, vertices_261, vertices_517, vertices_49, vertices_81, vertices_97, vertices_545, vertices_321, vertices_769, vertices_134, vertices_262, vertices_518, vertices_42, vertices_138, vertices_266, vertices_522, vertices_162, vertices_546, vertices_642, vertices_770, vertices_148, vertices_276, vertices_388, vertices_644, vertices_56, vertices_88, vertices_152, vertices_280, vertices_104, vertices_584, vertices_392, vertices_776, vertices_176, vertices_336, vertices_400, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_181), (false, vertices_341), (false, vertices_677), (false, vertices_121), (false, vertices_865), (true, vertices_134), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_162), (true, vertices_546), (true, vertices_642), (true, vertices_388), (true, vertices_152), (true, vertices_280), (true, vertices_584), (true, vertices_392), (true, vertices_776), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_121) then 22 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_4 1 0 2 3 4 6 186 42 2
cert_row_4 2 0 2 4 5 8 618 42 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 186
cert_cover_5 2 1 0 2 3 4 42 186 2
cert_coverFacet 3 618
cert_cover_5 3 2 0 2 4 5 42 618 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 856
cert_cover_5 7 3 2 3 5 7 88 856 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1001

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3543 : Certifies 3543 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0972.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3544 : Certifies 3544 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0973.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3545 : Certifies 3545 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0974.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3546 : Certifies 3546 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0975.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3547 : Certifies 3547 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0976.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3548 : Certifies 3548 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0977.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3549 : Certifies 3549 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0978.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3550 : Certifies 3550 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0979.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3551 : Certifies 3551 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0980.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3552 : Certifies 3552 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0981.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3553 : Certifies 3553 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0982.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3554 : Certifies 3554 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0983.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3555 : Certifies 3555 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0984.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3556 : Certifies 3556 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0985.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3557 : Certifies 3557 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0986.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3558 : Certifies 3558 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0987.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3559 : Certifies 3559 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0988.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3560 : Certifies 3560 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0989.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3561 : Certifies 3561 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0990.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3562 : Certifies 3562 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0991.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3563 : Certifies 3563 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0992.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3564 : Certifies 3564 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0993.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3565 : Certifies 3565 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0994.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3566 : Certifies 3566 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0995.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3567 : Certifies 3567 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0996.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3568 : Certifies 3568 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0997.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3569 : Certifies 3569 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0998.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3570 : Certifies 3570 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0999.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3571 : Certifies 3571 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1000.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3572 : Certifies 3572 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1001.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B117 (j : Fin 30) :
    Certifies (3543 + j.val) := by
  fin_cases j
  · exact projection_3543
  · exact projection_3544
  · exact projection_3545
  · exact projection_3546
  · exact projection_3547
  · exact projection_3548
  · exact projection_3549
  · exact projection_3550
  · exact projection_3551
  · exact projection_3552
  · exact projection_3553
  · exact projection_3554
  · exact projection_3555
  · exact projection_3556
  · exact projection_3557
  · exact projection_3558
  · exact projection_3559
  · exact projection_3560
  · exact projection_3561
  · exact projection_3562
  · exact projection_3563
  · exact projection_3564
  · exact projection_3565
  · exact projection_3566
  · exact projection_3567
  · exact projection_3568
  · exact projection_3569
  · exact projection_3570
  · exact projection_3571
  · exact projection_3572

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
