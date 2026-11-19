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
/- Source: ProjectionCertificates/R_m15e10q1_0812.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0812

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 565, 357, 901, 233, 673, 790, 570, 282, 714, 330, 898, 124, 348, 680, 37, 261, 517, 97, 161, 545, 193, 321, 385, 641, 26, 74, 266, 522, 274, 530, 194, 322, 386, 642, 770, 92, 52, 276, 532, 100, 324, 772, 56, 280, 104, 168, 552, 200, 328, 648, 560, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_565, vertices_357, vertices_901, vertices_233, vertices_673, vertices_790, vertices_570, vertices_282, vertices_714, vertices_330, vertices_898, vertices_124, vertices_348, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_26, vertices_74, vertices_266, vertices_522, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_92, vertices_52, vertices_276, vertices_532, vertices_100, vertices_324, vertices_772, vertices_56, vertices_280, vertices_104, vertices_168, vertices_552, vertices_200, vertices_328, vertices_648, vertices_560, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_565), (false, vertices_357), (false, vertices_901), (false, vertices_233), (false, vertices_673), (true, vertices_26), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_642), (true, vertices_770), (true, vertices_92), (true, vertices_276), (true, vertices_56), (true, vertices_280), (true, vertices_552), (true, vertices_328), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_565) then 21 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_901) then 23 else
  if p.val = (false, vertices_233) then 18 else
  if p.val = (false, vertices_673) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_92) then 19 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_648) then 14 else
  0
cert_priority
cert_nodeAtPriority_43 673 1 26 2 74 266 522 274 530 642 770 276 56 280 552 328 648 451 233 92 565 357 901
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_2 1 1 2 3 5 92
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 0 2 5 6 8 714 74 3
cert_rows
cert_pivot_2 7 1 3 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 570
cert_cover_5 1 2 0 2 3 4 26 570 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 714
cert_cover_5 3 3 0 2 5 6 74 714 3
cert_coverFacet 4 330
cert_cover_2 4 2 0 5 7 74 330 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 124
cert_cover_5 6 1 1 2 3 4 92 124 3
cert_coverFacet 7 348
cert_cover_5 7 1 1 2 3 7 92 348 3
cert_coverFacet 8 680
cert_cover_2 8 4 2 6 8 168 680 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0812

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0813.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0813

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 173, 333, 613, 425, 849, 678, 346, 666, 394, 786, 418, 204, 724, 216, 13, 37, 69, 169, 265, 289, 545, 321, 577, 769, 26, 138, 266, 274, 530, 162, 290, 546, 386, 642, 770, 76, 140, 164, 548, 196, 580, 644, 88, 152, 200, 328, 392, 208, 336, 592, 656, 784, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_173, vertices_333, vertices_613, vertices_425, vertices_849, vertices_678, vertices_346, vertices_666, vertices_394, vertices_786, vertices_418, vertices_204, vertices_724, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_169, vertices_265, vertices_289, vertices_545, vertices_321, vertices_577, vertices_769, vertices_26, vertices_138, vertices_266, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_88, vertices_152, vertices_200, vertices_328, vertices_392, vertices_208, vertices_336, vertices_592, vertices_656, vertices_784, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_173), (false, vertices_333), (false, vertices_613), (false, vertices_425), (false, vertices_849), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_196), (true, vertices_644), (true, vertices_88), (true, vertices_152), (true, vertices_200), (true, vertices_208), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_173) then 21 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 26 1 138 2 266 274 530 162 386 642 196 644 88 152 200 208 656 803 333 613 173 425 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 162 1
cert_row_4 1 0 2 3 5 7 346 26 3
cert_row_4 2 0 2 3 6 8 666 26 3
cert_row_4 3 1 3 5 6 8 724 196 1
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 162 678 1
cert_coverFacet 1 346
cert_cover_5 1 1 0 2 3 5 26 346 3
cert_coverFacet 2 666
cert_cover_5 2 2 0 2 3 6 26 666 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 204
cert_cover_2 6 2 1 5 6 76 204 3
cert_coverFacet 7 724
cert_cover_5 7 3 1 3 5 6 196 724 1
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0813

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0814.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0814

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 333, 565, 229, 773, 929, 542, 218, 842, 690, 898, 60, 108, 780, 248, 37, 69, 261, 517, 161, 545, 193, 321, 385, 769, 26, 74, 522, 146, 530, 194, 322, 386, 642, 770, 28, 44, 76, 268, 524, 52, 532, 100, 772, 56, 216, 104, 328, 776, 176, 560, 224, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_333, vertices_565, vertices_229, vertices_773, vertices_929, vertices_542, vertices_218, vertices_842, vertices_690, vertices_898, vertices_60, vertices_108, vertices_780, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_261, vertices_517, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_26, vertices_74, vertices_522, vertices_146, vertices_530, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_76, vertices_268, vertices_524, vertices_52, vertices_532, vertices_100, vertices_772, vertices_56, vertices_216, vertices_104, vertices_328, vertices_776, vertices_176, vertices_560, vertices_224, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_333), (false, vertices_565), (false, vertices_229), (false, vertices_773), (false, vertices_929), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_642), (true, vertices_770), (true, vertices_28), (true, vertices_44), (true, vertices_524), (true, vertices_56), (true, vertices_216), (true, vertices_104), (true, vertices_776), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_229) then 20 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_216) then 22 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_176) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 26 1
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_2 2 2 3 5 6 216
cert_row_4 3 0 3 4 6 8 690 146 2
cert_rows
cert_pivot_2 1 7 2 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 26 542 1
cert_coverFacet 1 218
cert_cover_5 1 2 0 2 3 5 26 218 3
cert_coverFacet 2 842
cert_cover_5 2 1 0 2 5 7 74 842 3
cert_coverFacet 3 690
cert_cover_5 3 3 0 3 4 6 146 690 2
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 108
cert_cover_2 6 2 1 4 5 44 108 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 248
cert_cover_5 8 2 2 3 4 5 56 248 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0814

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0815.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0815

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 267, 787, 611, 157, 281, 721, 806, 330, 354, 796, 428, 660, 740, 488, 11, 67, 259, 515, 25, 137, 265, 145, 273, 529, 193, 577, 74, 266, 98, 290, 546, 322, 770, 28, 140, 268, 148, 532, 164, 292, 548, 644, 772, 280, 424, 200, 328, 656, 784, 224, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_267, vertices_787, vertices_611, vertices_157, vertices_281, vertices_721, vertices_806, vertices_330, vertices_354, vertices_796, vertices_428, vertices_660, vertices_740, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_259, vertices_515, vertices_25, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_74, vertices_266, vertices_98, vertices_290, vertices_546, vertices_322, vertices_770, vertices_28, vertices_140, vertices_268, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_280, vertices_424, vertices_200, vertices_328, vertices_656, vertices_784, vertices_224, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_267), (false, vertices_787), (false, vertices_611), (false, vertices_157), (false, vertices_281), (false, vertices_721), (true, vertices_290), (true, vertices_322), (true, vertices_268), (true, vertices_532), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_424), (true, vertices_328), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_157) then 19 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_424) then 21 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_424), by decide +kernel⟩
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
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_4 1 1 2 3 7 8 796 28 3
cert_row_2 2 2 4 6 7 424
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 0 3 2 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 330
cert_cover_2 1 2 0 5 7 74 330 3
cert_coverFacet 2 354
cert_cover_2 2 4 0 5 7 98 354 3
cert_coverFacet 3 796
cert_cover_5 3 1 1 2 3 7 28 796 3
cert_coverFacet 4 428
cert_cover_5 4 2 1 2 4 6 140 428 2
cert_coverFacet 5 660
cert_cover_2 5 3 1 6 8 148 660 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 164 740 2
cert_coverFacet 7 488
cert_cover_5 7 2 2 4 5 6 424 488 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0815

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0816.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0816

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 93, 781, 789, 105, 425, 241, 662, 810, 786, 738, 418, 620, 212, 708, 13, 21, 773, 41, 73, 265, 81, 145, 273, 97, 161, 385, 146, 274, 530, 162, 290, 546, 386, 642, 770, 76, 524, 84, 148, 532, 196, 580, 644, 104, 296, 552, 776, 208, 784, 224, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_93, vertices_781, vertices_789, vertices_105, vertices_425, vertices_241, vertices_662, vertices_810, vertices_786, vertices_738, vertices_418, vertices_620, vertices_212, vertices_708] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_773, vertices_41, vertices_73, vertices_265, vertices_81, vertices_145, vertices_273, vertices_97, vertices_161, vertices_385, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_524, vertices_84, vertices_148, vertices_532, vertices_196, vertices_580, vertices_644, vertices_104, vertices_296, vertices_552, vertices_776, vertices_208, vertices_784, vertices_224, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_93), (false, vertices_781), (false, vertices_789), (false, vertices_105), (false, vertices_425), (false, vertices_241), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_770), (true, vertices_148), (true, vertices_196), (true, vertices_580), (true, vertices_644), (true, vertices_552), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 15 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_105) then 0 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_105), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 1 2 4 5 8 620 76 2
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 810
cert_cover_5 1 1 0 2 4 7 290 810 1
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 738
cert_cover_5 3 2 0 4 5 6 162 738 2
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 620
cert_cover_5 5 3 1 2 4 5 76 620 2
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0816

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0817.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0817

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 589, 681, 457, 625, 353, 654, 566, 150, 370, 402, 674, 348, 412, 596, 73, 137, 521, 97, 161, 289, 545, 321, 577, 385, 22, 134, 518, 50, 146, 274, 162, 290, 546, 386, 642, 284, 76, 140, 524, 84, 148, 532, 580, 328, 392, 648, 112, 560, 336, 592, 400, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_589, vertices_681, vertices_457, vertices_625, vertices_353, vertices_654, vertices_566, vertices_150, vertices_370, vertices_402, vertices_674, vertices_348, vertices_412, vertices_596] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_521, vertices_97, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_22, vertices_134, vertices_518, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_284, vertices_76, vertices_140, vertices_524, vertices_84, vertices_148, vertices_532, vertices_580, vertices_328, vertices_392, vertices_648, vertices_112, vertices_560, vertices_336, vertices_592, vertices_400, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_589), (false, vertices_681), (false, vertices_457), (false, vertices_625), (false, vertices_353), (true, vertices_22), (true, vertices_134), (true, vertices_518), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_546), (true, vertices_642), (true, vertices_284), (true, vertices_140), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (false, vertices_353) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_284) then 19 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_148) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 353 2 22 1 134 3 518 50 146 274 546 642 140 84 148 532 336 400 419 589 284 681 457 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 134 2
cert_row_2 1 1 2 3 7 284
cert_row_4 2 0 1 3 4 8 566 22 3
cert_row_4 3 0 3 4 5 7 370 50 3
cert_rows
cert_pivot_2 6 2 1 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 134 654 2
cert_coverFacet 1 566
cert_cover_5 1 2 0 1 3 4 22 566 3
cert_coverFacet 2 150
cert_cover_2 2 1 0 3 6 22 150 3
cert_coverFacet 3 370
cert_cover_5 3 3 0 3 4 5 50 370 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 348
cert_cover_5 6 1 1 2 3 5 284 348 3
cert_coverFacet 7 412
cert_cover_5 7 1 1 2 3 6 284 412 3
cert_coverFacet 8 596
cert_cover_2 8 3 1 5 8 84 596 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0817

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0818.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0818

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 453, 601, 425, 329, 737, 598, 406, 678, 58, 538, 434, 348, 708, 312, 41, 73, 265, 521, 161, 545, 193, 321, 577, 385, 22, 134, 518, 26, 42, 522, 50, 402, 530, 162, 546, 84, 276, 196, 324, 580, 388, 644, 56, 88, 280, 536, 296, 328, 304, 592, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_453, vertices_601, vertices_425, vertices_329, vertices_737, vertices_598, vertices_406, vertices_678, vertices_58, vertices_538, vertices_434, vertices_348, vertices_708, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_521, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_22, vertices_134, vertices_518, vertices_26, vertices_42, vertices_522, vertices_50, vertices_402, vertices_530, vertices_162, vertices_546, vertices_84, vertices_276, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_56, vertices_88, vertices_280, vertices_536, vertices_296, vertices_328, vertices_304, vertices_592, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_453), (false, vertices_601), (false, vertices_425), (false, vertices_329), (false, vertices_737), (true, vertices_22), (true, vertices_134), (true, vertices_518), (true, vertices_26), (true, vertices_50), (true, vertices_402), (true, vertices_530), (true, vertices_162), (true, vertices_84), (true, vertices_276), (true, vertices_580), (true, vertices_644), (true, vertices_56), (true, vertices_280), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 16 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_402) then 17 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_162) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_304) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 329 22 134 518 26 50 530 162 84 276 580 644 56 280 304 555 402 453 601 425 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 134 2
cert_row_2 1 0 3 6 7 402
cert_row_4 2 0 1 3 5 8 598 22 3
cert_row_4 3 1 2 3 5 7 348 84 1
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 2 0 1 3 5 22 598 3
cert_coverFacet 1 406
cert_cover_5 1 1 0 1 3 6 22 406 3
cert_coverFacet 2 678
cert_cover_5 2 0 0 1 4 6 134 678 2
cert_coverFacet 3 58
cert_cover_2 3 2 0 3 4 26 58 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 434
cert_cover_5 5 1 0 3 4 6 50 434 3
cert_coverFacet 6 348
cert_cover_5 6 3 1 2 3 5 84 348 1
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0818

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0819.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0819

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 309, 213, 613, 809, 721, 406, 618, 458, 778, 658, 706, 236, 420, 424, 21, 37, 69, 209, 273, 529, 289, 545, 577, 769, 74, 266, 522, 146, 274, 530, 194, 578, 386, 642, 770, 148, 276, 100, 164, 292, 196, 388, 104, 168, 296, 552, 200, 392, 776, 656, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_309, vertices_213, vertices_613, vertices_809, vertices_721, vertices_406, vertices_618, vertices_458, vertices_778, vertices_658, vertices_706, vertices_236, vertices_420, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_69, vertices_209, vertices_273, vertices_529, vertices_289, vertices_545, vertices_577, vertices_769, vertices_74, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_148, vertices_276, vertices_100, vertices_164, vertices_292, vertices_196, vertices_388, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_392, vertices_776, vertices_656, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_309), (false, vertices_213), (false, vertices_613), (false, vertices_809), (false, vertices_721), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_194), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_164), (true, vertices_388), (true, vertices_104), (true, vertices_168), (true, vertices_200), (true, vertices_392), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_309) then 18 else
  if p.val = (false, vertices_213) then 23 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 7 406 146 1
cert_row_4 1 0 2 4 5 8 618 74 2
cert_row_4 2 0 2 5 6 7 458 74 3
cert_row_4 3 1 2 4 5 6 236 100 1
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 146 406 1
cert_coverFacet 1 618
cert_cover_5 1 1 0 2 4 5 74 618 2
cert_coverFacet 2 458
cert_cover_5 2 2 0 2 5 6 74 458 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 236
cert_cover_5 6 3 1 2 4 5 100 236 1
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0819

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0820.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0820

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 333, 613, 901, 201, 721, 806, 666, 282, 626, 306, 898, 124, 316, 216, 69, 261, 517, 73, 137, 265, 193, 577, 385, 641, 26, 138, 266, 50, 274, 530, 290, 546, 386, 642, 770, 60, 76, 268, 100, 292, 548, 772, 88, 152, 280, 200, 112, 304, 208, 592, 656, 608, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_333, vertices_613, vertices_901, vertices_201, vertices_721, vertices_806, vertices_666, vertices_282, vertices_626, vertices_306, vertices_898, vertices_124, vertices_316, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_193, vertices_577, vertices_385, vertices_641, vertices_26, vertices_138, vertices_266, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_268, vertices_100, vertices_292, vertices_548, vertices_772, vertices_88, vertices_152, vertices_280, vertices_200, vertices_112, vertices_304, vertices_208, vertices_592, vertices_656, vertices_608, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_333), (false, vertices_613), (false, vertices_901), (false, vertices_201), (false, vertices_721), (true, vertices_26), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_770), (true, vertices_60), (true, vertices_292), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_112), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_901) then 22 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_60) then 19 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_304) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 201 1 26 2 50 3 274 530 290 546 642 770 292 88 152 280 112 304 395 333 60 613 901 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 2 3 6 8 666 26 3
cert_row_4 3 0 3 4 5 8 626 50 3
cert_rows
cert_pivot_2 7 1 2 0
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 666
cert_cover_5 1 2 0 2 3 6 26 666 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 626
cert_cover_5 3 3 0 3 4 5 50 626 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 124
cert_cover_5 6 1 1 2 3 5 60 124 3
cert_coverFacet 7 316
cert_cover_5 7 1 1 2 3 7 60 316 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0820

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0821.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0821

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 563, 227, 771, 205, 681, 777, 790, 306, 354, 844, 652, 692, 468, 496, 35, 67, 259, 515, 73, 137, 265, 521, 161, 545, 193, 769, 50, 274, 530, 98, 290, 322, 770, 76, 140, 524, 148, 276, 532, 196, 324, 644, 772, 328, 648, 776, 176, 304, 560, 464, 224, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_563, vertices_227, vertices_771, vertices_205, vertices_681, vertices_777, vertices_790, vertices_306, vertices_354, vertices_844, vertices_652, vertices_692, vertices_468, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_259, vertices_515, vertices_73, vertices_137, vertices_265, vertices_521, vertices_161, vertices_545, vertices_193, vertices_769, vertices_50, vertices_274, vertices_530, vertices_98, vertices_290, vertices_322, vertices_770, vertices_76, vertices_140, vertices_524, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_644, vertices_772, vertices_328, vertices_648, vertices_776, vertices_176, vertices_304, vertices_560, vertices_464, vertices_224, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_563), (false, vertices_227), (false, vertices_771), (false, vertices_205), (false, vertices_681), (false, vertices_777), (true, vertices_274), (true, vertices_290), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_324), (true, vertices_644), (true, vertices_772), (true, vertices_176), (true, vertices_304), (true, vertices_464), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_227) then 17 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_205) then 19 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_464) then 23 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(true, vertices_464), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_4 1 1 2 5 7 8 844 76 3
cert_row_2 2 3 5 6 7 464
cert_row_4 3 1 3 4 6 8 692 148 2
cert_rows
cert_pivot_2 0 2 5 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 306
cert_cover_2 1 3 0 4 7 50 306 3
cert_coverFacet 2 354
cert_cover_2 2 4 0 5 7 98 354 3
cert_coverFacet 3 844
cert_cover_5 3 1 1 2 5 7 76 844 3
cert_coverFacet 4 652
cert_cover_2 4 2 1 6 8 140 652 3
cert_coverFacet 5 692
cert_cover_5 5 3 1 3 4 6 148 692 2
cert_coverFacet 6 468
cert_cover_5 6 2 1 3 5 6 148 468 2
cert_coverFacet 7 496
cert_cover_5 7 2 3 4 5 6 176 496 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0821

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0822.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0822

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 173, 269, 789, 613, 929, 598, 218, 794, 738, 898, 60, 284, 116, 248, 13, 37, 261, 517, 137, 265, 161, 545, 385, 769, 26, 138, 266, 82, 530, 194, 578, 386, 642, 770, 28, 44, 268, 52, 84, 276, 532, 100, 580, 56, 216, 280, 168, 112, 784, 224, 608, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_173, vertices_269, vertices_789, vertices_613, vertices_929, vertices_598, vertices_218, vertices_794, vertices_738, vertices_898, vertices_60, vertices_284, vertices_116, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_261, vertices_517, vertices_137, vertices_265, vertices_161, vertices_545, vertices_385, vertices_769, vertices_26, vertices_138, vertices_266, vertices_82, vertices_530, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_52, vertices_84, vertices_276, vertices_532, vertices_100, vertices_580, vertices_56, vertices_216, vertices_280, vertices_168, vertices_112, vertices_784, vertices_224, vertices_608, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_173), (false, vertices_269), (false, vertices_789), (false, vertices_613), (false, vertices_929), (true, vertices_26), (true, vertices_82), (true, vertices_530), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_28), (true, vertices_52), (true, vertices_84), (true, vertices_56), (true, vertices_216), (true, vertices_280), (true, vertices_112), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_173) then 18 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_216) then 22 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 82 1
cert_row_4 1 0 2 3 7 8 794 26 3
cert_row_2 2 2 3 5 6 216
cert_row_4 3 0 4 5 6 8 738 194 1
cert_rows
cert_pivot_2 1 7 2 0
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 82 598 1
cert_coverFacet 1 218
cert_cover_5 1 2 0 2 3 5 26 218 3
cert_coverFacet 2 794
cert_cover_5 2 1 0 2 3 7 26 794 3
cert_coverFacet 3 738
cert_cover_5 3 3 0 4 5 6 194 738 1
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 116
cert_cover_2 7 3 1 4 5 52 116 3
cert_coverFacet 8 248
cert_cover_5 8 2 2 3 4 5 56 248 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0822

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0823.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0823

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 563, 227, 789, 389, 409, 241, 714, 866, 844, 396, 652, 376, 216, 816, 35, 131, 515, 133, 261, 517, 49, 145, 273, 529, 225, 385, 98, 546, 194, 578, 642, 140, 268, 524, 388, 644, 772, 88, 152, 280, 200, 328, 584, 392, 648, 112, 304, 560, 208, 784, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_563, vertices_227, vertices_789, vertices_389, vertices_409, vertices_241, vertices_714, vertices_866, vertices_844, vertices_396, vertices_652, vertices_376, vertices_216, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_133, vertices_261, vertices_517, vertices_49, vertices_145, vertices_273, vertices_529, vertices_225, vertices_385, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_140, vertices_268, vertices_524, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_112, vertices_304, vertices_560, vertices_208, vertices_784, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_563), (false, vertices_227), (false, vertices_789), (false, vertices_389), (false, vertices_409), (false, vertices_241), (true, vertices_578), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_88), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_648), (true, vertices_304), (true, vertices_352), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 21 22 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_227) then 23 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 194 1
cert_row_4 1 0 4 5 7 8 866 98 3
cert_row_4 2 1 2 5 7 8 844 268 2
cert_row_4 3 2 3 4 5 7 376 88 2
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 714
cert_cover_5 0 0 0 2 5 6 194 714 1
cert_coverFacet 1 866
cert_cover_5 1 1 0 4 5 7 98 866 3
cert_coverFacet 2 844
cert_cover_5 2 2 1 2 5 7 268 844 2
cert_coverFacet 3 396
cert_cover_2 3 2 1 6 7 140 396 3
cert_coverFacet 4 652
cert_cover_2 4 2 1 6 8 140 652 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 88 376 2
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 816
cert_cover_2 7 4 3 7 8 304 816 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0823

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0824.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0824

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 301, 653, 789, 217, 281, 593, 806, 682, 850, 482, 556, 184, 312, 496, 13, 261, 517, 25, 137, 265, 81, 273, 529, 193, 577, 641, 162, 290, 546, 194, 322, 578, 642, 770, 44, 524, 292, 548, 772, 56, 152, 280, 168, 296, 552, 648, 176, 304, 208, 336, 592, 784, 480]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_301, vertices_653, vertices_789, vertices_217, vertices_281, vertices_593, vertices_806, vertices_682, vertices_850, vertices_482, vertices_556, vertices_184, vertices_312, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_261, vertices_517, vertices_25, vertices_137, vertices_265, vertices_81, vertices_273, vertices_529, vertices_193, vertices_577, vertices_641, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_44, vertices_524, vertices_292, vertices_548, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_648, vertices_176, vertices_304, vertices_208, vertices_336, vertices_592, vertices_784, vertices_480] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_301), (false, vertices_653), (false, vertices_789), (false, vertices_217), (false, vertices_281), (false, vertices_593), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_770), (true, vertices_548), (true, vertices_56), (true, vertices_168), (true, vertices_552), (true, vertices_176), (true, vertices_304), (true, vertices_336), (true, vertices_480)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_301) then 17 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_593) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_480) then 24 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(true, vertices_480), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_4 1 0 2 4 6 8 682 162 1
cert_row_2 2 4 5 6 7 480
cert_row_4 3 0 3 5 7 8 850 322 1
cert_rows
cert_pivot_2 1 2 4 0
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 682
cert_cover_5 1 1 0 2 4 6 162 682 1
cert_coverFacet 2 850
cert_cover_5 2 3 0 3 5 7 322 850 1
cert_coverFacet 3 482
cert_cover_5 3 2 0 4 5 6 162 482 2
cert_coverFacet 4 556
cert_cover_2 4 2 1 4 8 44 556 3
cert_coverFacet 5 184
cert_cover_2 5 3 2 4 6 56 184 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 496
cert_cover_5 7 2 3 4 5 6 176 496 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0824

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0825.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0825

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 213, 277, 677, 773, 233, 625, 902, 346, 602, 682, 394, 460, 340, 616, 21, 133, 261, 517, 81, 273, 529, 97, 161, 545, 193, 769, 90, 138, 266, 522, 274, 530, 386, 642, 770, 84, 276, 196, 324, 388, 644, 772, 104, 168, 552, 200, 328, 584, 392, 336, 592, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_213, vertices_277, vertices_677, vertices_773, vertices_233, vertices_625, vertices_902, vertices_346, vertices_602, vertices_682, vertices_394, vertices_460, vertices_340, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_81, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_193, vertices_769, vertices_90, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_84, vertices_276, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_104, vertices_168, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_336, vertices_592, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_213), (false, vertices_277), (false, vertices_677), (false, vertices_773), (false, vertices_233), (false, vertices_625), (true, vertices_90), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_386), (true, vertices_642), (true, vertices_324), (true, vertices_388), (true, vertices_552), (true, vertices_328), (true, vertices_584), (true, vertices_392), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_773) then 1 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (true, vertices_90) then 16 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_336) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 277 1 773 138 266 522 386 642 324 388 552 328 584 392 336 787 90 213 677 233 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 2 4 6 8 682 138 2
cert_row_4 2 0 1 6 7 8 902 386 1
cert_row_4 3 1 2 5 6 7 460 196 1
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 2 0 1 6 7 386 902 1
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 7 90 346 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 8 90 602 3
cert_coverFacet 3 682
cert_cover_5 3 1 0 2 4 6 138 682 2
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 460
cert_cover_5 5 3 1 2 5 6 196 460 1
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0825

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0826.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0826

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 653, 773, 233, 841, 369, 417, 598, 150, 838, 434, 338, 692, 632, 680, 133, 261, 517, 73, 137, 521, 97, 161, 289, 321, 385, 769, 22, 582, 134, 262, 82, 146, 274, 322, 386, 148, 532, 644, 772, 104, 168, 552, 584, 648, 112, 176, 304, 560, 336, 592, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_653, vertices_773, vertices_233, vertices_841, vertices_369, vertices_417, vertices_598, vertices_150, vertices_838, vertices_434, vertices_338, vertices_692, vertices_632, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_97, vertices_161, vertices_289, vertices_321, vertices_385, vertices_769, vertices_22, vertices_582, vertices_134, vertices_262, vertices_82, vertices_146, vertices_274, vertices_322, vertices_386, vertices_148, vertices_532, vertices_644, vertices_772, vertices_104, vertices_168, vertices_552, vertices_584, vertices_648, vertices_112, vertices_176, vertices_304, vertices_560, vertices_336, vertices_592, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_653), (false, vertices_773), (false, vertices_233), (false, vertices_841), (false, vertices_369), (false, vertices_417), (true, vertices_22), (true, vertices_582), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_322), (true, vertices_148), (true, vertices_532), (true, vertices_552), (true, vertices_176), (true, vertices_560), (true, vertices_592), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 15 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_417) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_582) then 16 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_582), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 7 434 146 2
cert_row_2 1 0 1 5 8 582
cert_row_4 2 1 3 4 6 8 692 148 2
cert_row_4 3 2 3 4 5 8 632 104 1
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 1 0 1 3 5 22 598 3
cert_coverFacet 1 150
cert_cover_2 1 1 0 3 6 22 150 3
cert_coverFacet 2 838
cert_cover_5 2 1 0 1 5 7 582 838 3
cert_coverFacet 3 434
cert_cover_5 3 0 0 3 4 6 146 434 2
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 692
cert_cover_5 5 2 1 3 4 6 148 692 2
cert_coverFacet 6 632
cert_cover_5 6 3 2 3 4 5 104 632 1
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0826

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0828.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0828

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 597, 149, 453, 793, 361, 585, 662, 810, 786, 482, 674, 236, 684, 588, 21, 69, 133, 73, 265, 521, 145, 273, 529, 321, 577, 385, 146, 274, 530, 162, 290, 546, 386, 642, 770, 172, 76, 524, 148, 532, 196, 580, 644, 104, 296, 552, 584, 776, 784, 224, 352, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_597, vertices_149, vertices_453, vertices_793, vertices_361, vertices_585, vertices_662, vertices_810, vertices_786, vertices_482, vertices_674, vertices_236, vertices_684, vertices_588] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_133, vertices_73, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_321, vertices_577, vertices_385, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_172, vertices_76, vertices_524, vertices_148, vertices_532, vertices_196, vertices_580, vertices_644, vertices_104, vertices_296, vertices_552, vertices_584, vertices_776, vertices_784, vertices_224, vertices_352, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_597), (false, vertices_149), (false, vertices_453), (false, vertices_793), (false, vertices_361), (false, vertices_585), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_770), (true, vertices_172), (true, vertices_76), (true, vertices_524), (true, vertices_644), (true, vertices_552), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 15 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_585) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_172) then 19 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_172), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
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
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_2 1 1 2 4 6 172
cert_row_4 2 0 2 4 7 8 810 290 1
cert_row_4 3 0 4 5 6 7 482 162 2
cert_rows
cert_pivot_2 3 1 2 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 810
cert_cover_5 1 2 0 2 4 7 290 810 1
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 482
cert_cover_5 3 3 0 4 5 6 162 482 2
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 236
cert_cover_5 5 1 1 2 4 5 172 236 3
cert_coverFacet 6 684
cert_cover_5 6 1 1 2 4 8 172 684 3
cert_coverFacet 7 588
cert_cover_2 7 2 1 5 8 76 588 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0828

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0829.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0829

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 781, 213, 661, 357, 457, 806, 426, 778, 626, 178, 658, 596, 612, 496, 149, 69, 261, 517, 137, 265, 521, 193, 321, 641, 138, 266, 522, 50, 146, 530, 162, 290, 546, 642, 770, 84, 532, 100, 292, 548, 580, 772, 392, 776, 112, 176, 208, 592, 656, 352, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_781, vertices_213, vertices_661, vertices_357, vertices_457, vertices_806, vertices_426, vertices_778, vertices_626, vertices_178, vertices_658, vertices_596, vertices_612, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_149, vertices_69, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_641, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_84, vertices_532, vertices_100, vertices_292, vertices_548, vertices_580, vertices_772, vertices_392, vertices_776, vertices_112, vertices_176, vertices_208, vertices_592, vertices_656, vertices_352, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_781), (false, vertices_213), (false, vertices_661), (false, vertices_357), (false, vertices_457), (true, vertices_266), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_548), (true, vertices_580), (true, vertices_112), (true, vertices_176), (true, vertices_592), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_213) then 21 else
  if p.val = (false, vertices_661) then 22 else
  if p.val = (false, vertices_357) then 23 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_42 266 1 50 2 146 530 162 290 546 770 548 580 112 176 592 608 416 651 781 457 213 661 357
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_4 1 0 2 4 6 7 426 138 2
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 426
cert_cover_5 1 1 0 2 4 6 138 426 2
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 626
cert_cover_5 3 2 0 3 4 5 50 626 3
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 612
cert_cover_2 7 4 1 5 8 100 612 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0829

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0830.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0830

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 779, 227, 643, 101, 805, 689, 666, 202, 330, 412, 460, 244, 308, 824, 67, 131, 259, 515, 37, 69, 261, 97, 161, 545, 641, 769, 74, 138, 266, 522, 194, 322, 642, 396, 52, 148, 276, 100, 292, 196, 324, 152, 280, 536, 200, 328, 776, 176, 304, 560, 656, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_779, vertices_227, vertices_643, vertices_101, vertices_805, vertices_689, vertices_666, vertices_202, vertices_330, vertices_412, vertices_460, vertices_244, vertices_308, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_37, vertices_69, vertices_261, vertices_97, vertices_161, vertices_545, vertices_641, vertices_769, vertices_74, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_642, vertices_396, vertices_52, vertices_148, vertices_276, vertices_100, vertices_292, vertices_196, vertices_324, vertices_152, vertices_280, vertices_536, vertices_200, vertices_328, vertices_776, vertices_176, vertices_304, vertices_560, vertices_656, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_779), (false, vertices_227), (false, vertices_643), (false, vertices_101), (false, vertices_805), (false, vertices_689), (true, vertices_74), (true, vertices_138), (true, vertices_396), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_196), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_200), (true, vertices_328), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 15 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_227) then 17 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_101) then 1 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_396) then 20 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_304) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_101), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 138 2
cert_row_4 1 1 3 4 5 6 244 52 3
cert_row_2 2 1 2 6 7 396
cert_row_4 3 2 3 4 7 8 824 280 2
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 666
cert_cover_5 0 0 0 2 3 6 138 666 2
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 330
cert_cover_2 2 2 0 5 7 74 330 3
cert_coverFacet 3 412
cert_cover_5 3 2 1 2 3 6 396 412 2
cert_coverFacet 4 460
cert_cover_5 4 2 1 2 5 6 396 460 2
cert_coverFacet 5 244
cert_cover_5 5 1 1 3 4 5 52 244 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 824
cert_cover_5 7 3 2 3 4 7 280 824 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0830

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0831.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0831

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 789, 357, 313, 689, 609, 398, 782, 198, 666, 738, 452, 184, 792, 488, 69, 261, 517, 49, 273, 529, 97, 289, 545, 577, 270, 70, 134, 518, 138, 522, 194, 578, 642, 196, 324, 388, 772, 56, 152, 280, 536, 168, 296, 392, 776, 176, 656, 784, 224, 352, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_789, vertices_357, vertices_313, vertices_689, vertices_609, vertices_398, vertices_782, vertices_198, vertices_666, vertices_738, vertices_452, vertices_184, vertices_792, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_577, vertices_270, vertices_70, vertices_134, vertices_518, vertices_138, vertices_522, vertices_194, vertices_578, vertices_642, vertices_196, vertices_324, vertices_388, vertices_772, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_392, vertices_776, vertices_176, vertices_656, vertices_784, vertices_224, vertices_352, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_789), (false, vertices_357), (false, vertices_313), (false, vertices_689), (false, vertices_609), (true, vertices_270), (true, vertices_134), (true, vertices_138), (true, vertices_522), (true, vertices_194), (true, vertices_642), (true, vertices_196), (true, vertices_388), (true, vertices_152), (true, vertices_536), (true, vertices_168), (true, vertices_392), (true, vertices_776), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 16 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (false, vertices_609) then 0 else
  if p.val = (true, vertices_270) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 609 134 138 522 194 642 196 388 152 536 168 392 776 224 448 583 270 789 357 313 689
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 7 270
cert_row_4 1 0 2 3 6 8 666 138 2
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 270 398 3
cert_coverFacet 1 782
cert_cover_5 1 0 0 1 2 8 270 782 3
cert_coverFacet 2 198
cert_cover_2 2 1 0 5 6 70 198 3
cert_coverFacet 3 666
cert_cover_5 3 1 0 2 3 6 138 666 2
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 194 738 1
cert_coverFacet 5 452
cert_cover_2 5 5 1 6 7 196 452 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 168 488 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0831

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0832.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0832

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 307, 387, 643, 453, 361, 713, 406, 562, 722, 604, 812, 332, 820, 212, 35, 131, 259, 515, 41, 73, 521, 289, 193, 321, 385, 641, 50, 146, 274, 530, 546, 386, 642, 76, 268, 524, 84, 148, 276, 532, 804, 196, 324, 388, 296, 552, 328, 584, 304, 560, 208, 592, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_307, vertices_387, vertices_643, vertices_453, vertices_361, vertices_713, vertices_406, vertices_562, vertices_722, vertices_604, vertices_812, vertices_332, vertices_820, vertices_212] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_41, vertices_73, vertices_521, vertices_289, vertices_193, vertices_321, vertices_385, vertices_641, vertices_50, vertices_146, vertices_274, vertices_530, vertices_546, vertices_386, vertices_642, vertices_76, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_804, vertices_196, vertices_324, vertices_388, vertices_296, vertices_552, vertices_328, vertices_584, vertices_304, vertices_560, vertices_208, vertices_592, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_307), (false, vertices_387), (false, vertices_643), (false, vertices_453), (false, vertices_361), (false, vertices_713), (true, vertices_146), (true, vertices_530), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_804), (true, vertices_560), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 15 else
  if p.val = (false, vertices_307) then 16 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_643) then 1 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_804) then 19 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_592) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 20 => Sum.inl 2
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
cert_row_2 0 1 4 7 8 804
cert_row_4 1 0 1 3 6 7 406 146 1
cert_row_4 2 0 3 5 6 8 722 146 2
cert_row_4 3 1 2 3 5 8 604 76 2
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 1 0 1 3 6 146 406 1
cert_coverFacet 1 562
cert_cover_2 1 3 0 4 8 50 562 3
cert_coverFacet 2 722
cert_cover_5 2 2 0 3 5 6 146 722 2
cert_coverFacet 3 604
cert_cover_5 3 3 1 2 3 5 76 604 2
cert_coverFacet 4 812
cert_cover_5 4 0 1 2 4 7 268 812 2
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 820
cert_cover_5 6 0 1 3 4 7 276 820 2
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0832

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0833.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0833

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 595, 99, 301, 397, 217, 537, 481, 806, 354, 962, 572, 156, 724, 900, 35, 67, 515, 269, 25, 41, 137, 521, 81, 529, 97, 289, 193, 385, 98, 290, 546, 322, 578, 770, 28, 44, 140, 148, 532, 292, 548, 388, 644, 772, 152, 536, 552, 208, 592, 352, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_595, vertices_99, vertices_301, vertices_397, vertices_217, vertices_537, vertices_481, vertices_806, vertices_354, vertices_962, vertices_572, vertices_156, vertices_724, vertices_900] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_515, vertices_269, vertices_25, vertices_41, vertices_137, vertices_521, vertices_81, vertices_529, vertices_97, vertices_289, vertices_193, vertices_385, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_44, vertices_140, vertices_148, vertices_532, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_152, vertices_536, vertices_552, vertices_208, vertices_592, vertices_352, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_595), (false, vertices_99), (false, vertices_301), (false, vertices_397), (false, vertices_217), (false, vertices_537), (false, vertices_481), (true, vertices_290), (true, vertices_322), (true, vertices_770), (true, vertices_28), (true, vertices_148), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 14 else
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_99) then 0 else
  if p.val = (false, vertices_301) then 17 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_217) then 20 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_99), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
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
cert_row_4 0 1 2 3 4 8 572 28 3
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 5 6 7 8 962 322 2
cert_row_4 3 1 3 5 6 8 724 148 2
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 354
cert_cover_2 1 4 0 5 7 98 354 3
cert_coverFacet 2 962
cert_cover_5 2 2 0 5 6 7 322 962 2
cert_coverFacet 3 572
cert_cover_5 3 0 1 2 3 4 28 572 3
cert_coverFacet 4 156
cert_cover_2 4 2 1 3 6 28 156 3
cert_coverFacet 5 724
cert_cover_5 5 3 1 3 5 6 148 724 2
cert_coverFacet 6 900
cert_cover_2 6 6 1 7 8 388 900 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0833

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0834.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0834

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 789, 409, 681, 841, 118, 406, 422, 618, 594, 674, 364, 596, 836, 424, 137, 265, 521, 145, 273, 529, 641, 769, 22, 38, 390, 82, 146, 530, 98, 162, 546, 578, 642, 84, 276, 532, 100, 292, 324, 580, 772, 104, 168, 296, 552, 328, 584, 392, 592, 400, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_789, vertices_409, vertices_681, vertices_841, vertices_118, vertices_406, vertices_422, vertices_618, vertices_594, vertices_674, vertices_364, vertices_596, vertices_836, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_641, vertices_769, vertices_22, vertices_38, vertices_390, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_578, vertices_642, vertices_84, vertices_276, vertices_532, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_104, vertices_168, vertices_296, vertices_552, vertices_328, vertices_584, vertices_392, vertices_592, vertices_400, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_789), (false, vertices_409), (false, vertices_681), (false, vertices_841), (true, vertices_22), (true, vertices_38), (true, vertices_390), (true, vertices_82), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_578), (true, vertices_84), (true, vertices_100), (true, vertices_292), (true, vertices_324), (true, vertices_580), (true, vertices_104), (true, vertices_296), (true, vertices_592), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_841) then 24 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_390) then 18 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_4 1 0 1 3 4 5 118 22 3
cert_row_4 2 0 2 4 5 8 618 98 1
cert_row_4 3 1 2 4 5 7 364 100 1
cert_rows
cert_pivot_2 6 3 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 1 0 1 3 4 22 118 3
cert_coverFacet 1 406
cert_cover_5 1 0 0 1 3 6 22 406 3
cert_coverFacet 2 422
cert_cover_5 2 0 0 1 4 6 38 422 3
cert_coverFacet 3 618
cert_cover_5 3 2 0 2 4 5 98 618 1
cert_coverFacet 4 594
cert_cover_2 4 3 0 5 8 82 594 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 364
cert_cover_5 6 3 1 2 4 5 100 364 1
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 836
cert_cover_2 8 5 1 7 8 324 836 3
cert_coverFacet 9 424
cert_cover_2 9 4 2 6 7 168 424 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0834

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0835.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0835

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 229, 665, 433, 865, 705, 542, 46, 358, 838, 282, 426, 172, 716, 408, 145, 273, 529, 97, 161, 289, 193, 577, 641, 769, 14, 38, 326, 518, 26, 42, 266, 274, 530, 290, 770, 44, 140, 524, 100, 164, 196, 580, 152, 280, 536, 168, 392, 648, 400, 352, 416, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_229, vertices_665, vertices_433, vertices_865, vertices_705, vertices_542, vertices_46, vertices_358, vertices_838, vertices_282, vertices_426, vertices_172, vertices_716, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_193, vertices_577, vertices_641, vertices_769, vertices_14, vertices_38, vertices_326, vertices_518, vertices_26, vertices_42, vertices_266, vertices_274, vertices_530, vertices_290, vertices_770, vertices_44, vertices_140, vertices_524, vertices_100, vertices_164, vertices_196, vertices_580, vertices_152, vertices_280, vertices_536, vertices_168, vertices_392, vertices_648, vertices_400, vertices_352, vertices_416, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_229), (false, vertices_665), (false, vertices_433), (false, vertices_865), (false, vertices_705), (true, vertices_14), (true, vertices_38), (true, vertices_326), (true, vertices_518), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_290), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_580), (true, vertices_280), (true, vertices_168), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_326) then 17 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 705 14 38 518 26 42 266 290 44 140 524 580 280 168 392 787 326 229 665 433 865
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 14 3
cert_row_4 1 0 2 4 6 7 426 42 3
cert_row_2 2 0 1 5 7 326
cert_row_4 3 1 2 5 6 8 716 140 2
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 14 542 3
cert_coverFacet 1 46
cert_cover_2 1 1 0 2 4 14 46 3
cert_coverFacet 2 358
cert_cover_5 2 2 0 1 4 5 38 358 3
cert_coverFacet 3 838
cert_cover_5 3 2 0 1 5 8 326 838 3
cert_coverFacet 4 282
cert_cover_2 4 2 0 3 7 26 282 3
cert_coverFacet 5 426
cert_cover_5 5 1 0 2 4 6 42 426 3
cert_coverFacet 6 172
cert_cover_2 6 2 1 4 6 44 172 3
cert_coverFacet 7 716
cert_cover_5 7 3 1 2 5 6 140 716 2
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0835

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0836.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0836

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 589, 789, 453, 737, 542, 282, 682, 298, 786, 482, 124, 372, 312, 616, 69, 261, 517, 193, 577, 385, 641, 769, 26, 42, 266, 522, 274, 530, 162, 290, 386, 642, 770, 28, 76, 524, 116, 276, 532, 324, 56, 280, 104, 296, 552, 584, 304, 784, 224, 352, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_589, vertices_789, vertices_453, vertices_737, vertices_542, vertices_282, vertices_682, vertices_298, vertices_786, vertices_482, vertices_124, vertices_372, vertices_312, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_530, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_524, vertices_116, vertices_276, vertices_532, vertices_324, vertices_56, vertices_280, vertices_104, vertices_296, vertices_552, vertices_584, vertices_304, vertices_784, vertices_224, vertices_352, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_589), (false, vertices_789), (false, vertices_453), (false, vertices_737), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_28), (true, vertices_116), (true, vertices_56), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_304), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 18 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_116) then 23 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_352) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 23 => Sum.inr ⟨(true, vertices_116), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 6 7 482 162 2
cert_row_2 1 1 3 4 5 116
cert_row_4 2 0 1 2 3 8 542 26 1
cert_row_4 3 0 2 4 6 8 682 42 3
cert_rows
cert_pivot_2 7 5 1 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 2 0 1 2 3 26 542 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 682
cert_cover_5 2 3 0 2 4 6 42 682 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 482
cert_cover_5 5 0 0 4 5 6 162 482 2
cert_coverFacet 6 124
cert_cover_5 6 1 1 2 3 4 28 124 3
cert_coverFacet 7 372
cert_cover_5 7 1 1 3 4 7 116 372 3
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coverFacet 9 616
cert_cover_2 9 4 2 5 8 104 616 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0836

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0837.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0837

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 421, 837, 809, 689, 590, 214, 570, 346, 658, 468, 184, 408, 424, 840, 133, 261, 517, 161, 289, 545, 641, 769, 70, 134, 518, 26, 74, 522, 82, 146, 530, 642, 212, 324, 580, 388, 56, 152, 280, 168, 296, 552, 328, 584, 392, 776, 176, 560, 336, 400, 656, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_421, vertices_837, vertices_809, vertices_689, vertices_590, vertices_214, vertices_570, vertices_346, vertices_658, vertices_468, vertices_184, vertices_408, vertices_424, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_70, vertices_134, vertices_518, vertices_26, vertices_74, vertices_522, vertices_82, vertices_146, vertices_530, vertices_642, vertices_212, vertices_324, vertices_580, vertices_388, vertices_56, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_328, vertices_584, vertices_392, vertices_776, vertices_176, vertices_560, vertices_336, vertices_400, vertices_656, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_421), (false, vertices_837), (false, vertices_809), (false, vertices_689), (true, vertices_70), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_212), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_328), (true, vertices_584), (true, vertices_392), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 17 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_809) then 23 else
  if p.val = (false, vertices_689) then 25 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_212) then 21 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_2 0 1 3 5 6 212
cert_row_4 1 0 1 2 5 8 590 70 2
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 0 2 3 5 7 346 26 3
cert_rows
cert_pivot_2 6 1 4 0
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 70 590 2
cert_coverFacet 1 214
cert_cover_5 1 0 0 1 3 5 70 214 2
cert_coverFacet 2 570
cert_cover_5 2 2 0 2 3 4 26 570 3
cert_coverFacet 3 346
cert_cover_5 3 3 0 2 3 5 26 346 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 468
cert_cover_5 5 0 1 3 5 7 212 468 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coverFacet 9 840
cert_cover_2 9 5 2 7 8 328 840 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0837

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0838.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0838

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 557, 357, 709, 465, 801, 542, 154, 810, 394, 722, 124, 596, 376, 408, 37, 69, 517, 289, 545, 193, 321, 385, 641, 769, 26, 138, 266, 522, 146, 530, 386, 642, 770, 28, 44, 524, 84, 532, 100, 580, 120, 152, 280, 296, 552, 392, 208, 336, 592, 400, 352, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_557, vertices_357, vertices_709, vertices_465, vertices_801, vertices_542, vertices_154, vertices_810, vertices_394, vertices_722, vertices_124, vertices_596, vertices_376, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_524, vertices_84, vertices_532, vertices_100, vertices_580, vertices_120, vertices_152, vertices_280, vertices_296, vertices_552, vertices_392, vertices_208, vertices_336, vertices_592, vertices_400, vertices_352, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_557), (false, vertices_357), (false, vertices_709), (false, vertices_465), (false, vertices_801), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_84), (true, vertices_532), (true, vertices_120), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_392), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_120) then 22 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(true, vertices_120), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 26 1
cert_row_4 1 0 2 4 7 8 810 266 2
cert_row_2 2 2 3 4 5 120
cert_row_4 3 0 3 5 6 8 722 146 2
cert_rows
cert_pivot_2 1 7 2 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 26 542 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 810
cert_cover_5 2 1 0 2 4 7 266 810 2
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 722
cert_cover_5 4 3 0 3 5 6 146 722 2
cert_coverFacet 5 124
cert_cover_5 5 2 1 2 3 4 28 124 3
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 376
cert_cover_5 7 2 2 3 4 7 120 376 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0838

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0839.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0839

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 789, 905, 433, 737, 30, 334, 118, 538, 714, 610, 540, 780, 372, 488, 49, 273, 529, 161, 545, 385, 641, 769, 14, 22, 70, 26, 74, 522, 50, 530, 98, 546, 578, 28, 268, 524, 116, 276, 532, 324, 772, 536, 200, 328, 392, 648, 776, 304, 224, 352, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_789, vertices_905, vertices_433, vertices_737, vertices_30, vertices_334, vertices_118, vertices_538, vertices_714, vertices_610, vertices_540, vertices_780, vertices_372, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_273, vertices_529, vertices_161, vertices_545, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_70, vertices_26, vertices_74, vertices_522, vertices_50, vertices_530, vertices_98, vertices_546, vertices_578, vertices_28, vertices_268, vertices_524, vertices_116, vertices_276, vertices_532, vertices_324, vertices_772, vertices_536, vertices_200, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_224, vertices_352, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_789), (false, vertices_905), (false, vertices_433), (false, vertices_737), (true, vertices_14), (true, vertices_22), (true, vertices_70), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_98), (true, vertices_578), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_116), (true, vertices_324), (true, vertices_536), (true, vertices_200), (true, vertices_328), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 17 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_905) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_116) then 20 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_328) then 14 else
  if p.val = (true, vertices_352) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_116), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 4 5 116
cert_row_4 1 0 1 2 5 7 334 14 3
cert_row_4 2 0 2 5 6 8 714 74 3
cert_row_4 3 2 4 5 6 7 488 200 1
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 334
cert_cover_5 1 1 0 1 2 5 14 334 3
cert_coverFacet 2 118
cert_cover_5 2 0 0 1 3 4 22 118 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 714
cert_cover_5 4 2 0 2 5 6 74 714 3
cert_coverFacet 5 610
cert_cover_2 5 4 0 5 8 98 610 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 372
cert_cover_5 8 0 1 3 4 7 116 372 3
cert_coverFacet 9 488
cert_cover_5 9 3 2 4 5 6 200 488 1
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0839

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0840.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0840

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 589, 805, 453, 721, 558, 314, 154, 650, 466, 802, 124, 372, 600, 664, 69, 261, 517, 193, 577, 385, 641, 769, 26, 42, 138, 522, 146, 274, 290, 546, 386, 642, 770, 44, 76, 524, 116, 292, 548, 324, 56, 88, 152, 536, 584, 648, 304, 208, 336, 592, 656, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_589, vertices_805, vertices_453, vertices_721, vertices_558, vertices_314, vertices_154, vertices_650, vertices_466, vertices_802, vertices_124, vertices_372, vertices_600, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_138, vertices_522, vertices_146, vertices_274, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_524, vertices_116, vertices_292, vertices_548, vertices_324, vertices_56, vertices_88, vertices_152, vertices_536, vertices_584, vertices_648, vertices_304, vertices_208, vertices_336, vertices_592, vertices_656, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_589), (false, vertices_805), (false, vertices_453), (false, vertices_721), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_290), (true, vertices_546), (true, vertices_44), (true, vertices_116), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_648), (true, vertices_304), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 18 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_116) then 23 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_336) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 23 => Sum.inr ⟨(true, vertices_116), by decide +kernel⟩
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
cert_row_4 0 0 1 2 4 8 558 42 1
cert_row_2 1 1 3 4 5 116
cert_row_4 2 0 2 3 4 7 314 26 3
cert_row_4 3 0 3 5 6 7 466 146 2
cert_rows
cert_pivot_2 8 1 2 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 42 558 1
cert_coverFacet 1 314
cert_cover_5 1 2 0 2 3 4 26 314 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 466
cert_cover_5 4 3 0 3 5 6 146 466 2
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 124
cert_cover_5 6 1 1 2 3 4 44 124 2
cert_coverFacet 7 372
cert_cover_5 7 1 1 3 4 7 116 372 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coverFacet 9 664
cert_cover_2 9 3 2 6 8 152 664 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0840

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0841.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0841

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 653, 617, 425, 369, 897, 542, 342, 390, 646, 626, 898, 188, 436, 568, 41, 137, 521, 97, 289, 321, 577, 385, 641, 769, 22, 134, 262, 518, 82, 530, 322, 578, 386, 642, 770, 28, 140, 524, 180, 276, 388, 644, 56, 536, 168, 552, 112, 304, 560, 336, 608, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_653, vertices_617, vertices_425, vertices_369, vertices_897, vertices_542, vertices_342, vertices_390, vertices_646, vertices_626, vertices_898, vertices_188, vertices_436, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_521, vertices_97, vertices_289, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_22, vertices_134, vertices_262, vertices_518, vertices_82, vertices_530, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_140, vertices_524, vertices_180, vertices_276, vertices_388, vertices_644, vertices_56, vertices_536, vertices_168, vertices_552, vertices_112, vertices_304, vertices_560, vertices_336, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_653), (false, vertices_617), (false, vertices_425), (false, vertices_369), (false, vertices_897), (true, vertices_22), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_82), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_28), (true, vertices_180), (true, vertices_276), (true, vertices_388), (true, vertices_56), (true, vertices_536), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_180) then 19 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_560) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 897 2 22 1 134 3 262 518 82 530 386 642 28 276 388 56 536 560 835 653 180 617 425 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 4 6 180
cert_row_4 1 0 1 2 3 8 542 22 2
cert_row_4 2 0 1 3 5 7 342 22 3
cert_row_4 3 0 3 4 5 8 626 82 2
cert_rows
cert_pivot_2 6 2 1 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 1 0 1 2 3 22 542 2
cert_coverFacet 1 342
cert_cover_5 1 2 0 1 3 5 22 342 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 646
cert_cover_2 3 1 0 6 8 134 646 3
cert_coverFacet 4 626
cert_cover_5 4 3 0 3 4 5 82 626 2
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 188
cert_cover_5 6 0 1 2 3 4 28 188 3
cert_coverFacet 7 436
cert_cover_5 7 0 1 3 4 7 180 436 3
cert_coverFacet 8 568
cert_cover_2 8 3 2 4 8 56 568 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0841

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0842.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0842

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 339, 803, 557, 229, 481, 282, 538, 778, 722, 668, 428, 708, 472, 808, 67, 259, 515, 37, 69, 517, 225, 289, 545, 321, 26, 266, 522, 82, 274, 530, 578, 770, 44, 140, 524, 164, 196, 580, 644, 152, 280, 536, 296, 552, 392, 776, 208, 336, 656, 416, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_339, vertices_803, vertices_557, vertices_229, vertices_481, vertices_282, vertices_538, vertices_778, vertices_722, vertices_668, vertices_428, vertices_708, vertices_472, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_37, vertices_69, vertices_517, vertices_225, vertices_289, vertices_545, vertices_321, vertices_26, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_578, vertices_770, vertices_44, vertices_140, vertices_524, vertices_164, vertices_196, vertices_580, vertices_644, vertices_152, vertices_280, vertices_536, vertices_296, vertices_552, vertices_392, vertices_776, vertices_208, vertices_336, vertices_656, vertices_416, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_339), (false, vertices_803), (false, vertices_557), (false, vertices_229), (false, vertices_481), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_530), (true, vertices_140), (true, vertices_644), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_296), (true, vertices_392), (true, vertices_776), (true, vertices_208), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 21 22 23 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 16 else
  if p.val = (false, vertices_339) then 17 else
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_557) then 20 else
  if p.val = (false, vertices_229) then 24 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 8 722 82 3
cert_row_4 1 1 2 3 6 8 668 140 2
cert_row_4 2 1 2 4 6 7 428 44 3
cert_row_4 3 2 3 5 6 7 472 152 2
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 282
cert_cover_2 0 2 0 3 7 26 282 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 722
cert_cover_5 3 0 0 3 5 6 82 722 3
cert_coverFacet 4 668
cert_cover_5 4 1 1 2 3 6 140 668 2
cert_coverFacet 5 428
cert_cover_5 5 2 1 2 4 6 44 428 3
cert_coverFacet 6 708
cert_cover_2 6 5 1 6 8 196 708 3
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 152 472 2
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0842

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3393 : Certifies 3393 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0812.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3394 : Certifies 3394 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0813.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3395 : Certifies 3395 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0814.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3396 : Certifies 3396 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0815.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3397 : Certifies 3397 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0816.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3398 : Certifies 3398 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0817.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3399 : Certifies 3399 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0818.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3400 : Certifies 3400 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0819.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3401 : Certifies 3401 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0820.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3402 : Certifies 3402 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0821.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3403 : Certifies 3403 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0822.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3404 : Certifies 3404 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0823.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3405 : Certifies 3405 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0824.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3406 : Certifies 3406 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0825.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3407 : Certifies 3407 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0826.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3408 : Certifies 3408 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0828.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3409 : Certifies 3409 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0829.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3410 : Certifies 3410 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0830.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3411 : Certifies 3411 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0831.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3412 : Certifies 3412 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0832.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3413 : Certifies 3413 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0833.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3414 : Certifies 3414 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0834.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3415 : Certifies 3415 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0835.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3416 : Certifies 3416 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0836.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3417 : Certifies 3417 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0837.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3418 : Certifies 3418 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0838.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3419 : Certifies 3419 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0839.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3420 : Certifies 3420 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0840.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3421 : Certifies 3421 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0841.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3422 : Certifies 3422 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0842.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B112 (j : Fin 30) :
    Certifies (3393 + j.val) := by
  fin_cases j
  · exact projection_3393
  · exact projection_3394
  · exact projection_3395
  · exact projection_3396
  · exact projection_3397
  · exact projection_3398
  · exact projection_3399
  · exact projection_3400
  · exact projection_3401
  · exact projection_3402
  · exact projection_3403
  · exact projection_3404
  · exact projection_3405
  · exact projection_3406
  · exact projection_3407
  · exact projection_3408
  · exact projection_3409
  · exact projection_3410
  · exact projection_3411
  · exact projection_3412
  · exact projection_3413
  · exact projection_3414
  · exact projection_3415
  · exact projection_3416
  · exact projection_3417
  · exact projection_3418
  · exact projection_3419
  · exact projection_3420
  · exact projection_3421
  · exact projection_3422

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
