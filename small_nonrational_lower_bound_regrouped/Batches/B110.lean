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
/- Source: ProjectionCertificates/R_m15e10q1_0748.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0748

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 675, 579, 387, 405, 617, 241, 902, 842, 124, 348, 812, 564, 660, 688, 67, 131, 259, 515, 81, 145, 273, 97, 161, 545, 577, 385, 322, 578, 386, 642, 770, 92, 44, 268, 52, 148, 276, 532, 548, 388, 644, 772, 104, 552, 328, 584, 776, 112, 176, 560, 336, 656, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_675, vertices_579, vertices_387, vertices_405, vertices_617, vertices_241, vertices_902, vertices_842, vertices_124, vertices_348, vertices_812, vertices_564, vertices_660, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_81, vertices_145, vertices_273, vertices_97, vertices_161, vertices_545, vertices_577, vertices_385, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_92, vertices_44, vertices_268, vertices_52, vertices_148, vertices_276, vertices_532, vertices_548, vertices_388, vertices_644, vertices_772, vertices_104, vertices_552, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_560, vertices_336, vertices_656, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_675), (false, vertices_579), (false, vertices_387), (false, vertices_405), (false, vertices_617), (false, vertices_241), (true, vertices_770), (true, vertices_92), (true, vertices_44), (true, vertices_268), (true, vertices_52), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_328), (true, vertices_776), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 15 else
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_579) then 0 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_92) then 19 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_656) then 13 else
  0
cert_priority
cert_nodeAtPriority_44 579 387 770 44 268 52 532 548 644 772 328 776 560 656 339 675 405 92 617 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 5 92
cert_row_4 1 0 1 6 7 8 902 386 1
cert_row_4 2 0 2 5 7 8 842 322 1
cert_row_4 3 1 2 4 7 8 812 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 842
cert_cover_5 1 2 0 2 5 7 322 842 1
cert_coverFacet 2 124
cert_cover_5 2 0 1 2 3 4 92 124 3
cert_coverFacet 3 348
cert_cover_5 3 0 1 2 3 7 92 348 3
cert_coverFacet 4 812
cert_cover_5 4 3 1 2 4 7 44 812 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0748

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0749.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0749

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 117, 181, 709, 425, 865, 662, 58, 538, 170, 842, 394, 178, 604, 376, 53, 69, 133, 97, 161, 289, 577, 385, 641, 769, 26, 42, 138, 266, 522, 50, 146, 530, 162, 386, 642, 770, 84, 148, 532, 580, 644, 56, 88, 536, 168, 296, 328, 584, 392, 112, 176, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_117, vertices_181, vertices_709, vertices_425, vertices_865, vertices_662, vertices_58, vertices_538, vertices_170, vertices_842, vertices_394, vertices_178, vertices_604, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_53, vertices_69, vertices_133, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_386, vertices_642, vertices_770, vertices_84, vertices_148, vertices_532, vertices_580, vertices_644, vertices_56, vertices_88, vertices_536, vertices_168, vertices_296, vertices_328, vertices_584, vertices_392, vertices_112, vertices_176, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_117), (false, vertices_181), (false, vertices_709), (false, vertices_425), (false, vertices_865), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_532), (true, vertices_56), (true, vertices_88), (true, vertices_536), (true, vertices_328), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_117) then 18 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_162) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_584) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_4 1 0 2 5 7 8 842 266 2
cert_row_4 2 1 2 3 5 8 604 84 1
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 170
cert_cover_2 3 2 0 4 6 42 170 3
cert_coverFacet 4 842
cert_cover_5 4 1 0 2 5 7 266 842 2
cert_coverFacet 5 394
cert_cover_2 5 2 0 6 7 138 394 3
cert_coverFacet 6 178
cert_cover_2 6 3 0 4 6 50 178 3
cert_coverFacet 7 604
cert_cover_5 7 2 1 2 3 5 84 604 1
cert_coverFacet 8 376
cert_cover_5 8 3 2 3 4 5 56 376 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0749

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0750.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0750

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 93, 157, 677, 837, 625, 902, 154, 282, 394, 306, 866, 674, 460, 376, 29, 69, 133, 517, 49, 81, 145, 161, 545, 577, 26, 138, 266, 50, 146, 274, 162, 290, 546, 386, 642, 770, 76, 140, 324, 388, 644, 772, 88, 152, 280, 328, 392, 112, 304, 352, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_93, vertices_157, vertices_677, vertices_837, vertices_625, vertices_902, vertices_154, vertices_282, vertices_394, vertices_306, vertices_866, vertices_674, vertices_460, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_69, vertices_133, vertices_517, vertices_49, vertices_81, vertices_145, vertices_161, vertices_545, vertices_577, vertices_26, vertices_138, vertices_266, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_324, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_328, vertices_392, vertices_112, vertices_304, vertices_352, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_93), (false, vertices_157), (false, vertices_677), (false, vertices_837), (false, vertices_625), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_274), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_388), (true, vertices_280), (true, vertices_328), (true, vertices_392), (true, vertices_304), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 16 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_157) then 19 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 26 2 138 1 266 274 290 546 386 642 770 388 280 328 392 304 352 179 93 157 677 837 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 5 7 376 88 2
cert_row_4 1 0 4 5 7 8 866 290 2
cert_row_4 2 0 1 6 7 8 902 386 1
cert_row_4 3 1 2 5 6 7 460 76 3
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 2 0 1 6 7 386 902 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 866
cert_cover_5 5 1 0 4 5 7 290 866 2
cert_coverFacet 6 674
cert_cover_2 6 4 0 6 8 162 674 3
cert_coverFacet 7 460
cert_cover_5 7 3 1 2 5 6 76 460 3
cert_coverFacet 8 376
cert_cover_5 8 0 2 3 4 5 88 376 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0750

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0751.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0751

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 109, 333, 677, 569, 905, 214, 326, 794, 690, 338, 898, 228, 376, 240, 77, 37, 133, 261, 41, 265, 521, 545, 385, 641, 70, 134, 262, 82, 146, 274, 530, 322, 386, 642, 770, 100, 164, 196, 324, 56, 280, 536, 104, 328, 776, 112, 176, 560, 208, 336, 224, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_109, vertices_333, vertices_677, vertices_569, vertices_905, vertices_214, vertices_326, vertices_794, vertices_690, vertices_338, vertices_898, vertices_228, vertices_376, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_77, vertices_37, vertices_133, vertices_261, vertices_41, vertices_265, vertices_521, vertices_545, vertices_385, vertices_641, vertices_70, vertices_134, vertices_262, vertices_82, vertices_146, vertices_274, vertices_530, vertices_322, vertices_386, vertices_642, vertices_770, vertices_100, vertices_164, vertices_196, vertices_324, vertices_56, vertices_280, vertices_536, vertices_104, vertices_328, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_336, vertices_224, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_109), (false, vertices_333), (false, vertices_677), (false, vertices_569), (false, vertices_905), (true, vertices_70), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_322), (true, vertices_642), (true, vertices_770), (true, vertices_196), (true, vertices_280), (true, vertices_112), (true, vertices_176), (true, vertices_208), (true, vertices_336), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 16 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_569) then 22 else
  if p.val = (false, vertices_905) then 23 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 70 1 82 2 146 274 530 322 642 770 196 280 112 176 208 336 224 391 109 333 677 569 905
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 70 2
cert_row_4 1 0 3 4 6 8 690 146 2
cert_row_4 2 0 2 3 7 8 794 274 1
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 70 214 2
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 794
cert_cover_5 2 2 0 2 3 7 274 794 1
cert_coverFacet 3 690
cert_cover_5 3 1 0 3 4 6 146 690 2
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 376
cert_cover_5 7 3 2 3 4 5 56 376 3
cert_coverFacet 8 240
cert_cover_2 8 4 3 5 6 112 240 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0751

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0752.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0752

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 779, 579, 61, 285, 229, 617, 914, 738, 450, 692, 212, 340, 824, 464, 67, 259, 515, 29, 37, 69, 261, 41, 265, 521, 97, 577, 194, 322, 578, 386, 642, 770, 52, 84, 148, 276, 164, 196, 324, 56, 280, 552, 776, 560, 208, 336, 400, 656, 784, 224, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_779, vertices_579, vertices_61, vertices_285, vertices_229, vertices_617, vertices_914, vertices_738, vertices_450, vertices_692, vertices_212, vertices_340, vertices_824, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_29, vertices_37, vertices_69, vertices_261, vertices_41, vertices_265, vertices_521, vertices_97, vertices_577, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_148, vertices_276, vertices_164, vertices_196, vertices_324, vertices_56, vertices_280, vertices_552, vertices_776, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_779), (false, vertices_579), (false, vertices_61), (false, vertices_285), (false, vertices_229), (false, vertices_617), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_84), (true, vertices_148), (true, vertices_560), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 15 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_579) then 0 else
  if p.val = (false, vertices_61) then 18 else
  if p.val = (false, vertices_285) then 19 else
  if p.val = (false, vertices_229) then 20 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_579), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 6 8 738 194 1
cert_row_4 1 0 3 6 7 8 914 386 1
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 914
cert_cover_5 0 1 0 3 6 7 386 914 1
cert_coverFacet 1 738
cert_cover_5 1 0 0 4 5 6 194 738 1
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 692
cert_cover_5 3 2 1 3 4 6 52 692 3
cert_coverFacet 4 212
cert_cover_2 4 3 1 5 6 84 212 3
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 824
cert_cover_5 6 3 2 3 4 7 56 824 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0752

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0753.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0753

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 555, 771, 173, 205, 341, 841, 434, 850, 658, 674, 724, 404, 420, 744, 35, 259, 515, 141, 37, 69, 261, 41, 73, 521, 321, 769, 146, 274, 530, 162, 290, 546, 642, 770, 84, 148, 276, 164, 292, 196, 388, 168, 552, 200, 584, 336, 592, 400, 656, 416, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_555, vertices_771, vertices_173, vertices_205, vertices_341, vertices_841, vertices_434, vertices_850, vertices_658, vertices_674, vertices_724, vertices_404, vertices_420, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_141, vertices_37, vertices_69, vertices_261, vertices_41, vertices_73, vertices_521, vertices_321, vertices_769, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_84, vertices_148, vertices_276, vertices_164, vertices_292, vertices_196, vertices_388, vertices_168, vertices_552, vertices_200, vertices_584, vertices_336, vertices_592, vertices_400, vertices_656, vertices_416, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_555), (false, vertices_771), (false, vertices_173), (false, vertices_205), (false, vertices_341), (false, vertices_841), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_642), (true, vertices_148), (true, vertices_388), (true, vertices_592), (true, vertices_400), (true, vertices_656), (true, vertices_416), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 15 else
  if p.val = (false, vertices_555) then 16 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_173) then 18 else
  if p.val = (false, vertices_205) then 19 else
  if p.val = (false, vertices_341) then 20 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 5 6 8 724 84 3
cert_row_4 1 2 4 5 6 8 744 168 2
cert_row_4 2 0 3 4 6 7 434 146 2
cert_row_4 3 0 3 5 7 8 850 274 2
cert_rows
cert_pivot_2 1 2 4 0
cert_heightProof 4
cert_coverFacet 0 434
cert_cover_5 0 2 0 3 4 6 146 434 2
cert_coverFacet 1 850
cert_cover_5 1 3 0 3 5 7 274 850 2
cert_coverFacet 2 658
cert_cover_2 2 3 0 6 8 146 658 3
cert_coverFacet 3 674
cert_cover_2 3 4 0 6 8 162 674 3
cert_coverFacet 4 724
cert_cover_5 4 0 1 3 5 6 84 724 3
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 420
cert_cover_2 6 4 1 6 7 164 420 3
cert_coverFacet 7 744
cert_cover_5 7 1 2 4 5 6 168 744 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0753

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0754.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0754

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 109, 301, 409, 713, 241, 806, 394, 650, 778, 562, 722, 402, 844, 628, 45, 73, 137, 265, 49, 145, 273, 97, 289, 193, 138, 266, 522, 50, 146, 274, 530, 290, 546, 386, 642, 770, 76, 268, 100, 292, 548, 580, 772, 584, 392, 648, 776, 112, 560, 208, 592, 400, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_109, vertices_301, vertices_409, vertices_713, vertices_241, vertices_806, vertices_394, vertices_650, vertices_778, vertices_562, vertices_722, vertices_402, vertices_844, vertices_628] (by decide +kernel)
  polygons := literalFinset [vertices_45, vertices_73, vertices_137, vertices_265, vertices_49, vertices_145, vertices_273, vertices_97, vertices_289, vertices_193, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_268, vertices_100, vertices_292, vertices_548, vertices_580, vertices_772, vertices_584, vertices_392, vertices_648, vertices_776, vertices_112, vertices_560, vertices_208, vertices_592, vertices_400, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_109), (false, vertices_301), (false, vertices_409), (false, vertices_713), (false, vertices_241), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_548), (true, vertices_580), (true, vertices_772), (true, vertices_776), (true, vertices_560), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 16 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_301) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 138 1 266 2 522 146 530 546 386 642 770 548 580 772 776 560 592 307 109 301 409 713 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 8 722 146 2
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 1 2 5 7 8 844 76 3
cert_row_4 3 1 3 4 5 8 628 100 1
cert_rows
cert_pivot_2 6 0 2 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 722
cert_cover_5 5 0 0 3 5 6 146 722 2
cert_coverFacet 6 402
cert_cover_2 6 3 0 6 7 146 402 3
cert_coverFacet 7 844
cert_cover_5 7 2 1 2 5 7 76 844 3
cert_coverFacet 8 628
cert_cover_5 8 3 1 3 4 5 100 628 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0754

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0755.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0755

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 173, 557, 793, 457, 433, 614, 842, 114, 466, 786, 652, 244, 708, 712, 45, 137, 265, 521, 49, 273, 529, 161, 545, 385, 50, 82, 274, 530, 98, 546, 322, 578, 770, 140, 524, 100, 164, 548, 196, 580, 644, 200, 328, 584, 648, 776, 112, 176, 208, 400, 784, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_173, vertices_557, vertices_793, vertices_457, vertices_433, vertices_614, vertices_842, vertices_114, vertices_466, vertices_786, vertices_652, vertices_244, vertices_708, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_45, vertices_137, vertices_265, vertices_521, vertices_49, vertices_273, vertices_529, vertices_161, vertices_545, vertices_385, vertices_50, vertices_82, vertices_274, vertices_530, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_140, vertices_524, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_200, vertices_328, vertices_584, vertices_648, vertices_776, vertices_112, vertices_176, vertices_208, vertices_400, vertices_784, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_173), (false, vertices_557), (false, vertices_793), (false, vertices_457), (false, vertices_433), (true, vertices_82), (true, vertices_274), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_100), (true, vertices_196), (true, vertices_580), (true, vertices_644), (true, vertices_584), (true, vertices_648), (true, vertices_112), (true, vertices_208), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_173) then 18 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 82 1 274 2 98 322 578 770 100 196 580 644 584 648 112 208 704 563 173 557 793 457 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 322 1
cert_row_4 1 0 1 4 5 8 614 98 1
cert_row_4 2 0 3 5 6 7 466 82 3
cert_row_4 3 1 3 4 5 6 244 100 1
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 1 0 1 4 5 98 614 1
cert_coverFacet 1 842
cert_cover_5 1 0 0 2 5 7 322 842 1
cert_coverFacet 2 114
cert_cover_2 2 3 0 4 5 50 114 3
cert_coverFacet 3 466
cert_cover_5 3 2 0 3 5 6 82 466 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 244
cert_cover_5 6 3 1 3 4 5 100 244 1
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coverFacet 8 712
cert_cover_2 8 5 2 6 8 200 712 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0755

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0756.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0756

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 117, 341, 805, 409, 689, 838, 122, 282, 714, 394, 338, 620, 184, 680, 85, 37, 261, 49, 145, 273, 545, 385, 641, 769, 26, 74, 138, 266, 82, 274, 322, 578, 386, 642, 770, 100, 548, 324, 580, 772, 56, 152, 280, 104, 168, 552, 584, 392, 648, 112, 176, 336, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_117, vertices_341, vertices_805, vertices_409, vertices_689, vertices_838, vertices_122, vertices_282, vertices_714, vertices_394, vertices_338, vertices_620, vertices_184, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_85, vertices_37, vertices_261, vertices_49, vertices_145, vertices_273, vertices_545, vertices_385, vertices_641, vertices_769, vertices_26, vertices_74, vertices_138, vertices_266, vertices_82, vertices_274, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_104, vertices_168, vertices_552, vertices_584, vertices_392, vertices_648, vertices_112, vertices_176, vertices_336, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_117), (false, vertices_341), (false, vertices_805), (false, vertices_409), (false, vertices_689), (true, vertices_26), (true, vertices_74), (true, vertices_138), (true, vertices_266), (true, vertices_82), (true, vertices_274), (true, vertices_322), (true, vertices_578), (true, vertices_580), (true, vertices_56), (true, vertices_104), (true, vertices_168), (true, vertices_552), (true, vertices_584), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_117) then 18 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_648) then 14 else
  0
cert_priority
cert_nodeAtPriority_68 0 26 1 74 138 266 82 274 322 578 580 56 104 168 552 584 648 899 117 341 805 409 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 7 8 838 322 1
cert_row_4 1 0 2 3 4 5 122 26 3
cert_row_4 2 0 2 5 6 8 714 74 3
cert_row_4 3 1 2 4 5 8 620 100 1
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 0 0 1 5 7 322 838 1
cert_coverFacet 1 122
cert_cover_5 1 1 0 2 3 4 26 122 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 714
cert_cover_5 3 2 0 2 5 6 74 714 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 100 620 1
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 680
cert_cover_2 8 4 2 6 8 168 680 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0756

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0757.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0757

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 611, 291, 387, 421, 601, 681, 806, 850, 450, 220, 796, 652, 468, 676, 35, 67, 131, 259, 73, 137, 521, 161, 289, 545, 577, 385, 290, 546, 194, 322, 578, 386, 770, 28, 140, 524, 212, 276, 164, 292, 548, 388, 644, 772, 88, 536, 200, 648, 336, 592, 784, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_611, vertices_291, vertices_387, vertices_421, vertices_601, vertices_681, vertices_806, vertices_850, vertices_450, vertices_220, vertices_796, vertices_652, vertices_468, vertices_676] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_131, vertices_259, vertices_73, vertices_137, vertices_521, vertices_161, vertices_289, vertices_545, vertices_577, vertices_385, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_28, vertices_140, vertices_524, vertices_212, vertices_276, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_88, vertices_536, vertices_200, vertices_648, vertices_336, vertices_592, vertices_784, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_611), (false, vertices_291), (false, vertices_387), (false, vertices_421), (false, vertices_601), (false, vertices_681), (true, vertices_322), (true, vertices_770), (true, vertices_28), (true, vertices_140), (true, vertices_524), (true, vertices_212), (true, vertices_276), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_336), (true, vertices_784), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_421) then 18 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_212) then 19 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 5 6 212
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 3 5 7 8 850 322 1
cert_row_4 3 1 2 3 7 8 796 28 3
cert_rows
cert_pivot_2 6 4 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 850
cert_cover_5 1 2 0 3 5 7 322 850 1
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 220
cert_cover_5 3 0 1 2 3 5 28 220 3
cert_coverFacet 4 796
cert_cover_5 4 3 1 2 3 7 28 796 3
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 468
cert_cover_5 6 0 1 3 5 7 212 468 3
cert_coverFacet 7 676
cert_cover_2 7 4 1 6 8 164 676 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0757

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0758.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0758

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 781, 601, 153, 425, 465, 302, 614, 774, 242, 418, 450, 188, 540, 628, 25, 137, 265, 521, 81, 145, 321, 577, 385, 769, 38, 262, 518, 98, 162, 290, 194, 322, 578, 386, 770, 28, 44, 268, 524, 52, 532, 612, 772, 152, 536, 168, 296, 112, 176, 208, 592, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_781, vertices_601, vertices_153, vertices_425, vertices_465, vertices_302, vertices_614, vertices_774, vertices_242, vertices_418, vertices_450, vertices_188, vertices_540, vertices_628] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_321, vertices_577, vertices_385, vertices_769, vertices_38, vertices_262, vertices_518, vertices_98, vertices_162, vertices_290, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_28, vertices_44, vertices_268, vertices_524, vertices_52, vertices_532, vertices_612, vertices_772, vertices_152, vertices_536, vertices_168, vertices_296, vertices_112, vertices_176, vertices_208, vertices_592, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_781), (false, vertices_601), (false, vertices_153), (false, vertices_425), (false, vertices_465), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_194), (true, vertices_386), (true, vertices_28), (true, vertices_44), (true, vertices_52), (true, vertices_532), (true, vertices_612), (true, vertices_112), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_153) then 0 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_44) then 10 else
  if p.val = (true, vertices_52) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_612) then 19 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_176) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 153 2 38 1 262 3 518 98 162 290 194 386 28 44 52 532 112 176 835 781 612 601 425 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 8 612
cert_row_4 1 0 1 2 4 7 302 38 2
cert_row_4 2 0 3 4 5 6 242 98 1
cert_row_4 3 1 2 3 4 6 188 28 3
cert_rows
cert_pivot_2 8 7 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 1 0 1 2 4 38 302 2
cert_coverFacet 1 614
cert_cover_5 1 0 0 1 4 5 38 614 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 98 242 1
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 188
cert_cover_5 6 3 1 2 3 4 28 188 3
cert_coverFacet 7 540
cert_cover_2 7 2 1 3 8 28 540 3
cert_coverFacet 8 628
cert_cover_5 8 0 1 3 4 5 52 628 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0758

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0759.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0759

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 677, 57, 601, 233, 817, 206, 334, 806, 646, 850, 396, 420, 440, 344, 25, 41, 73, 49, 529, 161, 545, 193, 577, 641, 78, 134, 262, 518, 194, 322, 578, 642, 770, 140, 268, 164, 292, 548, 388, 644, 56, 88, 280, 168, 200, 328, 392, 304, 336, 592, 784, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_677, vertices_57, vertices_601, vertices_233, vertices_817, vertices_206, vertices_334, vertices_806, vertices_646, vertices_850, vertices_396, vertices_420, vertices_440, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_73, vertices_49, vertices_529, vertices_161, vertices_545, vertices_193, vertices_577, vertices_641, vertices_78, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_140, vertices_268, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_56, vertices_88, vertices_280, vertices_168, vertices_200, vertices_328, vertices_392, vertices_304, vertices_336, vertices_592, vertices_784, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_677), (false, vertices_57), (false, vertices_601), (false, vertices_233), (false, vertices_817), (true, vertices_78), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_322), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_292), (true, vertices_388), (true, vertices_280), (true, vertices_328), (true, vertices_392), (true, vertices_336), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 57 134 262 518 322 770 140 268 292 388 280 328 392 336 416 707 78 677 601 233 817
cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 6 7 440 56 3
cert_row_2 1 0 1 2 5 78
cert_row_4 2 0 1 4 7 8 806 262 2
cert_row_4 3 0 3 5 7 8 850 322 1
cert_rows
cert_pivot_2 6 2 1 0
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 6 78 206 3
cert_coverFacet 1 334
cert_cover_5 1 1 0 1 2 7 78 334 3
cert_coverFacet 2 806
cert_cover_5 2 2 0 1 4 7 262 806 2
cert_coverFacet 3 646
cert_cover_2 3 1 0 6 8 134 646 3
cert_coverFacet 4 850
cert_cover_5 4 3 0 3 5 7 322 850 1
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 420
cert_cover_2 6 4 1 6 7 164 420 3
cert_coverFacet 7 440
cert_cover_5 7 0 2 3 4 6 56 440 3
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0759

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0760.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0760

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 805, 105, 425, 713, 625, 158, 270, 566, 774, 394, 722, 220, 364, 116, 41, 73, 137, 97, 289, 545, 577, 385, 641, 769, 14, 22, 262, 518, 138, 266, 146, 530, 386, 642, 770, 156, 76, 268, 52, 84, 100, 292, 548, 772, 104, 296, 200, 392, 112, 560, 208, 592, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_805, vertices_105, vertices_425, vertices_713, vertices_625, vertices_158, vertices_270, vertices_566, vertices_774, vertices_394, vertices_722, vertices_220, vertices_364, vertices_116] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_137, vertices_97, vertices_289, vertices_545, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_518, vertices_138, vertices_266, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_156, vertices_76, vertices_268, vertices_52, vertices_84, vertices_100, vertices_292, vertices_548, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_560, vertices_208, vertices_592, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_805), (false, vertices_105), (false, vertices_425), (false, vertices_713), (false, vertices_625), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_530), (true, vertices_156), (true, vertices_76), (true, vertices_268), (true, vertices_52), (true, vertices_84), (true, vertices_100), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_105) then 0 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_146) then 7 else
  if p.val = (true, vertices_530) then 8 else
  if p.val = (true, vertices_156) then 19 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_52) then 11 else
  if p.val = (true, vertices_84) then 12 else
  if p.val = (true, vertices_100) then 13 else
  if p.val = (true, vertices_208) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 105 2 14 1 22 3 262 518 138 266 146 530 76 268 52 84 100 208 899 805 156 425 713 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 5 7 364 76 2
cert_row_2 1 1 2 3 6 156
cert_row_4 2 0 1 3 4 8 566 22 3
cert_row_4 3 0 3 5 6 8 722 146 2
cert_rows
cert_pivot_2 7 2 1 0
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 14 158 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 566
cert_cover_5 2 2 0 1 3 4 22 566 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 722
cert_cover_5 5 3 0 3 5 6 146 722 2
cert_coverFacet 6 220
cert_cover_5 6 1 1 2 3 5 156 220 3
cert_coverFacet 7 364
cert_cover_5 7 0 1 2 4 5 76 364 2
cert_coverFacet 8 116
cert_cover_2 8 3 1 4 5 52 116 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0760

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0761.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0761

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 557, 53, 789, 369, 737, 782, 218, 346, 682, 706, 156, 284, 172, 244, 21, 37, 517, 49, 273, 97, 545, 321, 577, 769, 90, 138, 266, 522, 194, 322, 578, 642, 770, 28, 44, 140, 268, 524, 52, 148, 276, 164, 772, 152, 280, 168, 552, 112, 208, 336, 224, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_557, vertices_53, vertices_789, vertices_369, vertices_737, vertices_782, vertices_218, vertices_346, vertices_682, vertices_706, vertices_156, vertices_284, vertices_172, vertices_244] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_517, vertices_49, vertices_273, vertices_97, vertices_545, vertices_321, vertices_577, vertices_769, vertices_90, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_44, vertices_140, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_164, vertices_772, vertices_152, vertices_280, vertices_168, vertices_552, vertices_112, vertices_208, vertices_336, vertices_224, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_557), (false, vertices_53), (false, vertices_789), (false, vertices_369), (false, vertices_737), (true, vertices_90), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_194), (true, vertices_642), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_148), (true, vertices_164), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_53) then 0 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_90) then 17 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_208) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_53), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
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
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 0 2 4 6 8 682 138 2
cert_row_2 2 0 2 3 5 90
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 7 8 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 218
cert_cover_5 1 2 0 2 3 6 90 218 3
cert_coverFacet 2 346
cert_cover_5 2 2 0 2 3 7 90 346 3
cert_coverFacet 3 682
cert_cover_5 3 1 0 2 4 6 138 682 2
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 172
cert_cover_2 7 2 1 4 6 44 172 3
cert_coverFacet 8 244
cert_cover_5 8 3 1 3 4 5 52 244 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0761

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0762.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0762

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 45, 589, 677, 361, 817, 710, 218, 346, 690, 786, 316, 156, 204, 180, 13, 37, 517, 41, 73, 289, 545, 321, 577, 769, 90, 146, 274, 530, 194, 322, 578, 642, 770, 28, 44, 76, 140, 52, 148, 164, 196, 580, 644, 152, 280, 296, 200, 328, 176, 304, 560, 784, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_45, vertices_589, vertices_677, vertices_361, vertices_817, vertices_710, vertices_218, vertices_346, vertices_690, vertices_786, vertices_316, vertices_156, vertices_204, vertices_180] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_517, vertices_41, vertices_73, vertices_289, vertices_545, vertices_321, vertices_577, vertices_769, vertices_90, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_44, vertices_76, vertices_140, vertices_52, vertices_148, vertices_164, vertices_196, vertices_580, vertices_644, vertices_152, vertices_280, vertices_296, vertices_200, vertices_328, vertices_176, vertices_304, vertices_560, vertices_784, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_45), (false, vertices_589), (false, vertices_677), (false, vertices_361), (false, vertices_817), (true, vertices_90), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_642), (true, vertices_28), (true, vertices_140), (true, vertices_52), (true, vertices_148), (true, vertices_196), (true, vertices_152), (true, vertices_280), (true, vertices_200), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_45) then 0 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_90) then 17 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_176) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 45 146 274 530 194 642 28 140 52 148 196 152 280 200 176 835 90 589 677 361 817
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 4 7 316 28 3
cert_row_2 1 0 2 3 5 90
cert_row_4 2 0 1 5 6 8 710 194 1
cert_row_4 3 0 3 4 6 8 690 146 2
cert_rows
cert_pivot_2 7 2 1 0
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 2 0 1 5 6 194 710 1
cert_coverFacet 1 218
cert_cover_5 1 1 0 2 3 6 90 218 3
cert_coverFacet 2 346
cert_cover_5 2 1 0 2 3 7 90 346 3
cert_coverFacet 3 690
cert_cover_5 3 3 0 3 4 6 146 690 2
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 316
cert_cover_5 5 0 1 2 3 4 28 316 3
cert_coverFacet 6 156
cert_cover_2 6 2 1 3 6 28 156 3
cert_coverFacet 7 204
cert_cover_2 7 2 1 5 6 76 204 3
cert_coverFacet 8 180
cert_cover_2 8 3 1 4 6 52 180 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0762

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0763.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0763

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 557, 293, 837, 689, 481, 590, 570, 218, 658, 60, 284, 332, 436, 472, 37, 261, 517, 161, 289, 545, 193, 321, 577, 641, 26, 74, 522, 146, 530, 194, 578, 642, 28, 44, 76, 268, 524, 52, 276, 292, 324, 580, 56, 216, 280, 552, 328, 176, 560, 400, 656, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_557, vertices_293, vertices_837, vertices_689, vertices_481, vertices_590, vertices_570, vertices_218, vertices_658, vertices_60, vertices_284, vertices_332, vertices_436, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_26, vertices_74, vertices_522, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_28, vertices_44, vertices_76, vertices_268, vertices_524, vertices_52, vertices_276, vertices_292, vertices_324, vertices_580, vertices_56, vertices_216, vertices_280, vertices_552, vertices_328, vertices_176, vertices_560, vertices_400, vertices_656, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_557), (false, vertices_293), (false, vertices_837), (false, vertices_689), (false, vertices_481), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_52), (true, vertices_276), (true, vertices_56), (true, vertices_216), (true, vertices_280), (true, vertices_328), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_216) then 21 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 6 7 436 52 3
cert_row_2 1 2 3 5 6 216
cert_row_4 2 0 1 2 5 8 590 74 1
cert_row_4 3 0 2 3 4 8 570 26 3
cert_rows
cert_pivot_2 7 6 1 0
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 2 0 1 2 5 74 590 1
cert_coverFacet 1 570
cert_cover_5 1 3 0 2 3 4 26 570 3
cert_coverFacet 2 218
cert_cover_5 2 1 0 2 3 5 26 218 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 60
cert_cover_2 4 2 1 3 4 28 60 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 332
cert_cover_2 6 2 1 5 7 76 332 3
cert_coverFacet 7 436
cert_cover_5 7 0 1 3 4 6 52 436 3
cert_coverFacet 8 472
cert_cover_5 8 1 2 3 5 7 216 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0763

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0764.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0764

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 341, 101, 421, 809, 625, 662, 278, 390, 426, 714, 778, 236, 724, 616, 37, 69, 261, 81, 273, 529, 97, 289, 545, 769, 22, 134, 262, 138, 266, 522, 274, 530, 386, 642, 770, 84, 660, 276, 100, 164, 196, 388, 104, 168, 296, 552, 200, 584, 776, 592, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_341, vertices_101, vertices_421, vertices_809, vertices_625, vertices_662, vertices_278, vertices_390, vertices_426, vertices_714, vertices_778, vertices_236, vertices_724, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_261, vertices_81, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_769, vertices_22, vertices_134, vertices_262, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_84, vertices_660, vertices_276, vertices_100, vertices_164, vertices_196, vertices_388, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_584, vertices_776, vertices_592, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_341), (false, vertices_101), (false, vertices_421), (false, vertices_809), (false, vertices_625), (true, vertices_22), (true, vertices_134), (true, vertices_262), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_386), (true, vertices_642), (true, vertices_660), (true, vertices_196), (true, vertices_104), (true, vertices_168), (true, vertices_200), (true, vertices_584), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_101) then 0 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_660) then 20 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_101), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 6 8 660
cert_row_4 1 0 2 4 6 7 426 138 2
cert_row_4 2 0 2 5 6 8 714 138 2
cert_row_4 3 1 2 4 5 6 236 100 1
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 22 662 3
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 426
cert_cover_5 3 1 0 2 4 6 138 426 2
cert_coverFacet 4 714
cert_cover_5 4 2 0 2 5 6 138 714 2
cert_coverFacet 5 778
cert_cover_2 5 2 0 7 8 266 778 3
cert_coverFacet 6 236
cert_cover_5 6 3 1 2 4 5 100 236 1
cert_coverFacet 7 724
cert_cover_5 7 0 1 3 5 6 84 724 3
cert_coverFacet 8 616
cert_cover_2 8 4 2 5 8 104 616 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0764

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0765.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0765

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 805, 361, 169, 713, 689, 566, 278, 774, 722, 338, 188, 300, 460, 468, 41, 73, 137, 161, 289, 545, 321, 577, 641, 769, 22, 262, 518, 82, 274, 530, 322, 578, 770, 44, 140, 268, 52, 148, 276, 292, 548, 452, 772, 168, 296, 200, 328, 176, 560, 208, 336, 656, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_805, vertices_361, vertices_169, vertices_713, vertices_689, vertices_566, vertices_278, vertices_774, vertices_722, vertices_338, vertices_188, vertices_300, vertices_460, vertices_468] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_137, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_641, vertices_769, vertices_22, vertices_262, vertices_518, vertices_82, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_44, vertices_140, vertices_268, vertices_52, vertices_148, vertices_276, vertices_292, vertices_548, vertices_452, vertices_772, vertices_168, vertices_296, vertices_200, vertices_328, vertices_176, vertices_560, vertices_208, vertices_336, vertices_656, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_805), (false, vertices_361), (false, vertices_169), (false, vertices_713), (false, vertices_689), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_452), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_52) then 10 else
  if p.val = (true, vertices_148) then 11 else
  if p.val = (true, vertices_276) then 12 else
  if p.val = (true, vertices_452) then 19 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 169 2 22 1 262 3 518 82 274 530 44 140 268 52 148 276 208 336 835 805 452 361 713 689
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 5 6 7 452
cert_row_4 1 0 3 5 6 8 722 82 3
cert_row_4 2 0 1 3 4 8 566 22 3
cert_row_4 3 1 2 3 4 6 188 44 2
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 2 0 1 3 4 22 566 3
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 722
cert_cover_5 3 1 0 3 5 6 82 722 3
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 188
cert_cover_5 5 3 1 2 3 4 44 188 2
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 460
cert_cover_5 7 0 1 2 5 6 140 460 2
cert_coverFacet 8 468
cert_cover_5 8 0 1 3 5 6 148 468 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0765

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0766.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0766

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 805, 233, 297, 841, 689, 566, 214, 838, 658, 316, 468, 184, 408, 456, 41, 73, 265, 161, 289, 545, 193, 577, 641, 769, 22, 70, 518, 146, 530, 194, 578, 642, 52, 212, 276, 292, 548, 324, 772, 56, 152, 280, 168, 296, 200, 328, 392, 176, 560, 400, 656, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_805, vertices_233, vertices_297, vertices_841, vertices_689, vertices_566, vertices_214, vertices_838, vertices_658, vertices_316, vertices_468, vertices_184, vertices_408, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_641, vertices_769, vertices_22, vertices_70, vertices_518, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_52, vertices_212, vertices_276, vertices_292, vertices_548, vertices_324, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_296, vertices_200, vertices_328, vertices_392, vertices_176, vertices_560, vertices_400, vertices_656, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_805), (false, vertices_233), (false, vertices_297), (false, vertices_841), (false, vertices_689), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_146), (true, vertices_530), (true, vertices_52), (true, vertices_212), (true, vertices_276), (true, vertices_324), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_392), (true, vertices_400), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_212) then 19 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 297 2 22 1 70 3 518 146 530 52 276 324 56 152 280 392 400 448 707 805 212 233 841 689
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 5 6 212
cert_row_4 1 0 1 5 7 8 838 70 3
cert_row_4 2 0 1 3 4 8 566 22 3
cert_row_4 3 1 2 3 4 7 316 52 1
cert_rows
cert_pivot_2 6 5 0 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 2 0 1 3 4 22 566 3
cert_coverFacet 1 214
cert_cover_5 1 0 0 1 3 5 22 214 3
cert_coverFacet 2 838
cert_cover_5 2 1 0 1 5 7 70 838 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 316
cert_cover_5 4 3 1 2 3 4 52 316 1
cert_coverFacet 5 468
cert_cover_5 5 0 1 3 5 7 212 468 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0766

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0767.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0767

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 789, 613, 325, 713, 465, 806, 410, 618, 298, 650, 786, 236, 428, 452, 69, 261, 517, 145, 273, 529, 193, 321, 577, 641, 42, 138, 266, 522, 146, 274, 530, 290, 546, 642, 770, 172, 100, 292, 548, 196, 324, 388, 772, 104, 296, 200, 584, 392, 648, 400, 784, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_789, vertices_613, vertices_325, vertices_713, vertices_465, vertices_806, vertices_410, vertices_618, vertices_298, vertices_650, vertices_786, vertices_236, vertices_428, vertices_452] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_42, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_642, vertices_770, vertices_172, vertices_100, vertices_292, vertices_548, vertices_196, vertices_324, vertices_388, vertices_772, vertices_104, vertices_296, vertices_200, vertices_584, vertices_392, vertices_648, vertices_400, vertices_784, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_789), (false, vertices_613), (false, vertices_325), (false, vertices_713), (false, vertices_465), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_172), (true, vertices_292), (true, vertices_196), (true, vertices_388), (true, vertices_104), (true, vertices_296), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_172) then 20 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_172), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
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
cert_row_4 0 0 2 3 6 7 410 138 2
cert_row_2 1 1 2 4 6 172
cert_row_4 2 0 1 4 7 8 806 290 1
cert_row_4 3 0 2 4 5 8 618 42 3
cert_rows
cert_pivot_2 3 6 1 0
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 2 0 1 4 7 290 806 1
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 6 138 410 2
cert_coverFacet 2 618
cert_cover_5 2 3 0 2 4 5 42 618 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 236
cert_cover_5 6 1 1 2 4 5 172 236 3
cert_coverFacet 7 428
cert_cover_5 7 1 1 2 4 7 172 428 3
cert_coverFacet 8 452
cert_cover_2 8 5 1 6 7 196 452 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0767

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0768.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0768

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 541, 269, 805, 361, 713, 225, 406, 534, 422, 550, 722, 348, 600, 496, 13, 261, 517, 73, 265, 521, 97, 161, 289, 545, 193, 641, 22, 38, 390, 518, 146, 530, 162, 546, 642, 28, 268, 276, 532, 292, 548, 88, 536, 328, 584, 208, 336, 592, 400, 224, 352, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_541, vertices_269, vertices_805, vertices_361, vertices_713, vertices_225, vertices_406, vertices_534, vertices_422, vertices_550, vertices_722, vertices_348, vertices_600, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_641, vertices_22, vertices_38, vertices_390, vertices_518, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_28, vertices_268, vertices_276, vertices_532, vertices_292, vertices_548, vertices_88, vertices_536, vertices_328, vertices_584, vertices_208, vertices_336, vertices_592, vertices_400, vertices_224, vertices_352, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_541), (false, vertices_269), (false, vertices_805), (false, vertices_361), (false, vertices_713), (false, vertices_225), (true, vertices_22), (true, vertices_38), (true, vertices_390), (true, vertices_518), (true, vertices_146), (true, vertices_530), (true, vertices_276), (true, vertices_88), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_541) then 18 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_38) then 3 else
  if p.val = (true, vertices_390) then 16 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
cert_nodeAtPriority_25 0 269 1 225 22 38 518 146 530 276 88 208 336 592 400 416 675 390 541 805 361 713
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 8 722 146 2
cert_row_2 1 0 1 6 7 390
cert_row_4 2 1 2 3 5 7 348 28 3
cert_row_4 3 3 4 5 6 7 496 208 1
cert_rows
cert_pivot_2 8 0 1 3
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 1 0 1 3 6 22 406 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 422
cert_cover_5 2 1 0 1 4 6 38 422 3
cert_coverFacet 3 550
cert_cover_2 3 1 0 4 8 38 550 3
cert_coverFacet 4 722
cert_cover_5 4 0 0 3 5 6 146 722 2
cert_coverFacet 5 348
cert_cover_5 5 2 1 2 3 5 28 348 3
cert_coverFacet 6 600
cert_cover_2 6 3 2 5 8 88 600 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 208 496 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0768

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0769.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0769

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [91, 587, 403, 803, 421, 625, 177, 782, 282, 620, 204, 396, 244, 804, 472, 75, 19, 259, 515, 49, 81, 145, 161, 289, 545, 577, 385, 26, 266, 522, 274, 770, 76, 140, 268, 524, 100, 164, 292, 548, 196, 388, 772, 88, 280, 200, 584, 392, 112, 176, 208, 400, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_91, vertices_587, vertices_403, vertices_803, vertices_421, vertices_625, vertices_177, vertices_782, vertices_282, vertices_620, vertices_204, vertices_396, vertices_244, vertices_804, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_75, vertices_19, vertices_259, vertices_515, vertices_49, vertices_81, vertices_145, vertices_161, vertices_289, vertices_545, vertices_577, vertices_385, vertices_26, vertices_266, vertices_522, vertices_274, vertices_770, vertices_76, vertices_140, vertices_268, vertices_524, vertices_100, vertices_164, vertices_292, vertices_548, vertices_196, vertices_388, vertices_772, vertices_88, vertices_280, vertices_200, vertices_584, vertices_392, vertices_112, vertices_176, vertices_208, vertices_400, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_91), (false, vertices_587), (false, vertices_403), (false, vertices_803), (false, vertices_421), (false, vertices_625), (false, vertices_177), (true, vertices_266), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_100), (true, vertices_548), (true, vertices_196), (true, vertices_772), (true, vertices_280), (true, vertices_200), (true, vertices_392), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 14 16 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_91) then 17 else
  if p.val = (false, vertices_587) then 18 else
  if p.val = (false, vertices_403) then 20 else
  if p.val = (false, vertices_803) then 21 else
  if p.val = (false, vertices_421) then 15 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_208) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 1 2 4 5 8 620 76 2
cert_row_4 2 1 3 4 5 6 244 100 1
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 620
cert_cover_5 2 1 1 2 4 5 76 620 2
cert_coverFacet 3 204
cert_cover_2 3 2 1 5 6 76 204 3
cert_coverFacet 4 396
cert_cover_2 4 2 1 6 7 140 396 3
cert_coverFacet 5 244
cert_cover_5 5 2 1 3 4 5 100 244 1
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 88 472 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0769

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0770.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0770

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 661, 421, 185, 625, 801, 206, 526, 454, 602, 866, 652, 120, 664, 488, 133, 261, 517, 49, 145, 529, 161, 289, 545, 769, 14, 198, 262, 518, 74, 522, 322, 578, 770, 140, 524, 388, 644, 56, 88, 152, 536, 104, 168, 200, 648, 112, 592, 656, 352, 608, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_661, vertices_421, vertices_185, vertices_625, vertices_801, vertices_206, vertices_526, vertices_454, vertices_602, vertices_866, vertices_652, vertices_120, vertices_664, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_49, vertices_145, vertices_529, vertices_161, vertices_289, vertices_545, vertices_769, vertices_14, vertices_198, vertices_262, vertices_518, vertices_74, vertices_522, vertices_322, vertices_578, vertices_770, vertices_140, vertices_524, vertices_388, vertices_644, vertices_56, vertices_88, vertices_152, vertices_536, vertices_104, vertices_168, vertices_200, vertices_648, vertices_112, vertices_592, vertices_656, vertices_352, vertices_608, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_661), (false, vertices_421), (false, vertices_185), (false, vertices_625), (false, vertices_801), (true, vertices_14), (true, vertices_198), (true, vertices_74), (true, vertices_522), (true, vertices_322), (true, vertices_578), (true, vertices_140), (true, vertices_524), (true, vertices_88), (true, vertices_536), (true, vertices_104), (true, vertices_200), (true, vertices_648), (true, vertices_352), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_185) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_198) then 17 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 801 14 74 522 322 578 140 524 88 536 104 200 648 352 448 775 198 661 421 185 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_4 1 0 2 3 5 8 602 74 2
cert_row_4 2 0 4 5 7 8 866 322 1
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 454
cert_cover_5 2 0 0 1 5 7 198 454 3
cert_coverFacet 3 602
cert_cover_5 3 1 0 2 3 5 74 602 2
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 322 866 1
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 104 488 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0770

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0771.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0771

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 557, 141, 117, 405, 305, 929, 590, 346, 410, 962, 92, 156, 612, 880, 13, 21, 37, 133, 137, 521, 49, 273, 289, 545, 385, 641, 282, 74, 138, 522, 322, 578, 386, 642, 28, 76, 140, 524, 84, 148, 100, 548, 580, 88, 152, 112, 304, 336, 400, 608, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_557, vertices_141, vertices_117, vertices_405, vertices_305, vertices_929, vertices_590, vertices_346, vertices_410, vertices_962, vertices_92, vertices_156, vertices_612, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_37, vertices_133, vertices_137, vertices_521, vertices_49, vertices_273, vertices_289, vertices_545, vertices_385, vertices_641, vertices_282, vertices_74, vertices_138, vertices_522, vertices_322, vertices_578, vertices_386, vertices_642, vertices_28, vertices_76, vertices_140, vertices_524, vertices_84, vertices_148, vertices_100, vertices_548, vertices_580, vertices_88, vertices_152, vertices_112, vertices_304, vertices_336, vertices_400, vertices_608, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_557), (false, vertices_141), (false, vertices_117), (false, vertices_405), (false, vertices_305), (false, vertices_929), (true, vertices_282), (true, vertices_74), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_28), (true, vertices_76), (true, vertices_580), (true, vertices_88), (true, vertices_152), (true, vertices_336), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_117) then 19 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (false, vertices_929) then 24 else
  if p.val = (true, vertices_282) then 16 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_282), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 74 1
cert_row_2 1 0 2 3 7 282
cert_row_4 2 0 5 6 7 8 962 322 2
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 74 590 1
cert_coverFacet 1 346
cert_cover_5 1 1 0 2 3 5 282 346 3
cert_coverFacet 2 410
cert_cover_5 2 1 0 2 3 6 282 410 3
cert_coverFacet 3 962
cert_cover_5 3 2 0 5 6 7 322 962 2
cert_coverFacet 4 92
cert_cover_2 4 2 1 3 5 28 92 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 880
cert_cover_5 7 3 3 4 5 7 112 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0771

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0772.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0772

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 307, 899, 173, 101, 709, 865, 662, 794, 156, 540, 108, 844, 376, 184, 51, 131, 259, 37, 69, 133, 97, 161, 289, 577, 641, 769, 146, 274, 530, 642, 770, 28, 44, 76, 140, 524, 148, 532, 100, 580, 644, 56, 152, 280, 536, 104, 168, 328, 776, 176, 304, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_307, vertices_899, vertices_173, vertices_101, vertices_709, vertices_865, vertices_662, vertices_794, vertices_156, vertices_540, vertices_108, vertices_844, vertices_376, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_51, vertices_131, vertices_259, vertices_37, vertices_69, vertices_133, vertices_97, vertices_161, vertices_289, vertices_577, vertices_641, vertices_769, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_28, vertices_44, vertices_76, vertices_140, vertices_524, vertices_148, vertices_532, vertices_100, vertices_580, vertices_644, vertices_56, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_328, vertices_776, vertices_176, vertices_304, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_307), (false, vertices_899), (false, vertices_173), (false, vertices_101), (false, vertices_709), (false, vertices_865), (true, vertices_530), (true, vertices_28), (true, vertices_76), (true, vertices_524), (true, vertices_148), (true, vertices_532), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_104), (true, vertices_328), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 15 else
  if p.val = (false, vertices_307) then 16 else
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_173) then 19 else
  if p.val = (false, vertices_101) then 0 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_865) then 24 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_776) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_101), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_4 1 0 2 3 7 8 794 274 1
cert_row_4 2 1 2 5 7 8 844 76 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 274 794 1
cert_coverFacet 2 156
cert_cover_2 2 2 1 3 6 28 156 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 108
cert_cover_2 4 2 1 4 5 44 108 3
cert_coverFacet 5 844
cert_cover_5 5 2 1 2 5 7 76 844 3
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 56 376 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0772

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0773.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0773

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 787, 707, 229, 837, 570, 178, 402, 674, 316, 364, 180, 404, 856, 744, 131, 259, 515, 69, 133, 261, 193, 577, 769, 50, 146, 274, 530, 162, 546, 386, 642, 300, 52, 148, 276, 100, 164, 324, 388, 56, 280, 536, 104, 552, 328, 584, 176, 400, 784, 224, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_787, vertices_707, vertices_229, vertices_837, vertices_570, vertices_178, vertices_402, vertices_674, vertices_316, vertices_364, vertices_180, vertices_404, vertices_856, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_69, vertices_133, vertices_261, vertices_193, vertices_577, vertices_769, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_386, vertices_642, vertices_300, vertices_52, vertices_148, vertices_276, vertices_100, vertices_164, vertices_324, vertices_388, vertices_56, vertices_280, vertices_536, vertices_104, vertices_552, vertices_328, vertices_584, vertices_176, vertices_400, vertices_784, vertices_224, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_787), (false, vertices_707), (false, vertices_229), (false, vertices_837), (true, vertices_50), (true, vertices_146), (true, vertices_162), (true, vertices_546), (true, vertices_300), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_104), (true, vertices_552), (true, vertices_328), (true, vertices_584), (true, vertices_176), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 25 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 18 else
  if p.val = (false, vertices_787) then 19 else
  if p.val = (false, vertices_707) then 20 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_837) then 23 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_300) then 24 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_672) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_300), by decide +kernel⟩
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
cert_row_2 0 1 2 4 7 300
cert_row_4 1 0 2 3 4 8 570 50 1
cert_row_4 2 2 3 5 7 8 856 280 2
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 1 0 3 2
cert_heightProof 4
cert_coverFacet 0 570
cert_cover_5 0 1 0 2 3 4 50 570 1
cert_coverFacet 1 178
cert_cover_2 1 3 0 4 6 50 178 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 674
cert_cover_2 3 4 0 6 8 162 674 3
cert_coverFacet 4 316
cert_cover_5 4 0 1 2 3 4 300 316 2
cert_coverFacet 5 364
cert_cover_5 5 0 1 2 4 5 300 364 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 856
cert_cover_5 8 2 2 3 5 7 280 856 2
cert_coverFacet 9 744
cert_cover_5 9 3 2 4 5 6 104 744 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0773

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0774.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0774

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 109, 805, 709, 345, 297, 449, 666, 282, 810, 466, 244, 692, 120, 568, 37, 69, 517, 41, 73, 265, 289, 193, 321, 385, 641, 769, 26, 266, 522, 146, 274, 386, 642, 770, 180, 100, 548, 196, 644, 56, 88, 280, 536, 104, 296, 552, 112, 560, 208, 336, 656, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_109, vertices_805, vertices_709, vertices_345, vertices_297, vertices_449, vertices_666, vertices_282, vertices_810, vertices_466, vertices_244, vertices_692, vertices_120, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_41, vertices_73, vertices_265, vertices_289, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_266, vertices_522, vertices_146, vertices_274, vertices_386, vertices_642, vertices_770, vertices_180, vertices_100, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_112, vertices_560, vertices_208, vertices_336, vertices_656, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_109), (false, vertices_805), (false, vertices_709), (false, vertices_345), (false, vertices_297), (false, vertices_449), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_180), (true, vertices_56), (true, vertices_536), (true, vertices_552), (true, vertices_112), (true, vertices_560), (true, vertices_208), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 19 16 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_109) then 17 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_345) then 18 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_449) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_180) then 22 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_656) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_180), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 4 6 180
cert_row_4 1 0 2 4 7 8 810 266 2
cert_row_4 2 0 2 3 6 8 666 26 3
cert_row_4 3 0 3 5 6 7 466 146 2
cert_rows
cert_pivot_2 1 4 2 0
cert_heightProof 4
cert_coverFacet 0 666
cert_cover_5 0 2 0 2 3 6 26 666 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 810
cert_cover_5 2 1 0 2 4 7 266 810 2
cert_coverFacet 3 466
cert_cover_5 3 3 0 3 5 6 146 466 2
cert_coverFacet 4 244
cert_cover_5 4 0 1 3 4 5 180 244 3
cert_coverFacet 5 692
cert_cover_5 5 0 1 3 4 8 180 692 3
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0774

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0775.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0775

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 597, 281, 425, 713, 465, 286, 302, 566, 170, 650, 738, 340, 484, 612, 25, 137, 265, 521, 81, 273, 529, 193, 577, 385, 270, 22, 38, 26, 42, 138, 522, 530, 162, 546, 642, 84, 276, 532, 100, 292, 548, 324, 580, 280, 168, 296, 648, 336, 224, 608, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_597, vertices_281, vertices_425, vertices_713, vertices_465, vertices_286, vertices_302, vertices_566, vertices_170, vertices_650, vertices_738, vertices_340, vertices_484, vertices_612] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_521, vertices_81, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_270, vertices_22, vertices_38, vertices_26, vertices_42, vertices_138, vertices_522, vertices_530, vertices_162, vertices_546, vertices_642, vertices_84, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_280, vertices_168, vertices_296, vertices_648, vertices_336, vertices_224, vertices_608, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_597), (false, vertices_281), (false, vertices_425), (false, vertices_713), (false, vertices_465), (true, vertices_270), (true, vertices_22), (true, vertices_38), (true, vertices_42), (true, vertices_138), (true, vertices_162), (true, vertices_546), (true, vertices_642), (true, vertices_276), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_324), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 16 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_270) then 17 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_324) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 281 22 38 42 138 162 546 642 276 100 292 548 324 224 608 539 270 597 425 713 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 7 270
cert_row_4 1 0 1 3 4 8 566 22 3
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 270 286 3
cert_coverFacet 1 302
cert_cover_5 1 0 0 1 2 4 270 302 3
cert_coverFacet 2 566
cert_cover_5 2 1 0 1 3 4 22 566 3
cert_coverFacet 3 170
cert_cover_2 3 2 0 4 6 42 170 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 162 738 2
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 100 484 3
cert_coverFacet 8 612
cert_cover_2 8 4 1 5 8 100 612 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0775

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0776.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0776

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 781, 789, 681, 433, 721, 334, 526, 598, 554, 738, 354, 212, 404, 484, 773, 41, 265, 521, 145, 273, 529, 161, 289, 641, 14, 70, 518, 42, 266, 522, 98, 290, 546, 322, 578, 268, 524, 84, 148, 276, 532, 196, 324, 388, 552, 208, 592, 400, 224, 352, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_781, vertices_789, vertices_681, vertices_433, vertices_721, vertices_334, vertices_526, vertices_598, vertices_554, vertices_738, vertices_354, vertices_212, vertices_404, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_773, vertices_41, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_641, vertices_14, vertices_70, vertices_518, vertices_42, vertices_266, vertices_522, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_388, vertices_552, vertices_208, vertices_592, vertices_400, vertices_224, vertices_352, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_781), (false, vertices_789), (false, vertices_681), (false, vertices_433), (false, vertices_721), (true, vertices_14), (true, vertices_70), (true, vertices_518), (true, vertices_522), (true, vertices_98), (true, vertices_546), (true, vertices_322), (true, vertices_578), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 7 334 14 3
cert_row_4 1 0 1 3 5 8 598 70 2
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 1 4 5 6 7 484 196 1
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 598
cert_cover_5 2 1 0 1 3 5 70 598 2
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 98 738 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 484
cert_cover_5 8 3 1 4 5 6 196 484 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0776

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0777.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0777

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 285, 541, 421, 709, 681, 598, 346, 538, 554, 738, 354, 212, 404, 496, 29, 133, 261, 517, 41, 265, 521, 161, 289, 641, 26, 42, 266, 522, 82, 530, 98, 290, 546, 322, 578, 84, 148, 276, 532, 196, 580, 388, 280, 536, 552, 208, 336, 400, 224, 352, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_285, vertices_541, vertices_421, vertices_709, vertices_681, vertices_598, vertices_346, vertices_538, vertices_554, vertices_738, vertices_354, vertices_212, vertices_404, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_133, vertices_261, vertices_517, vertices_41, vertices_265, vertices_521, vertices_161, vertices_289, vertices_641, vertices_26, vertices_42, vertices_266, vertices_522, vertices_82, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_580, vertices_388, vertices_280, vertices_536, vertices_552, vertices_208, vertices_336, vertices_400, vertices_224, vertices_352, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_285), (false, vertices_541), (false, vertices_421), (false, vertices_709), (false, vertices_681), (true, vertices_26), (true, vertices_522), (true, vertices_82), (true, vertices_530), (true, vertices_98), (true, vertices_546), (true, vertices_322), (true, vertices_578), (true, vertices_84), (true, vertices_148), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 21 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_421) then 22 else
  if p.val = (false, vertices_709) then 23 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 26 2 522 1 82 530 98 546 322 578 84 148 208 336 400 224 352 299 285 541 681 421 709
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 82 1
cert_row_4 1 0 2 3 5 7 346 26 3
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 3 4 5 6 7 496 208 1
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 82 598 1
cert_coverFacet 1 346
cert_cover_5 1 1 0 2 3 5 26 346 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 98 738 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 208 496 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0777

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3333 : Certifies 3333 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0748.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3334 : Certifies 3334 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0749.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3335 : Certifies 3335 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0750.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3336 : Certifies 3336 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0751.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3337 : Certifies 3337 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0752.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3338 : Certifies 3338 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0753.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3339 : Certifies 3339 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0754.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3340 : Certifies 3340 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0755.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3341 : Certifies 3341 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0756.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3342 : Certifies 3342 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0757.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3343 : Certifies 3343 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0758.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3344 : Certifies 3344 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0759.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3345 : Certifies 3345 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0760.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3346 : Certifies 3346 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0761.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3347 : Certifies 3347 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0762.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3348 : Certifies 3348 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0763.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3349 : Certifies 3349 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0764.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3350 : Certifies 3350 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0765.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3351 : Certifies 3351 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0766.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3352 : Certifies 3352 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0767.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3353 : Certifies 3353 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0768.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3354 : Certifies 3354 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0769.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3355 : Certifies 3355 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0770.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3356 : Certifies 3356 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0771.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3357 : Certifies 3357 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0772.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3358 : Certifies 3358 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0773.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3359 : Certifies 3359 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0774.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3360 : Certifies 3360 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0775.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3361 : Certifies 3361 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0776.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3362 : Certifies 3362 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0777.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B110 (j : Fin 30) :
    Certifies (3333 + j.val) := by
  fin_cases j
  · exact projection_3333
  · exact projection_3334
  · exact projection_3335
  · exact projection_3336
  · exact projection_3337
  · exact projection_3338
  · exact projection_3339
  · exact projection_3340
  · exact projection_3341
  · exact projection_3342
  · exact projection_3343
  · exact projection_3344
  · exact projection_3345
  · exact projection_3346
  · exact projection_3347
  · exact projection_3348
  · exact projection_3349
  · exact projection_3350
  · exact projection_3351
  · exact projection_3352
  · exact projection_3353
  · exact projection_3354
  · exact projection_3355
  · exact projection_3356
  · exact projection_3357
  · exact projection_3358
  · exact projection_3359
  · exact projection_3360
  · exact projection_3361
  · exact projection_3362

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
