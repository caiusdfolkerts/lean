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
/- Source: ProjectionCertificates/R_m15e10q1_0029.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0029

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 157, 589, 453, 689, 737, 782, 282, 626, 306, 482, 834, 396, 836, 440, 13, 69, 133, 25, 521, 145, 529, 673, 193, 577, 26, 266, 522, 50, 274, 530, 98, 290, 322, 578, 770, 140, 268, 524, 324, 580, 388, 772, 152, 280, 392, 176, 304, 560, 224, 608, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_157, vertices_589, vertices_453, vertices_689, vertices_737, vertices_782, vertices_282, vertices_626, vertices_306, vertices_482, vertices_834, vertices_396, vertices_836, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_133, vertices_25, vertices_521, vertices_145, vertices_529, vertices_673, vertices_193, vertices_577, vertices_26, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_98, vertices_290, vertices_322, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_324, vertices_580, vertices_388, vertices_772, vertices_152, vertices_280, vertices_392, vertices_176, vertices_304, vertices_560, vertices_224, vertices_608, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_157), (false, vertices_589), (false, vertices_453), (false, vertices_689), (false, vertices_737), (true, vertices_266), (true, vertices_50), (true, vertices_274), (true, vertices_98), (true, vertices_290), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_268), (true, vertices_772), (true, vertices_280), (true, vertices_392), (true, vertices_304), (true, vertices_416), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 22 23 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 16 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 0 3 4 5 8 626 50 3
cert_row_4 2 0 4 5 6 7 482 98 3
cert_row_4 3 2 3 4 6 7 440 152 2
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 626
cert_cover_5 2 1 0 3 4 5 50 626 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 482
cert_cover_5 4 2 0 4 5 6 98 482 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 836
cert_cover_2 7 5 1 7 8 324 836 3
cert_coverFacet 8 440
cert_cover_5 8 3 2 3 4 6 152 440 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0029

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0030.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0030

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 213, 837, 345, 689, 785, 110, 270, 230, 774, 314, 930, 332, 248, 816, 69, 133, 517, 81, 145, 273, 529, 321, 641, 769, 14, 102, 134, 262, 518, 42, 266, 162, 290, 642, 770, 76, 268, 196, 324, 772, 56, 88, 280, 104, 328, 176, 304, 560, 208, 784, 224, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_213, vertices_837, vertices_345, vertices_689, vertices_785, vertices_110, vertices_270, vertices_230, vertices_774, vertices_314, vertices_930, vertices_332, vertices_248, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_81, vertices_145, vertices_273, vertices_529, vertices_321, vertices_641, vertices_769, vertices_14, vertices_102, vertices_134, vertices_262, vertices_518, vertices_42, vertices_266, vertices_162, vertices_290, vertices_642, vertices_770, vertices_76, vertices_268, vertices_196, vertices_324, vertices_772, vertices_56, vertices_88, vertices_280, vertices_104, vertices_328, vertices_176, vertices_304, vertices_560, vertices_208, vertices_784, vertices_224, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_213), (false, vertices_837), (false, vertices_345), (false, vertices_689), (false, vertices_785), (true, vertices_14), (true, vertices_102), (true, vertices_262), (true, vertices_42), (true, vertices_266), (true, vertices_162), (true, vertices_290), (true, vertices_770), (true, vertices_76), (true, vertices_268), (true, vertices_56), (true, vertices_104), (true, vertices_304), (true, vertices_224), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_102) then 17 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 785 14 262 42 266 162 290 770 76 268 56 104 304 224 800 647 102 213 837 345 689
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 5 102
cert_row_4 1 0 4 6 7 8 930 162 3
cert_row_4 2 0 2 3 4 7 314 42 2
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 230
cert_cover_5 2 0 0 1 4 6 102 230 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 314
cert_cover_5 4 2 0 2 3 4 42 314 2
cert_coverFacet 5 930
cert_cover_5 5 1 0 4 6 7 162 930 3
cert_coverFacet 6 332
cert_cover_2 6 2 1 5 7 76 332 3
cert_coverFacet 7 248
cert_cover_5 7 3 2 3 4 5 56 248 3
cert_coverFacet 8 816
cert_cover_2 8 4 3 7 8 304 816 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0030

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0031.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0031

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 205, 405, 805, 581, 425, 609, 790, 666, 282, 298, 714, 866, 724, 408, 69, 133, 261, 517, 41, 73, 137, 97, 289, 545, 577, 385, 26, 42, 74, 650, 266, 274, 530, 98, 290, 578, 770, 148, 276, 532, 196, 580, 772, 152, 280, 296, 200, 392, 400, 656, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_205, vertices_405, vertices_805, vertices_581, vertices_425, vertices_609, vertices_790, vertices_666, vertices_282, vertices_298, vertices_714, vertices_866, vertices_724, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_517, vertices_41, vertices_73, vertices_137, vertices_97, vertices_289, vertices_545, vertices_577, vertices_385, vertices_26, vertices_42, vertices_74, vertices_650, vertices_266, vertices_274, vertices_530, vertices_98, vertices_290, vertices_578, vertices_770, vertices_148, vertices_276, vertices_532, vertices_196, vertices_580, vertices_772, vertices_152, vertices_280, vertices_296, vertices_200, vertices_392, vertices_400, vertices_656, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_205), (false, vertices_405), (false, vertices_805), (false, vertices_581), (false, vertices_425), (false, vertices_609), (true, vertices_26), (true, vertices_650), (true, vertices_266), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_578), (true, vertices_770), (true, vertices_532), (true, vertices_152), (true, vertices_280), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 15 else
  if p.val = (false, vertices_205) then 18 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_609) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_650) then 16 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 581 1 609 26 266 274 530 290 578 770 532 152 280 656 704 107 650 205 405 805 425
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 6 8 650
cert_row_4 1 0 4 5 7 8 866 98 3
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 1 3 5 6 8 724 148 2
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 666
cert_cover_5 1 0 0 2 3 6 26 666 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 714
cert_cover_5 4 0 0 2 5 6 74 714 3
cert_coverFacet 5 866
cert_cover_5 5 1 0 4 5 7 98 866 3
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 148 724 2
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0031

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0032.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0032

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 613, 121, 713, 433, 673, 334, 590, 806, 282, 650, 914, 372, 344, 928, 25, 73, 137, 49, 145, 97, 161, 545, 577, 641, 78, 262, 518, 26, 138, 266, 522, 146, 274, 642, 770, 100, 292, 548, 324, 580, 88, 280, 328, 584, 648, 112, 304, 336, 400, 416, 672, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_613, vertices_121, vertices_713, vertices_433, vertices_673, vertices_334, vertices_590, vertices_806, vertices_282, vertices_650, vertices_914, vertices_372, vertices_344, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_137, vertices_49, vertices_145, vertices_97, vertices_161, vertices_545, vertices_577, vertices_641, vertices_78, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_642, vertices_770, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_88, vertices_280, vertices_328, vertices_584, vertices_648, vertices_112, vertices_304, vertices_336, vertices_400, vertices_416, vertices_672, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_613), (false, vertices_121), (false, vertices_713), (false, vertices_433), (false, vertices_673), (true, vertices_78), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_642), (true, vertices_770), (true, vertices_292), (true, vertices_324), (true, vertices_280), (true, vertices_328), (true, vertices_336), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 16 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_121) then 21 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_673) then 0 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_800) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 673 262 518 266 522 274 642 770 292 324 280 328 336 800 896 155 78 613 121 713 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 3 6 7 8 914 146 3
cert_row_4 2 0 1 4 7 8 806 262 2
cert_row_4 3 1 3 4 5 7 372 100 1
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 7 78 334 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 806
cert_cover_5 2 2 0 1 4 7 262 806 2
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 914
cert_cover_5 5 1 0 3 6 7 146 914 3
cert_coverFacet 6 372
cert_cover_5 6 3 1 3 4 5 100 372 1
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 928
cert_cover_2 8 6 4 7 8 416 928 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0032

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0033.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0033

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 653, 453, 217, 585, 865, 406, 662, 122, 538, 810, 306, 664, 616, 496, 133, 261, 517, 73, 137, 521, 193, 321, 577, 769, 150, 262, 518, 26, 42, 522, 50, 274, 530, 290, 770, 388, 644, 88, 152, 536, 104, 552, 584, 648, 112, 304, 208, 400, 656, 352, 608, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_653, vertices_453, vertices_217, vertices_585, vertices_865, vertices_406, vertices_662, vertices_122, vertices_538, vertices_810, vertices_306, vertices_664, vertices_616, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_193, vertices_321, vertices_577, vertices_769, vertices_150, vertices_262, vertices_518, vertices_26, vertices_42, vertices_522, vertices_50, vertices_274, vertices_530, vertices_290, vertices_770, vertices_388, vertices_644, vertices_88, vertices_152, vertices_536, vertices_104, vertices_552, vertices_584, vertices_648, vertices_112, vertices_304, vertices_208, vertices_400, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_653), (false, vertices_453), (false, vertices_217), (false, vertices_585), (false, vertices_865), (true, vertices_150), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_536), (true, vertices_104), (true, vertices_552), (true, vertices_112), (true, vertices_304), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_217) then 22 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_150) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
cert_nodeAtPriority_34 585 26 42 522 50 274 530 290 536 104 552 112 304 400 656 775 150 653 453 217 865
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 6 150
cert_row_4 1 0 2 4 7 8 810 42 3
cert_row_4 2 0 2 3 4 5 122 26 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 8 0 3
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 7 150 406 3
cert_coverFacet 1 662
cert_cover_5 1 0 0 1 3 8 150 662 3
cert_coverFacet 2 122
cert_cover_5 2 2 0 2 3 4 26 122 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 810
cert_cover_5 4 1 0 2 4 7 42 810 3
cert_coverFacet 5 306
cert_cover_2 5 3 0 4 7 50 306 3
cert_coverFacet 6 664
cert_cover_2 6 3 2 6 8 152 664 3
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0033

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0034.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0034

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 781, 185, 553, 817, 465, 270, 526, 598, 454, 234, 618, 340, 788, 752, 41, 137, 265, 521, 49, 145, 273, 545, 385, 769, 14, 70, 262, 518, 106, 138, 266, 522, 194, 578, 386, 268, 524, 84, 276, 532, 324, 772, 168, 552, 176, 560, 208, 336, 592, 784, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_781, vertices_185, vertices_553, vertices_817, vertices_465, vertices_270, vertices_526, vertices_598, vertices_454, vertices_234, vertices_618, vertices_340, vertices_788, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_273, vertices_545, vertices_385, vertices_769, vertices_14, vertices_70, vertices_262, vertices_518, vertices_106, vertices_138, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_324, vertices_772, vertices_168, vertices_552, vertices_176, vertices_560, vertices_208, vertices_336, vertices_592, vertices_784, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_781), (false, vertices_185), (false, vertices_553), (false, vertices_817), (false, vertices_465), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_106), (true, vertices_522), (true, vertices_194), (true, vertices_578), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_324), (true, vertices_592), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_106) then 17 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
cert_nodeAtPriority_40 553 14 70 262 518 522 194 578 84 276 532 324 592 224 608 395 106 781 185 817 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 1 5 6 7 454 70 3
cert_row_4 2 0 1 3 5 8 598 70 2
cert_row_4 3 3 4 5 6 8 752 176 2
cert_rows
cert_pivot_2 2 7 0 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 598
cert_cover_5 2 2 0 1 3 5 70 598 2
cert_coverFacet 3 454
cert_cover_5 3 1 0 1 5 6 70 454 3
cert_coverFacet 4 234
cert_cover_5 4 0 0 2 4 6 106 234 3
cert_coverFacet 5 618
cert_cover_5 5 0 0 2 4 8 106 618 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 176 752 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0034

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0035.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0035

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 395, 563, 659, 453, 329, 737, 406, 58, 282, 796, 724, 836, 568, 872, 11, 531, 35, 131, 73, 265, 97, 545, 193, 321, 385, 641, 26, 42, 266, 50, 146, 274, 386, 148, 276, 532, 196, 324, 580, 388, 772, 56, 280, 536, 104, 552, 328, 776, 560, 656, 608, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_395, vertices_563, vertices_659, vertices_453, vertices_329, vertices_737, vertices_406, vertices_58, vertices_282, vertices_796, vertices_724, vertices_836, vertices_568, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_531, vertices_35, vertices_131, vertices_73, vertices_265, vertices_97, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_26, vertices_42, vertices_266, vertices_50, vertices_146, vertices_274, vertices_386, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_56, vertices_280, vertices_536, vertices_104, vertices_552, vertices_328, vertices_776, vertices_560, vertices_656, vertices_608, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_395), (false, vertices_563), (false, vertices_659), (false, vertices_453), (false, vertices_329), (false, vertices_737), (true, vertices_26), (true, vertices_274), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_580), (true, vertices_772), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_552), (true, vertices_776), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 14 16 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 17 else
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_563) then 20 else
  if p.val = (false, vertices_659) then 21 else
  if p.val = (false, vertices_453) then 15 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
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
cert_row_4 0 0 1 3 6 7 406 146 1
cert_row_4 1 1 3 5 6 8 724 148 2
cert_row_4 2 1 2 3 7 8 796 276 1
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 146 406 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 796
cert_cover_5 3 2 1 2 3 7 276 796 1
cert_coverFacet 4 724
cert_cover_5 4 1 1 3 5 6 148 724 2
cert_coverFacet 5 836
cert_cover_2 5 5 1 7 8 324 836 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 872
cert_cover_5 7 3 2 4 5 7 104 872 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0035

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0036.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0036

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 275, 419, 597, 453, 841, 785, 570, 794, 362, 178, 692, 708, 744, 480, 19, 131, 259, 21, 69, 133, 273, 529, 321, 577, 385, 769, 538, 42, 266, 50, 146, 274, 162, 290, 148, 532, 196, 580, 644, 104, 552, 328, 584, 776, 176, 560, 784, 224, 352, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_275, vertices_419, vertices_597, vertices_453, vertices_841, vertices_785, vertices_570, vertices_794, vertices_362, vertices_178, vertices_692, vertices_708, vertices_744, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_21, vertices_69, vertices_133, vertices_273, vertices_529, vertices_321, vertices_577, vertices_385, vertices_769, vertices_538, vertices_42, vertices_266, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_148, vertices_532, vertices_196, vertices_580, vertices_644, vertices_104, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_560, vertices_784, vertices_224, vertices_352, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_275), (false, vertices_419), (false, vertices_597), (false, vertices_453), (false, vertices_841), (false, vertices_785), (true, vertices_538), (true, vertices_42), (true, vertices_266), (true, vertices_50), (true, vertices_644), (true, vertices_104), (true, vertices_552), (true, vertices_176), (true, vertices_560), (true, vertices_224), (true, vertices_352), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 15 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_785) then 1 else
  if p.val = (true, vertices_538) then 17 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_538), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
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
cert_row_4 0 0 2 4 5 7 362 42 3
cert_row_2 1 0 2 3 8 538
cert_row_4 2 1 3 4 6 8 692 148 2
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 570
cert_cover_5 0 1 0 2 3 4 538 570 3
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 538 794 3
cert_coverFacet 2 362
cert_cover_5 2 0 0 2 4 5 42 362 3
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 692
cert_cover_5 4 2 1 3 4 6 148 692 2
cert_coverFacet 5 708
cert_cover_2 5 5 1 6 8 196 708 3
cert_coverFacet 6 744
cert_cover_5 6 3 2 4 5 6 104 744 3
cert_coverFacet 7 480
cert_cover_2 7 5 4 6 7 224 480 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0036

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0037.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0037

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 805, 793, 433, 737, 110, 526, 710, 346, 538, 466, 300, 780, 612, 488, 145, 273, 529, 161, 289, 545, 641, 769, 14, 70, 518, 26, 74, 522, 338, 146, 530, 194, 642, 44, 268, 524, 100, 292, 548, 580, 772, 280, 536, 104, 296, 328, 776, 400, 224, 608, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_805, vertices_793, vertices_433, vertices_737, vertices_110, vertices_526, vertices_710, vertices_346, vertices_538, vertices_466, vertices_300, vertices_780, vertices_612, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_14, vertices_70, vertices_518, vertices_26, vertices_74, vertices_522, vertices_338, vertices_146, vertices_530, vertices_194, vertices_642, vertices_44, vertices_268, vertices_524, vertices_100, vertices_292, vertices_548, vertices_580, vertices_772, vertices_280, vertices_536, vertices_104, vertices_296, vertices_328, vertices_776, vertices_400, vertices_224, vertices_608, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_805), (false, vertices_793), (false, vertices_433), (false, vertices_737), (true, vertices_14), (true, vertices_70), (true, vertices_518), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_338), (true, vertices_194), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_100), (true, vertices_580), (true, vertices_104), (true, vertices_296), (true, vertices_328), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_793) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_338) then 18 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_328) then 14 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
cert_nodeAtPriority_64 14 70 518 26 74 522 194 44 268 524 100 580 104 296 328 448 659 338 805 793 433 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 7 338
cert_row_4 1 0 1 5 6 8 710 70 3
cert_row_4 2 0 1 2 4 5 110 14 3
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 3 8 0 2
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 2 0 1 2 4 14 110 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 710
cert_cover_5 2 1 0 1 5 6 70 710 3
cert_coverFacet 3 346
cert_cover_5 3 0 0 2 3 5 26 346 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 466
cert_cover_5 5 0 0 3 5 6 338 466 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 612
cert_cover_2 8 4 1 5 8 100 612 3
cert_coverFacet 9 488
cert_cover_5 9 3 2 4 5 6 104 488 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0037

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0038.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0038

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 405, 837, 645, 681, 585, 481, 790, 58, 538, 842, 242, 466, 692, 568, 133, 261, 517, 41, 73, 521, 97, 161, 321, 577, 385, 641, 26, 42, 74, 522, 50, 210, 274, 530, 98, 322, 770, 148, 276, 532, 644, 772, 56, 536, 552, 584, 176, 560, 400, 224, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_405, vertices_837, vertices_645, vertices_681, vertices_585, vertices_481, vertices_790, vertices_58, vertices_538, vertices_842, vertices_242, vertices_466, vertices_692, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_73, vertices_521, vertices_97, vertices_161, vertices_321, vertices_577, vertices_385, vertices_641, vertices_26, vertices_42, vertices_74, vertices_522, vertices_50, vertices_210, vertices_274, vertices_530, vertices_98, vertices_322, vertices_770, vertices_148, vertices_276, vertices_532, vertices_644, vertices_772, vertices_56, vertices_536, vertices_552, vertices_584, vertices_176, vertices_560, vertices_400, vertices_224, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_405), (false, vertices_837), (false, vertices_645), (false, vertices_681), (false, vertices_585), (false, vertices_481), (true, vertices_26), (true, vertices_522), (true, vertices_50), (true, vertices_210), (true, vertices_274), (true, vertices_530), (true, vertices_322), (true, vertices_770), (true, vertices_532), (true, vertices_56), (true, vertices_536), (true, vertices_176), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 15 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_585) then 1 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_210) then 16 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_560) then 13 else
  0
cert_priority
cert_nodeAtPriority_53 0 645 1 585 26 522 50 274 530 322 770 532 56 536 176 560 107 210 405 837 681 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 74 3
cert_row_2 1 0 3 5 6 210
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 1 3 4 6 8 692 148 2
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 842
cert_cover_5 3 0 0 2 5 7 74 842 3
cert_coverFacet 4 242
cert_cover_5 4 1 0 3 4 5 50 242 3
cert_coverFacet 5 466
cert_cover_5 5 1 0 3 5 7 210 466 3
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 148 692 2
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0038

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0039.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0039

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 651, 211, 339, 357, 709, 186, 282, 778, 820, 612, 568, 792, 744, 496, 83, 131, 259, 515, 69, 261, 517, 193, 321, 641, 26, 138, 266, 522, 146, 274, 770, 100, 292, 548, 580, 772, 56, 280, 536, 168, 552, 648, 776, 176, 304, 560, 208, 336, 784, 224, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_651, vertices_211, vertices_339, vertices_357, vertices_709, vertices_186, vertices_282, vertices_778, vertices_820, vertices_612, vertices_568, vertices_792, vertices_744, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_83, vertices_131, vertices_259, vertices_515, vertices_69, vertices_261, vertices_517, vertices_193, vertices_321, vertices_641, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_770, vertices_100, vertices_292, vertices_548, vertices_580, vertices_772, vertices_56, vertices_280, vertices_536, vertices_168, vertices_552, vertices_648, vertices_776, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_784, vertices_224, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_651), (false, vertices_211), (false, vertices_339), (false, vertices_357), (false, vertices_709), (true, vertices_26), (true, vertices_266), (true, vertices_548), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_552), (true, vertices_776), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_784), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 15 23 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_651) then 20 else
  if p.val = (false, vertices_211) then 21 else
  if p.val = (false, vertices_339) then 22 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_56) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 6 186 26 3
cert_row_4 1 1 3 4 7 8 820 292 1
cert_row_4 2 2 4 5 6 8 744 168 2
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 186
cert_cover_5 0 0 0 2 3 4 26 186 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 292 820 1
cert_coverFacet 4 612
cert_cover_2 4 4 1 5 8 100 612 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 792
cert_cover_2 6 3 2 7 8 280 792 3
cert_coverFacet 7 744
cert_cover_5 7 2 2 4 5 6 168 744 2
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 176 496 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0039

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0040.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0040

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 403, 803, 557, 357, 453, 722, 786, 124, 716, 312, 600, 792, 808, 496, 131, 259, 515, 37, 325, 133, 517, 289, 545, 385, 146, 274, 530, 642, 770, 44, 76, 524, 100, 196, 644, 56, 88, 280, 536, 296, 552, 584, 776, 112, 304, 208, 592, 400, 784, 352, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_403, vertices_803, vertices_557, vertices_357, vertices_453, vertices_722, vertices_786, vertices_124, vertices_716, vertices_312, vertices_600, vertices_792, vertices_808, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_37, vertices_325, vertices_133, vertices_517, vertices_289, vertices_545, vertices_385, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_44, vertices_76, vertices_524, vertices_100, vertices_196, vertices_644, vertices_56, vertices_88, vertices_280, vertices_536, vertices_296, vertices_552, vertices_584, vertices_776, vertices_112, vertices_304, vertices_208, vertices_592, vertices_400, vertices_784, vertices_352, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_403), (false, vertices_803), (false, vertices_557), (false, vertices_357), (false, vertices_453), (true, vertices_530), (true, vertices_76), (true, vertices_56), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_296), (true, vertices_584), (true, vertices_776), (true, vertices_112), (true, vertices_304), (true, vertices_208), (true, vertices_592), (true, vertices_784), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 23 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_403) then 17 else
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_557) then 20 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (true, vertices_530) then 0 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_56) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 8 722 146 2
cert_row_4 1 1 2 5 6 8 716 76 3
cert_row_4 2 1 2 3 4 5 124 44 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 8 1 3
cert_heightProof 4
cert_coverFacet 0 722
cert_cover_5 0 0 0 3 5 6 146 722 2
cert_coverFacet 1 786
cert_cover_2 1 3 0 7 8 274 786 3
cert_coverFacet 2 124
cert_cover_5 2 2 1 2 3 4 44 124 2
cert_coverFacet 3 716
cert_cover_5 3 1 1 2 5 6 76 716 3
cert_coverFacet 4 312
cert_cover_2 4 3 2 4 7 56 312 3
cert_coverFacet 5 600
cert_cover_2 5 3 2 5 8 88 600 3
cert_coverFacet 6 792
cert_cover_2 6 3 2 7 8 280 792 3
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0040

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0041.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0041

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 653, 613, 453, 121, 217, 666, 282, 298, 786, 866, 916, 836, 312, 496, 69, 133, 517, 89, 41, 137, 521, 97, 545, 193, 26, 42, 266, 522, 274, 530, 290, 546, 770, 324, 580, 388, 644, 772, 56, 152, 280, 296, 648, 112, 304, 208, 400, 656, 784, 352, 608, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_653, vertices_613, vertices_453, vertices_121, vertices_217, vertices_666, vertices_282, vertices_298, vertices_786, vertices_866, vertices_916, vertices_836, vertices_312, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_89, vertices_41, vertices_137, vertices_521, vertices_97, vertices_545, vertices_193, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_152, vertices_280, vertices_296, vertices_648, vertices_112, vertices_304, vertices_208, vertices_400, vertices_656, vertices_784, vertices_352, vertices_608, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_653), (false, vertices_613), (false, vertices_453), (false, vertices_121), (false, vertices_217), (true, vertices_26), (true, vertices_266), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_770), (true, vertices_772), (true, vertices_280), (true, vertices_296), (true, vertices_304), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_352), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 16 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_121) then 22 else
  if p.val = (false, vertices_217) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 26 1 266 2 274 530 290 770 772 280 296 304 400 656 784 352 832 555 653 613 453 121 217
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 26 3
cert_row_4 1 0 4 5 7 8 866 290 2
cert_row_4 2 1 3 6 7 8 916 388 1
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 666
cert_cover_5 0 0 0 2 3 6 26 666 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 866
cert_cover_5 4 1 0 4 5 7 290 866 2
cert_coverFacet 5 916
cert_cover_5 5 2 1 3 6 7 388 916 1
cert_coverFacet 6 836
cert_cover_2 6 5 1 7 8 324 836 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0041

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0042.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0042

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 117, 181, 901, 681, 865, 94, 406, 282, 362, 216, 920, 232, 808, 240, 53, 69, 133, 261, 97, 161, 545, 321, 641, 769, 22, 70, 262, 26, 74, 266, 274, 322, 84, 148, 388, 88, 152, 280, 104, 168, 296, 552, 200, 648, 776, 112, 176, 208, 400, 224, 352, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_117, vertices_181, vertices_901, vertices_681, vertices_865, vertices_94, vertices_406, vertices_282, vertices_362, vertices_216, vertices_920, vertices_232, vertices_808, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_53, vertices_69, vertices_133, vertices_261, vertices_97, vertices_161, vertices_545, vertices_321, vertices_641, vertices_769, vertices_22, vertices_70, vertices_262, vertices_26, vertices_74, vertices_266, vertices_274, vertices_322, vertices_84, vertices_148, vertices_388, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_176, vertices_208, vertices_400, vertices_224, vertices_352, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_117), (false, vertices_181), (false, vertices_901), (false, vertices_681), (false, vertices_865), (true, vertices_22), (true, vertices_26), (true, vertices_74), (true, vertices_266), (true, vertices_274), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_776), (true, vertices_208), (true, vertices_400), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 16 else
  if p.val = (false, vertices_117) then 18 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_901) then 20 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
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
cert_row_4 0 0 2 4 5 7 362 74 2
cert_row_4 1 0 1 2 3 5 94 22 2
cert_row_4 2 0 1 3 6 7 406 22 3
cert_row_4 3 2 3 6 7 8 920 152 3
cert_rows
cert_pivot_2 4 5 0 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 3 22 94 2
cert_coverFacet 1 406
cert_cover_5 1 2 0 1 3 6 22 406 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 362
cert_cover_5 3 0 0 2 4 5 74 362 2
cert_coverFacet 4 216
cert_cover_2 4 3 2 5 6 88 216 3
cert_coverFacet 5 920
cert_cover_5 5 3 2 3 6 7 152 920 3
cert_coverFacet 6 232
cert_cover_2 6 4 2 5 6 104 232 3
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coverFacet 8 240
cert_cover_2 8 4 3 5 6 112 240 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0042

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0043.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0043

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 117, 581, 645, 361, 433, 961, 30, 526, 902, 186, 426, 842, 604, 120, 21, 69, 133, 517, 49, 145, 97, 289, 321, 577, 385, 641, 14, 22, 134, 518, 26, 170, 266, 522, 146, 386, 770, 28, 524, 84, 580, 644, 56, 88, 104, 296, 328, 584, 112, 176, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_117, vertices_581, vertices_645, vertices_361, vertices_433, vertices_961, vertices_30, vertices_526, vertices_902, vertices_186, vertices_426, vertices_842, vertices_604, vertices_120] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_133, vertices_517, vertices_49, vertices_145, vertices_97, vertices_289, vertices_321, vertices_577, vertices_385, vertices_641, vertices_14, vertices_22, vertices_134, vertices_518, vertices_26, vertices_170, vertices_266, vertices_522, vertices_146, vertices_386, vertices_770, vertices_28, vertices_524, vertices_84, vertices_580, vertices_644, vertices_56, vertices_88, vertices_104, vertices_296, vertices_328, vertices_584, vertices_112, vertices_176, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_117), (false, vertices_581), (false, vertices_645), (false, vertices_361), (false, vertices_433), (false, vertices_961), (true, vertices_14), (true, vertices_518), (true, vertices_26), (true, vertices_170), (true, vertices_266), (true, vertices_522), (true, vertices_386), (true, vertices_770), (true, vertices_28), (true, vertices_524), (true, vertices_56), (true, vertices_88), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 21 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 15 else
  if p.val = (false, vertices_117) then 18 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_645) then 1 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_170) then 16 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_584) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_645), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_170), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 6 170
cert_row_4 1 0 1 6 7 8 902 134 3
cert_row_4 2 0 2 5 7 8 842 266 2
cert_row_4 3 1 2 3 5 8 604 28 3
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 902
cert_cover_5 2 1 0 1 6 7 134 902 3
cert_coverFacet 3 186
cert_cover_5 3 0 0 2 3 4 26 186 3
cert_coverFacet 4 426
cert_cover_5 4 0 0 2 4 7 170 426 3
cert_coverFacet 5 842
cert_cover_5 5 2 0 2 5 7 266 842 2
cert_coverFacet 6 604
cert_cover_5 6 3 1 2 3 5 28 604 3
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0043

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0044.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0044

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 339, 707, 653, 229, 357, 314, 538, 778, 594, 188, 300, 780, 728, 496, 67, 259, 515, 101, 133, 261, 517, 193, 321, 641, 26, 266, 522, 82, 274, 530, 578, 770, 44, 140, 268, 524, 164, 292, 772, 56, 152, 536, 296, 648, 776, 176, 304, 208, 336, 592, 224, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_339, vertices_707, vertices_653, vertices_229, vertices_357, vertices_314, vertices_538, vertices_778, vertices_594, vertices_188, vertices_300, vertices_780, vertices_728, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_101, vertices_133, vertices_261, vertices_517, vertices_193, vertices_321, vertices_641, vertices_26, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_578, vertices_770, vertices_44, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_772, vertices_56, vertices_152, vertices_536, vertices_296, vertices_648, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_592, vertices_224, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_339), (false, vertices_707), (false, vertices_653), (false, vertices_229), (false, vertices_357), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_530), (true, vertices_44), (true, vertices_268), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_296), (true, vertices_776), (true, vertices_176), (true, vertices_304), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 23 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_339) then 17 else
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_653) then 20 else
  if p.val = (false, vertices_229) then 21 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 7 314 26 3
cert_row_4 1 1 2 3 4 6 188 44 2
cert_row_4 2 2 3 5 6 8 728 152 2
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 314
cert_cover_5 0 0 0 2 3 4 26 314 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 594
cert_cover_2 3 3 0 5 8 82 594 3
cert_coverFacet 4 188
cert_cover_5 4 1 1 2 3 4 44 188 2
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 728
cert_cover_5 7 2 2 3 5 6 152 728 2
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 176 496 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0044

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0045.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0045

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 453, 793, 433, 737, 833, 30, 334, 54, 678, 710, 602, 316, 420, 840, 49, 273, 529, 161, 545, 193, 321, 577, 385, 769, 14, 22, 38, 70, 646, 26, 74, 50, 530, 546, 578, 28, 268, 52, 164, 292, 196, 324, 388, 280, 536, 328, 584, 776, 304, 416, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_453, vertices_793, vertices_433, vertices_737, vertices_833, vertices_30, vertices_334, vertices_54, vertices_678, vertices_710, vertices_602, vertices_316, vertices_420, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_273, vertices_529, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_14, vertices_22, vertices_38, vertices_70, vertices_646, vertices_26, vertices_74, vertices_50, vertices_530, vertices_546, vertices_578, vertices_28, vertices_268, vertices_52, vertices_164, vertices_292, vertices_196, vertices_324, vertices_388, vertices_280, vertices_536, vertices_328, vertices_584, vertices_776, vertices_304, vertices_416, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_453), (false, vertices_793), (false, vertices_433), (false, vertices_737), (false, vertices_833), (true, vertices_14), (true, vertices_22), (true, vertices_38), (true, vertices_70), (true, vertices_646), (true, vertices_26), (true, vertices_74), (true, vertices_578), (true, vertices_28), (true, vertices_268), (true, vertices_52), (true, vertices_164), (true, vertices_292), (true, vertices_328), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_38) then 3 else
  if p.val = (true, vertices_70) then 4 else
  if p.val = (true, vertices_646) then 17 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_74) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_52) then 10 else
  if p.val = (true, vertices_164) then 11 else
  if p.val = (true, vertices_292) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_584) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 833 14 22 38 70 26 74 578 28 268 52 164 292 328 584 563 646 453 793 433 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 8 646
cert_row_4 1 0 2 3 5 8 602 26 3
cert_row_4 2 0 1 2 5 7 334 14 3
cert_row_4 3 1 2 3 4 7 316 28 3
cert_rows
cert_pivot_2 6 8 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 334
cert_cover_5 1 2 0 1 2 5 14 334 3
cert_coverFacet 2 54
cert_cover_2 2 1 0 3 4 22 54 3
cert_coverFacet 3 678
cert_cover_5 3 0 0 1 4 6 38 678 3
cert_coverFacet 4 710
cert_cover_5 4 0 0 1 5 6 70 710 3
cert_coverFacet 5 602
cert_cover_5 5 1 0 2 3 5 26 602 3
cert_coverFacet 6 316
cert_cover_5 6 3 1 2 3 4 28 316 3
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coverFacet 8 840
cert_cover_2 8 5 2 7 8 328 840 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0045

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0046.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0046

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 781, 357, 709, 665, 449, 118, 570, 218, 810, 354, 450, 820, 596, 720, 69, 261, 517, 137, 265, 521, 193, 321, 385, 641, 26, 554, 138, 266, 50, 82, 98, 290, 194, 322, 386, 52, 84, 532, 100, 292, 580, 772, 152, 536, 776, 560, 208, 592, 656, 352, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_781, vertices_357, vertices_709, vertices_665, vertices_449, vertices_118, vertices_570, vertices_218, vertices_810, vertices_354, vertices_450, vertices_820, vertices_596, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_385, vertices_641, vertices_26, vertices_554, vertices_138, vertices_266, vertices_50, vertices_82, vertices_98, vertices_290, vertices_194, vertices_322, vertices_386, vertices_52, vertices_84, vertices_532, vertices_100, vertices_292, vertices_580, vertices_772, vertices_152, vertices_536, vertices_776, vertices_560, vertices_208, vertices_592, vertices_656, vertices_352, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_781), (false, vertices_357), (false, vertices_709), (false, vertices_665), (false, vertices_449), (true, vertices_26), (true, vertices_554), (true, vertices_50), (true, vertices_82), (true, vertices_98), (true, vertices_290), (true, vertices_194), (true, vertices_322), (true, vertices_52), (true, vertices_84), (true, vertices_532), (true, vertices_560), (true, vertices_208), (true, vertices_592), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_665) then 23 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_554) then 17 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
cert_nodeAtPriority_51 449 26 50 82 98 290 194 322 52 84 532 560 208 592 800 395 554 781 357 709 665
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 6 218 26 3
cert_row_2 1 0 2 4 8 554
cert_row_4 2 0 1 3 4 5 118 50 1
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 2 0 1 3 4 50 118 1
cert_coverFacet 1 570
cert_cover_5 1 1 0 2 3 4 26 570 3
cert_coverFacet 2 218
cert_cover_5 2 0 0 2 3 5 26 218 3
cert_coverFacet 3 810
cert_cover_5 3 1 0 2 4 7 554 810 3
cert_coverFacet 4 354
cert_cover_2 4 4 0 5 7 98 354 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 820
cert_cover_5 6 3 1 3 4 7 52 820 3
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 720
cert_cover_2 8 5 3 6 8 208 720 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0046

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0047.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0047

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 307, 531, 579, 181, 721, 481, 790, 714, 778, 668, 236, 364, 780, 308, 19, 67, 259, 515, 49, 145, 529, 161, 289, 193, 321, 577, 74, 266, 522, 274, 530, 578, 770, 108, 140, 268, 524, 52, 148, 276, 532, 164, 292, 772, 200, 328, 648, 776, 304, 656, 224, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_307, vertices_531, vertices_579, vertices_181, vertices_721, vertices_481, vertices_790, vertices_714, vertices_778, vertices_668, vertices_236, vertices_364, vertices_780, vertices_308] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_259, vertices_515, vertices_49, vertices_145, vertices_529, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_74, vertices_266, vertices_522, vertices_274, vertices_530, vertices_578, vertices_770, vertices_108, vertices_140, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_772, vertices_200, vertices_328, vertices_648, vertices_776, vertices_304, vertices_656, vertices_224, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_307), (false, vertices_531), (false, vertices_579), (false, vertices_181), (false, vertices_721), (false, vertices_481), (true, vertices_522), (true, vertices_770), (true, vertices_108), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_772), (true, vertices_200), (true, vertices_648), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_307) then 16 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_579) then 1 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_108) then 19 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_776) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_579), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 1 3 7 8 790 274 1
cert_row_4 2 0 2 5 6 8 714 74 3
cert_row_4 3 1 2 3 6 8 668 140 2
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 274 790 1
cert_coverFacet 1 714
cert_cover_5 1 2 0 2 5 6 74 714 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 668
cert_cover_5 3 3 1 2 3 6 140 668 2
cert_coverFacet 4 236
cert_cover_5 4 0 1 2 4 6 108 236 3
cert_coverFacet 5 364
cert_cover_5 5 0 1 2 4 7 108 364 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0047

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0048.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0048

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 541, 181, 901, 217, 457, 30, 526, 118, 550, 90, 362, 930, 676, 496, 21, 133, 517, 25, 201, 265, 521, 145, 385, 769, 14, 22, 38, 518, 26, 74, 266, 522, 82, 98, 290, 546, 770, 28, 524, 52, 164, 548, 644, 88, 328, 112, 176, 208, 352, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_541, vertices_181, vertices_901, vertices_217, vertices_457, vertices_30, vertices_526, vertices_118, vertices_550, vertices_90, vertices_362, vertices_930, vertices_676, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_25, vertices_201, vertices_265, vertices_521, vertices_145, vertices_385, vertices_769, vertices_14, vertices_22, vertices_38, vertices_518, vertices_26, vertices_74, vertices_266, vertices_522, vertices_82, vertices_98, vertices_290, vertices_546, vertices_770, vertices_28, vertices_524, vertices_52, vertices_164, vertices_548, vertices_644, vertices_88, vertices_328, vertices_112, vertices_176, vertices_208, vertices_352, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_541), (false, vertices_181), (false, vertices_901), (false, vertices_217), (false, vertices_457), (true, vertices_14), (true, vertices_22), (true, vertices_38), (true, vertices_518), (true, vertices_26), (true, vertices_74), (true, vertices_82), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_548), (true, vertices_112), (true, vertices_352), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_541) then 18 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_901) then 20 else
  if p.val = (false, vertices_217) then 22 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_82) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_290) then 8 else
  if p.val = (true, vertices_546) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 14 1 22 2 38 518 26 74 82 98 290 546 548 112 352 416 672 779 541 181 901 217 457
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 5 118 22 3
cert_row_4 1 0 2 4 5 7 362 74 2
cert_row_4 2 0 4 6 7 8 930 290 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 118
cert_cover_5 2 0 0 1 3 4 22 118 3
cert_coverFacet 3 550
cert_cover_2 3 1 0 4 8 38 550 3
cert_coverFacet 4 90
cert_cover_2 4 2 0 3 5 26 90 3
cert_coverFacet 5 362
cert_cover_5 5 1 0 2 4 5 74 362 2
cert_coverFacet 6 930
cert_cover_5 6 2 0 4 6 7 290 930 2
cert_coverFacet 7 676
cert_cover_2 7 4 1 6 8 164 676 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0048

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0049.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0049

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 173, 565, 405, 625, 481, 662, 602, 362, 394, 650, 402, 620, 652, 424, 21, 37, 133, 561, 81, 273, 97, 161, 321, 385, 74, 138, 266, 522, 82, 146, 274, 530, 322, 386, 642, 44, 140, 524, 148, 532, 548, 644, 104, 168, 296, 584, 392, 648, 592, 400, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_173, vertices_565, vertices_405, vertices_625, vertices_481, vertices_662, vertices_602, vertices_362, vertices_394, vertices_650, vertices_402, vertices_620, vertices_652, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_133, vertices_561, vertices_81, vertices_273, vertices_97, vertices_161, vertices_321, vertices_385, vertices_74, vertices_138, vertices_266, vertices_522, vertices_82, vertices_146, vertices_274, vertices_530, vertices_322, vertices_386, vertices_642, vertices_44, vertices_140, vertices_524, vertices_148, vertices_532, vertices_548, vertices_644, vertices_104, vertices_168, vertices_296, vertices_584, vertices_392, vertices_648, vertices_592, vertices_400, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_173), (false, vertices_565), (false, vertices_405), (false, vertices_625), (false, vertices_481), (true, vertices_74), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_524), (true, vertices_644), (true, vertices_104), (true, vertices_296), (true, vertices_584), (true, vertices_392), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 21 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 16 else
  if p.val = (false, vertices_173) then 18 else
  if p.val = (false, vertices_565) then 22 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_648) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_4 1 0 2 3 5 8 602 74 2
cert_row_4 2 0 2 4 5 7 362 74 2
cert_row_4 3 1 2 4 5 8 620 44 3
cert_rows
cert_pivot_2 6 3 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 602
cert_cover_5 1 1 0 2 3 5 74 602 2
cert_coverFacet 2 362
cert_cover_5 2 2 0 2 4 5 74 362 2
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 44 620 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0049

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0050.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0050

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 781, 425, 713, 817, 657, 566, 214, 806, 326, 458, 418, 604, 332, 720, 137, 265, 521, 49, 145, 529, 161, 289, 641, 769, 22, 550, 70, 262, 50, 146, 162, 290, 194, 322, 386, 76, 268, 524, 84, 532, 324, 772, 200, 328, 584, 392, 560, 208, 592, 656, 416, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_781, vertices_425, vertices_713, vertices_817, vertices_657, vertices_566, vertices_214, vertices_806, vertices_326, vertices_458, vertices_418, vertices_604, vertices_332, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_529, vertices_161, vertices_289, vertices_641, vertices_769, vertices_22, vertices_550, vertices_70, vertices_262, vertices_50, vertices_146, vertices_162, vertices_290, vertices_194, vertices_322, vertices_386, vertices_76, vertices_268, vertices_524, vertices_84, vertices_532, vertices_324, vertices_772, vertices_200, vertices_328, vertices_584, vertices_392, vertices_560, vertices_208, vertices_592, vertices_656, vertices_416, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_781), (false, vertices_425), (false, vertices_713), (false, vertices_817), (false, vertices_657), (true, vertices_22), (true, vertices_550), (true, vertices_70), (true, vertices_262), (true, vertices_290), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_532), (true, vertices_324), (true, vertices_328), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_550) then 17 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 657 22 70 262 290 194 322 386 76 84 532 324 328 208 592 179 550 781 425 713 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 8 550
cert_row_4 1 0 2 5 6 7 458 194 1
cert_row_4 2 0 1 3 5 6 214 22 3
cert_row_4 3 1 2 3 5 8 604 76 2
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 22 566 3
cert_coverFacet 1 214
cert_cover_5 1 2 0 1 3 5 22 214 3
cert_coverFacet 2 806
cert_cover_5 2 0 0 1 4 7 550 806 3
cert_coverFacet 3 326
cert_cover_2 3 1 0 5 7 70 326 3
cert_coverFacet 4 458
cert_cover_5 4 1 0 2 5 6 194 458 1
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 604
cert_cover_5 6 3 1 2 3 5 76 604 2
cert_coverFacet 7 332
cert_cover_2 7 2 1 5 7 76 332 3
cert_coverFacet 8 720
cert_cover_2 8 5 3 6 8 208 720 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0050

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0051.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0051

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 453, 793, 369, 737, 897, 62, 398, 614, 710, 666, 284, 308, 356, 904, 49, 273, 529, 97, 545, 193, 321, 385, 641, 769, 14, 38, 582, 134, 26, 138, 50, 530, 546, 642, 28, 268, 52, 276, 100, 292, 196, 324, 388, 280, 536, 392, 648, 776, 304, 352, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_453, vertices_793, vertices_369, vertices_737, vertices_897, vertices_62, vertices_398, vertices_614, vertices_710, vertices_666, vertices_284, vertices_308, vertices_356, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_273, vertices_529, vertices_97, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_38, vertices_582, vertices_134, vertices_26, vertices_138, vertices_50, vertices_530, vertices_546, vertices_642, vertices_28, vertices_268, vertices_52, vertices_276, vertices_100, vertices_292, vertices_196, vertices_324, vertices_388, vertices_280, vertices_536, vertices_392, vertices_648, vertices_776, vertices_304, vertices_352, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_453), (false, vertices_793), (false, vertices_369), (false, vertices_737), (false, vertices_897), (true, vertices_14), (true, vertices_38), (true, vertices_582), (true, vertices_134), (true, vertices_26), (true, vertices_138), (true, vertices_642), (true, vertices_28), (true, vertices_268), (true, vertices_52), (true, vertices_276), (true, vertices_100), (true, vertices_292), (true, vertices_392), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_582) then 17 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_292) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_648) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 897 14 38 134 26 138 642 28 268 52 276 100 292 392 648 563 582 453 793 369 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 8 582
cert_row_4 1 0 1 2 3 4 62 14 3
cert_row_4 2 0 1 2 6 7 398 14 3
cert_row_4 3 0 2 3 6 8 666 26 3
cert_rows
cert_pivot_2 5 4 1 0
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 1 0 1 2 3 14 62 3
cert_coverFacet 1 398
cert_cover_5 1 2 0 1 2 6 14 398 3
cert_coverFacet 2 614
cert_cover_5 2 0 0 1 4 5 38 614 3
cert_coverFacet 3 710
cert_cover_5 3 0 0 1 5 6 582 710 3
cert_coverFacet 4 666
cert_cover_5 4 3 0 2 3 6 26 666 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 356
cert_cover_2 7 4 1 5 7 100 356 3
cert_coverFacet 8 904
cert_cover_2 8 6 2 7 8 392 904 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0051

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0052.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0052

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 213, 837, 121, 689, 865, 806, 390, 666, 362, 554, 394, 460, 568, 216, 69, 133, 517, 49, 81, 145, 97, 545, 833, 641, 134, 262, 518, 42, 138, 266, 522, 290, 546, 386, 642, 196, 324, 388, 772, 56, 88, 152, 536, 104, 552, 200, 328, 392, 560, 208, 656, 352, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_213, vertices_837, vertices_121, vertices_689, vertices_865, vertices_806, vertices_390, vertices_666, vertices_362, vertices_554, vertices_394, vertices_460, vertices_568, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_49, vertices_81, vertices_145, vertices_97, vertices_545, vertices_833, vertices_641, vertices_134, vertices_262, vertices_518, vertices_42, vertices_138, vertices_266, vertices_522, vertices_290, vertices_546, vertices_386, vertices_642, vertices_196, vertices_324, vertices_388, vertices_772, vertices_56, vertices_88, vertices_152, vertices_536, vertices_104, vertices_552, vertices_200, vertices_328, vertices_392, vertices_560, vertices_208, vertices_656, vertices_352, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_213), (false, vertices_837), (false, vertices_121), (false, vertices_689), (false, vertices_865), (true, vertices_262), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_388), (true, vertices_152), (true, vertices_536), (true, vertices_552), (true, vertices_200), (true, vertices_328), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 19 21 23 24 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_837) then 25 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (false, vertices_865) then 26 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 138 2
cert_row_4 1 0 1 4 7 8 806 262 2
cert_row_4 2 0 2 4 5 7 362 42 3
cert_row_4 3 1 2 5 6 7 460 196 1
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 262 806 2
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 666
cert_cover_5 2 0 0 2 3 6 138 666 2
cert_coverFacet 3 362
cert_cover_5 3 2 0 2 4 5 42 362 3
cert_coverFacet 4 554
cert_cover_2 4 2 0 4 8 42 554 3
cert_coverFacet 5 394
cert_cover_2 5 2 0 6 7 138 394 3
cert_coverFacet 6 460
cert_cover_5 6 3 1 2 5 6 196 460 1
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0052

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0053.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0053

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 333, 213, 773, 689, 849, 110, 270, 230, 774, 314, 930, 248, 344, 816, 69, 133, 261, 517, 81, 145, 529, 321, 641, 769, 14, 102, 134, 262, 518, 42, 266, 162, 290, 642, 770, 76, 268, 196, 772, 56, 88, 280, 104, 328, 176, 304, 560, 208, 336, 784, 224, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_333, vertices_213, vertices_773, vertices_689, vertices_849, vertices_110, vertices_270, vertices_230, vertices_774, vertices_314, vertices_930, vertices_248, vertices_344, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_529, vertices_321, vertices_641, vertices_769, vertices_14, vertices_102, vertices_134, vertices_262, vertices_518, vertices_42, vertices_266, vertices_162, vertices_290, vertices_642, vertices_770, vertices_76, vertices_268, vertices_196, vertices_772, vertices_56, vertices_88, vertices_280, vertices_104, vertices_328, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_784, vertices_224, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_333), (false, vertices_213), (false, vertices_773), (false, vertices_689), (false, vertices_849), (true, vertices_14), (true, vertices_102), (true, vertices_262), (true, vertices_42), (true, vertices_266), (true, vertices_162), (true, vertices_290), (true, vertices_770), (true, vertices_56), (true, vertices_88), (true, vertices_280), (true, vertices_104), (true, vertices_304), (true, vertices_224), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_102) then 17 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 5 102
cert_row_4 1 0 4 6 7 8 930 162 3
cert_row_4 2 0 2 3 4 7 314 42 2
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 230
cert_cover_5 2 0 0 1 4 6 102 230 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 314
cert_cover_5 4 2 0 2 3 4 42 314 2
cert_coverFacet 5 930
cert_cover_5 5 1 0 4 6 7 162 930 3
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 56 248 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 816
cert_cover_2 8 4 3 7 8 304 816 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0053

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0054.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0054

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 39, 659, 227, 45, 361, 713, 406, 534, 422, 812, 852, 840, 496, 720, 7, 35, 131, 515, 13, 37, 41, 73, 521, 97, 193, 641, 22, 38, 390, 518, 146, 530, 162, 44, 524, 276, 532, 292, 772, 296, 328, 584, 776, 208, 336, 592, 400, 656, 224, 352, 416, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_39, vertices_659, vertices_227, vertices_45, vertices_361, vertices_713, vertices_406, vertices_534, vertices_422, vertices_812, vertices_852, vertices_840, vertices_496, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_35, vertices_131, vertices_515, vertices_13, vertices_37, vertices_41, vertices_73, vertices_521, vertices_97, vertices_193, vertices_641, vertices_22, vertices_38, vertices_390, vertices_518, vertices_146, vertices_530, vertices_162, vertices_44, vertices_524, vertices_276, vertices_532, vertices_292, vertices_772, vertices_296, vertices_328, vertices_584, vertices_776, vertices_208, vertices_336, vertices_592, vertices_400, vertices_656, vertices_224, vertices_352, vertices_416, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_39), (false, vertices_659), (false, vertices_227), (false, vertices_45), (false, vertices_361), (false, vertices_713), (true, vertices_22), (true, vertices_390), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_772), (true, vertices_776), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_400), (true, vertices_416), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 15 else
  if p.val = (false, vertices_39) then 0 else
  if p.val = (false, vertices_659) then 18 else
  if p.val = (false, vertices_227) then 19 else
  if p.val = (false, vertices_45) then 1 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_390) then 16 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
cert_nodeAtPriority_25 1 39 0 45 22 276 532 292 772 776 208 336 592 400 416 832 527 390 659 227 361 713
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 1 3 5 7 8 852 276 2
cert_row_4 3 3 4 5 6 7 496 208 1
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 22 406 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 422
cert_cover_5 2 0 0 1 4 6 38 422 3
cert_coverFacet 3 812
cert_cover_5 3 1 1 2 4 7 44 812 3
cert_coverFacet 4 852
cert_cover_5 4 2 1 3 5 7 276 852 2
cert_coverFacet 5 840
cert_cover_2 5 5 2 7 8 328 840 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 208 496 1
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0054

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0055.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0055

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 587, 565, 185, 809, 721, 598, 454, 774, 426, 778, 308, 340, 804, 496, 75, 41, 137, 521, 49, 145, 529, 545, 193, 577, 70, 262, 518, 138, 266, 522, 194, 578, 386, 770, 52, 84, 276, 532, 292, 548, 324, 772, 168, 296, 776, 176, 304, 208, 336, 592, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_587, vertices_565, vertices_185, vertices_809, vertices_721, vertices_598, vertices_454, vertices_774, vertices_426, vertices_778, vertices_308, vertices_340, vertices_804, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_75, vertices_41, vertices_137, vertices_521, vertices_49, vertices_145, vertices_529, vertices_545, vertices_193, vertices_577, vertices_70, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_770, vertices_52, vertices_84, vertices_276, vertices_532, vertices_292, vertices_548, vertices_324, vertices_772, vertices_168, vertices_296, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_592, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_587), (false, vertices_565), (false, vertices_185), (false, vertices_809), (false, vertices_721), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_386), (true, vertices_770), (true, vertices_84), (true, vertices_276), (true, vertices_292), (true, vertices_324), (true, vertices_772), (true, vertices_304), (true, vertices_336), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_587) then 17 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
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
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 70 598 2
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 6 70 454 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 426
cert_cover_5 3 2 0 2 4 6 138 426 2
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 308
cert_cover_2 5 3 1 4 7 52 308 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 176 496 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0055

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0056.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0056

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 405, 357, 709, 793, 833, 614, 678, 602, 154, 362, 170, 428, 408, 840, 69, 133, 261, 145, 273, 529, 321, 577, 641, 769, 550, 26, 42, 74, 138, 146, 530, 98, 162, 578, 642, 100, 164, 292, 580, 388, 644, 152, 280, 536, 168, 296, 328, 584, 392, 776, 400, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_405, vertices_357, vertices_709, vertices_793, vertices_833, vertices_614, vertices_678, vertices_602, vertices_154, vertices_362, vertices_170, vertices_428, vertices_408, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_145, vertices_273, vertices_529, vertices_321, vertices_577, vertices_641, vertices_769, vertices_550, vertices_26, vertices_42, vertices_74, vertices_138, vertices_146, vertices_530, vertices_98, vertices_162, vertices_578, vertices_642, vertices_100, vertices_164, vertices_292, vertices_580, vertices_388, vertices_644, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_328, vertices_584, vertices_392, vertices_776, vertices_400, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_405), (false, vertices_357), (false, vertices_709), (false, vertices_793), (false, vertices_833), (true, vertices_550), (true, vertices_26), (true, vertices_42), (true, vertices_74), (true, vertices_138), (true, vertices_98), (true, vertices_162), (true, vertices_578), (true, vertices_164), (true, vertices_152), (true, vertices_168), (true, vertices_296), (true, vertices_328), (true, vertices_584), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_793) then 23 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_550) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
cert_nodeAtPriority_51 833 26 42 74 138 98 162 578 164 152 168 296 328 584 392 659 550 405 357 709 793
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_2 1 0 1 4 8 550
cert_row_4 2 0 2 4 5 7 362 42 3
cert_row_4 3 1 2 4 6 7 428 164 1
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 1 0 1 4 5 550 614 3
cert_coverFacet 1 678
cert_cover_5 1 1 0 1 4 6 550 678 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 5 26 602 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 362
cert_cover_5 4 2 0 2 4 5 42 362 3
cert_coverFacet 5 170
cert_cover_2 5 2 0 4 6 42 170 3
cert_coverFacet 6 428
cert_cover_5 6 3 1 2 4 6 164 428 1
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 840
cert_cover_2 8 5 2 7 8 328 840 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0056

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0057.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0057

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 661, 837, 389, 425, 329, 737, 58, 538, 842, 242, 722, 796, 436, 312, 133, 261, 517, 41, 73, 265, 97, 161, 321, 577, 385, 641, 26, 42, 74, 522, 50, 210, 530, 98, 578, 148, 276, 532, 388, 772, 56, 280, 536, 296, 328, 776, 176, 304, 656, 224, 416, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_661, vertices_837, vertices_389, vertices_425, vertices_329, vertices_737, vertices_58, vertices_538, vertices_842, vertices_242, vertices_722, vertices_796, vertices_436, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_73, vertices_265, vertices_97, vertices_161, vertices_321, vertices_577, vertices_385, vertices_641, vertices_26, vertices_42, vertices_74, vertices_522, vertices_50, vertices_210, vertices_530, vertices_98, vertices_578, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_56, vertices_280, vertices_536, vertices_296, vertices_328, vertices_776, vertices_176, vertices_304, vertices_656, vertices_224, vertices_416, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_661), (false, vertices_837), (false, vertices_389), (false, vertices_425), (false, vertices_329), (false, vertices_737), (true, vertices_26), (true, vertices_522), (true, vertices_50), (true, vertices_210), (true, vertices_530), (true, vertices_578), (true, vertices_276), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_776), (true, vertices_176), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 15 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_210) then 16 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  0
cert_priority
cert_nodeAtPriority_53 0 389 1 329 26 522 50 530 578 276 56 280 536 776 176 304 107 210 661 837 425 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 6 7 436 148 2
cert_row_2 1 0 3 5 6 210
cert_row_4 2 0 2 5 7 8 842 74 3
cert_row_4 3 1 2 3 7 8 796 276 1
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 58
cert_cover_2 0 2 0 3 4 26 58 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 842
cert_cover_5 2 2 0 2 5 7 74 842 3
cert_coverFacet 3 242
cert_cover_5 3 1 0 3 4 5 50 242 3
cert_coverFacet 4 722
cert_cover_5 4 1 0 3 5 8 210 722 3
cert_coverFacet 5 796
cert_cover_5 5 3 1 2 3 7 276 796 1
cert_coverFacet 6 436
cert_cover_5 6 0 1 3 4 6 148 436 2
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0057

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0058.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0058

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 781, 661, 453, 553, 329, 737, 406, 58, 282, 458, 626, 722, 788, 824, 133, 261, 517, 41, 73, 265, 521, 97, 545, 193, 321, 641, 26, 42, 74, 266, 50, 594, 146, 274, 98, 194, 386, 148, 276, 532, 388, 772, 56, 280, 552, 328, 776, 560, 656, 784, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_781, vertices_661, vertices_453, vertices_553, vertices_329, vertices_737, vertices_406, vertices_58, vertices_282, vertices_458, vertices_626, vertices_722, vertices_788, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_73, vertices_265, vertices_521, vertices_97, vertices_545, vertices_193, vertices_321, vertices_641, vertices_26, vertices_42, vertices_74, vertices_266, vertices_50, vertices_594, vertices_146, vertices_274, vertices_98, vertices_194, vertices_386, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_56, vertices_280, vertices_552, vertices_328, vertices_776, vertices_560, vertices_656, vertices_784, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_781), (false, vertices_661), (false, vertices_453), (false, vertices_553), (false, vertices_329), (false, vertices_737), (true, vertices_26), (true, vertices_266), (true, vertices_50), (true, vertices_594), (true, vertices_146), (true, vertices_274), (true, vertices_194), (true, vertices_386), (true, vertices_276), (true, vertices_56), (true, vertices_280), (true, vertices_560), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 15 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_594) then 16 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_784) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_594), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_4 0 0 1 3 6 7 406 146 1
cert_row_4 1 0 2 5 6 7 458 74 3
cert_row_2 2 0 3 5 8 594
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 146 406 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 458
cert_cover_5 3 1 0 2 5 6 74 458 3
cert_coverFacet 4 626
cert_cover_5 4 2 0 3 4 5 50 626 3
cert_coverFacet 5 722
cert_cover_5 5 2 0 3 5 6 594 722 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 824
cert_cover_5 7 3 2 3 4 7 56 824 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0058

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2643 : Certifies 2643 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0029.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2644 : Certifies 2644 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0030.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2645 : Certifies 2645 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0031.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2646 : Certifies 2646 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0032.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2647 : Certifies 2647 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0033.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2648 : Certifies 2648 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0034.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2649 : Certifies 2649 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0035.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2650 : Certifies 2650 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0036.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2651 : Certifies 2651 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0037.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2652 : Certifies 2652 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0038.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2653 : Certifies 2653 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0039.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2654 : Certifies 2654 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0040.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2655 : Certifies 2655 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0041.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2656 : Certifies 2656 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0042.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2657 : Certifies 2657 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0043.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2658 : Certifies 2658 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0044.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2659 : Certifies 2659 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0045.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2660 : Certifies 2660 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0046.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2661 : Certifies 2661 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0047.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2662 : Certifies 2662 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0048.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2663 : Certifies 2663 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0049.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2664 : Certifies 2664 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0050.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2665 : Certifies 2665 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0051.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2666 : Certifies 2666 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0052.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2667 : Certifies 2667 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0053.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2668 : Certifies 2668 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0054.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2669 : Certifies 2669 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0055.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2670 : Certifies 2670 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0056.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2671 : Certifies 2671 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0057.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2672 : Certifies 2672 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0058.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B087 (j : Fin 30) :
    Certifies (2643 + j.val) := by
  fin_cases j
  · exact projection_2643
  · exact projection_2644
  · exact projection_2645
  · exact projection_2646
  · exact projection_2647
  · exact projection_2648
  · exact projection_2649
  · exact projection_2650
  · exact projection_2651
  · exact projection_2652
  · exact projection_2653
  · exact projection_2654
  · exact projection_2655
  · exact projection_2656
  · exact projection_2657
  · exact projection_2658
  · exact projection_2659
  · exact projection_2660
  · exact projection_2661
  · exact projection_2662
  · exact projection_2663
  · exact projection_2664
  · exact projection_2665
  · exact projection_2666
  · exact projection_2667
  · exact projection_2668
  · exact projection_2669
  · exact projection_2670
  · exact projection_2671
  · exact projection_2672

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
