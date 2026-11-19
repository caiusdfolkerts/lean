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
/- Source: ProjectionCertificates/R_m15e10q1_0554.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0554

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 589, 789, 229, 421, 457, 310, 394, 650, 242, 658, 786, 418, 628, 728, 165, 69, 261, 517, 73, 265, 521, 193, 385, 769, 138, 266, 522, 50, 146, 274, 530, 162, 290, 386, 642, 770, 52, 276, 532, 100, 292, 580, 200, 584, 392, 648, 112, 208, 592, 656, 784, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_589, vertices_789, vertices_229, vertices_421, vertices_457, vertices_310, vertices_394, vertices_650, vertices_242, vertices_658, vertices_786, vertices_418, vertices_628, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_165, vertices_69, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_193, vertices_385, vertices_769, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_52, vertices_276, vertices_532, vertices_100, vertices_292, vertices_580, vertices_200, vertices_584, vertices_392, vertices_648, vertices_112, vertices_208, vertices_592, vertices_656, vertices_784, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_589), (false, vertices_789), (false, vertices_229), (false, vertices_421), (false, vertices_457), (true, vertices_138), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_642), (true, vertices_52), (true, vertices_648), (true, vertices_112), (true, vertices_208), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_421) then 23 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
cert_nodeAtPriority_42 138 1 50 2 146 274 530 162 290 386 642 52 648 112 208 592 656 779 589 457 789 229 421
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 50 1
cert_row_4 1 0 3 4 5 6 242 50 3
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 2 3 5 6 8 728 200 1
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 50 310 1
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 242
cert_cover_5 3 1 0 3 4 5 50 242 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 418
cert_cover_2 6 4 0 6 7 162 418 3
cert_coverFacet 7 628
cert_cover_5 7 2 1 3 4 5 52 628 3
cert_coverFacet 8 728
cert_cover_5 8 3 2 3 5 6 200 728 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0554

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0555.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0555

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 109, 301, 213, 789, 457, 806, 666, 618, 298, 394, 786, 628, 712, 720, 45, 21, 69, 261, 73, 265, 145, 273, 193, 385, 42, 138, 266, 522, 146, 274, 530, 290, 546, 386, 770, 84, 532, 100, 292, 548, 772, 104, 296, 200, 584, 392, 648, 208, 592, 656, 784, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_109, vertices_301, vertices_213, vertices_789, vertices_457, vertices_806, vertices_666, vertices_618, vertices_298, vertices_394, vertices_786, vertices_628, vertices_712, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_45, vertices_21, vertices_69, vertices_261, vertices_73, vertices_265, vertices_145, vertices_273, vertices_193, vertices_385, vertices_42, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_770, vertices_84, vertices_532, vertices_100, vertices_292, vertices_548, vertices_772, vertices_104, vertices_296, vertices_200, vertices_584, vertices_392, vertices_648, vertices_208, vertices_592, vertices_656, vertices_784, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_109), (false, vertices_301), (false, vertices_213), (false, vertices_789), (false, vertices_457), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_548), (true, vertices_584), (true, vertices_648), (true, vertices_592), (true, vertices_656), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 21 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_301) then 19 else
  if p.val = (false, vertices_213) then 22 else
  if p.val = (false, vertices_789) then 23 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 42 2 138 1 266 522 530 290 546 770 548 584 648 592 656 608 704 403 109 301 457 213 789
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_4 1 0 2 3 6 8 666 138 2
cert_row_4 2 0 2 4 5 8 618 42 3
cert_row_4 3 1 3 4 5 8 628 84 2
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 666
cert_cover_5 1 1 0 2 3 6 138 666 2
cert_coverFacet 2 618
cert_cover_5 2 2 0 2 4 5 42 618 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 628
cert_cover_5 6 3 1 3 4 5 84 628 2
cert_coverFacet 7 712
cert_cover_2 7 5 2 6 8 200 712 3
cert_coverFacet 8 720
cert_cover_2 8 5 3 6 8 208 720 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0555

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0556.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0556

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 341, 773, 457, 721, 929, 30, 46, 806, 122, 626, 284, 428, 344, 744, 21, 261, 517, 81, 529, 193, 321, 385, 641, 769, 14, 22, 38, 518, 26, 42, 114, 530, 546, 28, 44, 268, 276, 292, 772, 88, 280, 104, 168, 200, 328, 392, 336, 592, 608, 416, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_341, vertices_773, vertices_457, vertices_721, vertices_929, vertices_30, vertices_46, vertices_806, vertices_122, vertices_626, vertices_284, vertices_428, vertices_344, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_261, vertices_517, vertices_81, vertices_529, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_38, vertices_518, vertices_26, vertices_42, vertices_114, vertices_530, vertices_546, vertices_28, vertices_44, vertices_268, vertices_276, vertices_292, vertices_772, vertices_88, vertices_280, vertices_104, vertices_168, vertices_200, vertices_328, vertices_392, vertices_336, vertices_592, vertices_608, vertices_416, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_341), (false, vertices_773), (false, vertices_457), (false, vertices_721), (false, vertices_929), (true, vertices_14), (true, vertices_38), (true, vertices_26), (true, vertices_42), (true, vertices_114), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_292), (true, vertices_88), (true, vertices_280), (true, vertices_104), (true, vertices_168), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 16 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_114) then 17 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 773 14 38 26 42 546 28 44 268 292 88 280 104 168 608 535 114 341 457 721 929
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 5 114
cert_row_4 1 0 1 4 7 8 806 38 3
cert_row_4 2 1 2 4 6 7 428 44 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 46
cert_cover_2 1 1 0 2 4 14 46 3
cert_coverFacet 2 806
cert_cover_5 2 1 0 1 4 7 38 806 3
cert_coverFacet 3 122
cert_cover_5 3 0 0 2 3 4 26 122 3
cert_coverFacet 4 626
cert_cover_5 4 0 0 3 4 8 114 626 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 428
cert_cover_5 6 2 1 2 4 6 44 428 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 744
cert_cover_5 8 3 2 4 5 6 104 744 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0556

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0557.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0557

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 341, 613, 389, 645, 409, 241, 654, 314, 154, 810, 178, 844, 396, 880, 69, 133, 261, 517, 81, 145, 273, 97, 161, 545, 385, 641, 26, 298, 138, 522, 50, 146, 162, 546, 642, 140, 268, 524, 324, 580, 388, 644, 152, 280, 392, 776, 112, 176, 304, 336, 608, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_341, vertices_613, vertices_389, vertices_645, vertices_409, vertices_241, vertices_654, vertices_314, vertices_154, vertices_810, vertices_178, vertices_844, vertices_396, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_273, vertices_97, vertices_161, vertices_545, vertices_385, vertices_641, vertices_26, vertices_298, vertices_138, vertices_522, vertices_50, vertices_146, vertices_162, vertices_546, vertices_642, vertices_140, vertices_268, vertices_524, vertices_324, vertices_580, vertices_388, vertices_644, vertices_152, vertices_280, vertices_392, vertices_776, vertices_112, vertices_176, vertices_304, vertices_336, vertices_608, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_341), (false, vertices_613), (false, vertices_389), (false, vertices_645), (false, vertices_409), (false, vertices_241), (true, vertices_26), (true, vertices_298), (true, vertices_138), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_776), (true, vertices_304), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_645) then 1 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_298) then 16 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 389 1 645 26 138 522 50 146 140 268 524 776 304 800 832 675 298 341 613 409 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_2 1 0 2 4 7 298
cert_row_4 2 1 2 5 7 8 844 268 2
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 6 0 1 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 314
cert_cover_5 1 1 0 2 3 4 26 314 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 810
cert_cover_5 3 1 0 2 4 8 298 810 3
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 844
cert_cover_5 5 2 1 2 5 7 268 844 2
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 880
cert_cover_5 7 3 3 4 5 7 112 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0557

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0558.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0558

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 597, 793, 681, 369, 737, 782, 710, 390, 170, 650, 434, 244, 404, 788, 41, 265, 521, 81, 273, 529, 97, 673, 289, 577, 134, 262, 518, 42, 138, 266, 522, 162, 290, 386, 642, 84, 148, 276, 532, 196, 580, 388, 772, 168, 648, 776, 112, 176, 304, 400, 784, 224, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_597, vertices_793, vertices_681, vertices_369, vertices_737, vertices_782, vertices_710, vertices_390, vertices_170, vertices_650, vertices_434, vertices_244, vertices_404, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_265, vertices_521, vertices_81, vertices_273, vertices_529, vertices_97, vertices_673, vertices_289, vertices_577, vertices_134, vertices_262, vertices_518, vertices_42, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_386, vertices_642, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_580, vertices_388, vertices_772, vertices_168, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_400, vertices_784, vertices_224, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_597), (false, vertices_793), (false, vertices_681), (false, vertices_369), (false, vertices_737), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_522), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_276), (true, vertices_196), (true, vertices_388), (true, vertices_772), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 19 21 23 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_681) then 24 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 262 2
cert_row_4 1 0 1 5 6 8 710 134 2
cert_row_4 2 0 3 4 6 7 434 162 1
cert_row_4 3 1 3 4 5 6 244 84 2
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 262 782 2
cert_coverFacet 1 710
cert_cover_5 1 1 0 1 5 6 134 710 2
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 170
cert_cover_2 3 2 0 4 6 42 170 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 434
cert_cover_5 5 2 0 3 4 6 162 434 1
cert_coverFacet 6 244
cert_cover_5 6 3 1 3 4 5 84 244 2
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 788
cert_cover_2 8 3 1 7 8 276 788 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0558

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0559.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0559

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 333, 653, 613, 409, 833, 118, 570, 666, 466, 866, 60, 284, 556, 340, 13, 69, 517, 137, 265, 321, 577, 385, 641, 769, 538, 50, 82, 146, 98, 546, 322, 386, 642, 770, 28, 44, 268, 524, 52, 84, 276, 100, 548, 324, 56, 152, 280, 552, 648, 336, 400, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_333, vertices_653, vertices_613, vertices_409, vertices_833, vertices_118, vertices_570, vertices_666, vertices_466, vertices_866, vertices_60, vertices_284, vertices_556, vertices_340] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_137, vertices_265, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_538, vertices_50, vertices_82, vertices_146, vertices_98, vertices_546, vertices_322, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_100, vertices_548, vertices_324, vertices_56, vertices_152, vertices_280, vertices_552, vertices_648, vertices_336, vertices_400, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_333), (false, vertices_653), (false, vertices_613), (false, vertices_409), (false, vertices_833), (true, vertices_538), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_98), (true, vertices_546), (true, vertices_322), (true, vertices_28), (true, vertices_44), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_56), (true, vertices_552), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_653) then 20 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_409) then 23 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_538) then 17 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_336) then 14 else
  0
cert_priority
cert_nodeAtPriority_51 833 50 82 146 98 546 322 28 44 52 84 276 56 552 336 899 538 333 653 613 409
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 8 538
cert_row_4 1 0 1 3 4 5 118 50 1
cert_row_4 2 0 3 5 6 7 466 82 3
cert_row_4 3 0 4 5 7 8 866 98 3
cert_rows
cert_pivot_2 2 1 3 0
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 1 0 1 3 4 50 118 1
cert_coverFacet 1 570
cert_cover_5 1 0 0 2 3 4 538 570 3
cert_coverFacet 2 666
cert_cover_5 2 0 0 2 3 6 538 666 3
cert_coverFacet 3 466
cert_cover_5 3 2 0 3 5 6 82 466 3
cert_coverFacet 4 866
cert_cover_5 4 3 0 4 5 7 98 866 3
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 556
cert_cover_2 7 2 1 4 8 44 556 3
cert_coverFacet 8 340
cert_cover_2 8 3 1 5 7 84 340 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0559

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0560.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0560

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 563, 339, 361, 809, 241, 398, 646, 402, 658, 236, 556, 780, 692, 472, 19, 259, 515, 297, 49, 81, 97, 545, 321, 769, 134, 262, 518, 146, 274, 530, 386, 642, 44, 140, 268, 524, 164, 548, 644, 772, 104, 552, 200, 328, 392, 776, 176, 560, 208, 336, 400, 656, 224]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_563, vertices_339, vertices_361, vertices_809, vertices_241, vertices_398, vertices_646, vertices_402, vertices_658, vertices_236, vertices_556, vertices_780, vertices_692, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_259, vertices_515, vertices_297, vertices_49, vertices_81, vertices_97, vertices_545, vertices_321, vertices_769, vertices_134, vertices_262, vertices_518, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_44, vertices_140, vertices_268, vertices_524, vertices_164, vertices_548, vertices_644, vertices_772, vertices_104, vertices_552, vertices_200, vertices_328, vertices_392, vertices_776, vertices_176, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_224] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_563), (false, vertices_339), (false, vertices_361), (false, vertices_809), (false, vertices_241), (true, vertices_134), (true, vertices_146), (true, vertices_386), (true, vertices_642), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_164), (true, vertices_548), (true, vertices_644), (true, vertices_200), (true, vertices_392), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_563) then 17 else
  if p.val = (false, vertices_339) then 18 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_4 1 1 3 4 6 8 692 164 1
cert_row_4 2 1 2 4 5 6 236 44 3
cert_row_4 3 2 3 5 6 7 472 200 1
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 236
cert_cover_5 4 2 1 2 4 5 44 236 3
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 692
cert_cover_5 7 1 1 3 4 6 164 692 1
cert_coverFacet 8 472
cert_cover_5 8 3 2 3 5 6 200 472 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0560

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0561.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0561

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 659, 653, 405, 837, 369, 558, 122, 154, 650, 866, 428, 804, 312, 408, 531, 133, 261, 517, 81, 145, 273, 321, 577, 641, 26, 42, 138, 522, 82, 146, 98, 546, 578, 642, 44, 140, 524, 292, 548, 388, 772, 56, 152, 280, 296, 392, 648, 112, 304, 400, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_659, vertices_653, vertices_405, vertices_837, vertices_369, vertices_558, vertices_122, vertices_154, vertices_650, vertices_866, vertices_428, vertices_804, vertices_312, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_531, vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_273, vertices_321, vertices_577, vertices_641, vertices_26, vertices_42, vertices_138, vertices_522, vertices_82, vertices_146, vertices_98, vertices_546, vertices_578, vertices_642, vertices_44, vertices_140, vertices_524, vertices_292, vertices_548, vertices_388, vertices_772, vertices_56, vertices_152, vertices_280, vertices_296, vertices_392, vertices_648, vertices_112, vertices_304, vertices_400, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_659), (false, vertices_653), (false, vertices_405), (false, vertices_837), (false, vertices_369), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_98), (true, vertices_546), (true, vertices_44), (true, vertices_292), (true, vertices_548), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_392), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 16 else
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 5 122 26 3
cert_row_4 1 0 4 5 7 8 866 98 3
cert_row_4 2 0 1 2 4 8 558 42 1
cert_row_4 3 1 2 4 6 7 428 44 3
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 2 0 1 2 4 42 558 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 4 26 122 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 866
cert_cover_5 4 1 0 4 5 7 98 866 3
cert_coverFacet 5 428
cert_cover_5 5 3 1 2 4 6 44 428 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0561

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0562.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0562

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 563, 355, 345, 601, 433, 654, 198, 226, 674, 412, 332, 588, 484, 696, 35, 67, 515, 89, 49, 273, 529, 289, 321, 577, 70, 134, 518, 98, 162, 546, 194, 642, 76, 140, 268, 524, 196, 324, 580, 388, 152, 280, 536, 328, 584, 648, 176, 560, 400, 224, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_563, vertices_355, vertices_345, vertices_601, vertices_433, vertices_654, vertices_198, vertices_226, vertices_674, vertices_412, vertices_332, vertices_588, vertices_484, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_515, vertices_89, vertices_49, vertices_273, vertices_529, vertices_289, vertices_321, vertices_577, vertices_70, vertices_134, vertices_518, vertices_98, vertices_162, vertices_546, vertices_194, vertices_642, vertices_76, vertices_140, vertices_268, vertices_524, vertices_196, vertices_324, vertices_580, vertices_388, vertices_152, vertices_280, vertices_536, vertices_328, vertices_584, vertices_648, vertices_176, vertices_560, vertices_400, vertices_224, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_563), (false, vertices_355), (false, vertices_345), (false, vertices_601), (false, vertices_433), (true, vertices_134), (true, vertices_162), (true, vertices_194), (true, vertices_642), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_152), (true, vertices_648), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 16 else
  if p.val = (false, vertices_563) then 17 else
  if p.val = (false, vertices_355) then 18 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_601) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 134 2
cert_row_4 1 1 4 5 6 7 484 196 1
cert_row_4 2 1 2 3 6 7 412 140 2
cert_row_4 3 2 3 4 6 8 696 152 2
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 134 654 2
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 226
cert_cover_2 2 4 0 5 6 98 226 3
cert_coverFacet 3 674
cert_cover_2 3 4 0 6 8 162 674 3
cert_coverFacet 4 412
cert_cover_5 4 2 1 2 3 6 140 412 2
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 588
cert_cover_2 6 2 1 5 8 76 588 3
cert_coverFacet 7 484
cert_cover_5 7 1 1 4 5 6 196 484 1
cert_coverFacet 8 696
cert_cover_5 8 3 2 3 4 6 152 696 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0562

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0563.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0563

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 781, 565, 421, 369, 833, 174, 558, 218, 842, 178, 562, 460, 432, 464, 37, 261, 517, 49, 81, 529, 289, 321, 577, 769, 46, 74, 138, 522, 50, 82, 146, 530, 162, 546, 578, 140, 268, 524, 164, 548, 388, 200, 328, 776, 176, 304, 560, 208, 336, 400, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_781, vertices_565, vertices_421, vertices_369, vertices_833, vertices_174, vertices_558, vertices_218, vertices_842, vertices_178, vertices_562, vertices_460, vertices_432, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_49, vertices_81, vertices_529, vertices_289, vertices_321, vertices_577, vertices_769, vertices_46, vertices_74, vertices_138, vertices_522, vertices_50, vertices_82, vertices_146, vertices_530, vertices_162, vertices_546, vertices_578, vertices_140, vertices_268, vertices_524, vertices_164, vertices_548, vertices_388, vertices_200, vertices_328, vertices_776, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_400, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_781), (false, vertices_565), (false, vertices_421), (false, vertices_369), (false, vertices_833), (true, vertices_46), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_162), (true, vertices_546), (true, vertices_140), (true, vertices_200), (true, vertices_328), (true, vertices_176), (true, vertices_208), (true, vertices_400), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_565) then 20 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_46) then 17 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_19 0 833 1 74 138 522 50 146 162 546 140 200 328 176 208 400 448 595 46 781 565 421 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 2 3 5 6 218 74 2
cert_row_4 2 0 2 5 7 8 842 74 3
cert_row_4 3 1 2 5 6 7 460 140 2
cert_rows
cert_pivot_2 4 3 0 1
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 0 0 1 2 6 46 174 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 8 46 558 3
cert_coverFacet 2 218
cert_cover_5 2 1 0 2 3 5 74 218 2
cert_coverFacet 3 842
cert_cover_5 3 2 0 2 5 7 74 842 3
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 562
cert_cover_2 5 3 0 4 8 50 562 3
cert_coverFacet 6 460
cert_cover_5 6 3 1 2 5 6 140 460 2
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0563

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0564.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0564

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [227, 789, 601, 433, 209, 865, 206, 270, 406, 618, 298, 418, 220, 540, 812, 81, 145, 273, 529, 97, 161, 289, 193, 577, 769, 14, 134, 262, 42, 74, 266, 98, 162, 290, 194, 386, 28, 204, 268, 524, 148, 276, 532, 772, 88, 536, 296, 552, 584, 208, 400, 608, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_789, vertices_601, vertices_433, vertices_209, vertices_865, vertices_206, vertices_270, vertices_406, vertices_618, vertices_298, vertices_418, vertices_220, vertices_540, vertices_812] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_193, vertices_577, vertices_769, vertices_14, vertices_134, vertices_262, vertices_42, vertices_74, vertices_266, vertices_98, vertices_162, vertices_290, vertices_194, vertices_386, vertices_28, vertices_204, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_772, vertices_88, vertices_536, vertices_296, vertices_552, vertices_584, vertices_208, vertices_400, vertices_608, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_789), (false, vertices_601), (false, vertices_433), (false, vertices_209), (false, vertices_865), (true, vertices_14), (true, vertices_134), (true, vertices_262), (true, vertices_42), (true, vertices_74), (true, vertices_266), (true, vertices_290), (true, vertices_386), (true, vertices_28), (true, vertices_204), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_296), (true, vertices_552)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 16 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_209) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_204) then 19 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_148) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_552) then 14 else
  0
cert_priority
cert_nodeAtPriority_9 0 209 1 14 134 262 42 74 266 290 386 28 268 524 148 296 552 227 789 204 601 433 865
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 7 406 134 2
cert_row_2 1 1 2 5 6 204
cert_row_4 2 0 2 4 5 8 618 42 3
cert_row_4 3 1 2 4 7 8 812 268 2
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 406
cert_cover_5 2 0 0 1 3 6 134 406 2
cert_coverFacet 3 618
cert_cover_5 3 2 0 2 4 5 42 618 3
cert_coverFacet 4 298
cert_cover_2 4 2 0 4 7 42 298 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 220
cert_cover_5 6 1 1 2 3 5 28 220 3
cert_coverFacet 7 540
cert_cover_2 7 2 1 3 8 28 540 3
cert_coverFacet 8 812
cert_cover_5 8 3 1 2 4 7 268 812 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0564

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0565.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0565

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [227, 837, 185, 817, 465, 609, 286, 590, 454, 618, 170, 394, 572, 788, 408, 49, 145, 273, 97, 161, 545, 193, 321, 577, 769, 14, 70, 262, 42, 586, 138, 266, 98, 162, 194, 386, 28, 524, 276, 532, 324, 580, 772, 56, 152, 280, 168, 552, 392, 560, 400, 784, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_837, vertices_185, vertices_817, vertices_465, vertices_609, vertices_286, vertices_590, vertices_454, vertices_618, vertices_170, vertices_394, vertices_572, vertices_788, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_273, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_769, vertices_14, vertices_70, vertices_262, vertices_42, vertices_586, vertices_138, vertices_266, vertices_98, vertices_162, vertices_194, vertices_386, vertices_28, vertices_524, vertices_276, vertices_532, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_552, vertices_392, vertices_560, vertices_400, vertices_784, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_837), (false, vertices_185), (false, vertices_817), (false, vertices_465), (false, vertices_609), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_42), (true, vertices_586), (true, vertices_138), (true, vertices_266), (true, vertices_386), (true, vertices_28), (true, vertices_524), (true, vertices_276), (true, vertices_532), (true, vertices_280), (true, vertices_552), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 16 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (false, vertices_609) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_586) then 17 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
cert_nodeAtPriority_40 609 14 70 262 42 138 266 386 28 524 276 532 280 552 392 227 586 837 185 817 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_2 1 0 2 5 8 586
cert_row_4 2 0 1 2 3 7 286 14 3
cert_row_4 3 1 2 3 4 8 572 28 3
cert_rows
cert_pivot_2 6 5 0 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 2 0 1 2 3 14 286 3
cert_coverFacet 1 590
cert_cover_5 1 1 0 1 2 5 14 590 3
cert_coverFacet 2 454
cert_cover_5 2 0 0 1 5 6 70 454 3
cert_coverFacet 3 618
cert_cover_5 3 1 0 2 4 5 42 618 3
cert_coverFacet 4 170
cert_cover_2 4 2 0 4 6 42 170 3
cert_coverFacet 5 394
cert_cover_2 5 2 0 6 7 138 394 3
cert_coverFacet 6 572
cert_cover_5 6 3 1 2 3 4 28 572 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0565

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0566.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0566

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 653, 269, 789, 233, 329, 721, 558, 358, 774, 242, 562, 786, 364, 696, 13, 261, 517, 73, 137, 265, 81, 273, 529, 193, 321, 641, 38, 262, 518, 50, 82, 274, 530, 98, 546, 322, 770, 44, 268, 524, 356, 772, 104, 168, 552, 328, 648, 176, 560, 208, 656, 784, 224]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_653, vertices_269, vertices_789, vertices_233, vertices_329, vertices_721, vertices_558, vertices_358, vertices_774, vertices_242, vertices_562, vertices_786, vertices_364, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_81, vertices_273, vertices_529, vertices_193, vertices_321, vertices_641, vertices_38, vertices_262, vertices_518, vertices_50, vertices_82, vertices_274, vertices_530, vertices_98, vertices_546, vertices_322, vertices_770, vertices_44, vertices_268, vertices_524, vertices_356, vertices_772, vertices_104, vertices_168, vertices_552, vertices_328, vertices_648, vertices_176, vertices_560, vertices_208, vertices_656, vertices_784, vertices_224] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_653), (false, vertices_269), (false, vertices_789), (false, vertices_233), (false, vertices_329), (false, vertices_721), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_530), (true, vertices_98), (true, vertices_546), (true, vertices_770), (true, vertices_44), (true, vertices_356), (true, vertices_552), (true, vertices_176), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 15 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_44) then 10 else
  if p.val = (true, vertices_356) then 19 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_560) then 13 else
  0
cert_priority
cert_nodeAtPriority_54 269 329 38 262 518 50 530 98 546 770 44 552 176 560 339 653 789 356 233 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 7 356
cert_row_4 1 0 1 2 4 8 558 38 2
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 2 3 4 6 8 696 168 1
cert_rows
cert_pivot_2 7 1 0 2
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 38 558 2
cert_coverFacet 1 358
cert_cover_5 1 0 0 1 4 5 38 358 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 50 242 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 364
cert_cover_5 6 0 1 2 4 5 44 364 3
cert_coverFacet 7 696
cert_cover_5 7 3 2 3 4 6 168 696 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0566

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0567.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0567

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 179, 643, 309, 533, 837, 929, 590, 218, 962, 60, 540, 108, 484, 248, 19, 131, 515, 21, 261, 517, 49, 529, 161, 289, 641, 769, 26, 74, 522, 146, 194, 578, 642, 28, 44, 76, 524, 52, 532, 100, 292, 324, 580, 56, 216, 536, 104, 176, 224, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_179, vertices_643, vertices_309, vertices_533, vertices_837, vertices_929, vertices_590, vertices_218, vertices_962, vertices_60, vertices_540, vertices_108, vertices_484, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_515, vertices_21, vertices_261, vertices_517, vertices_49, vertices_529, vertices_161, vertices_289, vertices_641, vertices_769, vertices_26, vertices_74, vertices_522, vertices_146, vertices_194, vertices_578, vertices_642, vertices_28, vertices_44, vertices_76, vertices_524, vertices_52, vertices_532, vertices_100, vertices_292, vertices_324, vertices_580, vertices_56, vertices_216, vertices_536, vertices_104, vertices_176, vertices_224, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_179), (false, vertices_643), (false, vertices_309), (false, vertices_533), (false, vertices_837), (false, vertices_929), (true, vertices_74), (true, vertices_194), (true, vertices_578), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_524), (true, vertices_100), (true, vertices_56), (true, vertices_216), (true, vertices_104), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 15 else
  if p.val = (false, vertices_179) then 16 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_309) then 18 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_929) then 24 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_216) then 21 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
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
cert_row_2 0 2 3 5 6 216
cert_row_4 1 0 1 2 5 8 590 74 1
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 74 590 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 5 26 218 3
cert_coverFacet 2 962
cert_cover_5 2 2 0 5 6 7 194 962 3
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 100 484 3
cert_coverFacet 7 248
cert_cover_5 7 0 2 3 4 5 56 248 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0567

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0568.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0568

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 75, 611, 405, 281, 457, 721, 302, 558, 330, 482, 796, 660, 740, 420, 11, 67, 515, 25, 73, 265, 145, 273, 529, 193, 577, 385, 46, 74, 266, 522, 98, 290, 546, 322, 268, 524, 148, 276, 532, 164, 292, 548, 388, 644, 280, 536, 328, 656, 224, 608, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_75, vertices_611, vertices_405, vertices_281, vertices_457, vertices_721, vertices_302, vertices_558, vertices_330, vertices_482, vertices_796, vertices_660, vertices_740, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_515, vertices_25, vertices_73, vertices_265, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_46, vertices_74, vertices_266, vertices_522, vertices_98, vertices_290, vertices_546, vertices_322, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_280, vertices_536, vertices_328, vertices_656, vertices_224, vertices_608, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_75), (false, vertices_611), (false, vertices_405), (false, vertices_281), (false, vertices_457), (false, vertices_721), (true, vertices_46), (true, vertices_266), (true, vertices_290), (true, vertices_322), (true, vertices_268), (true, vertices_524), (true, vertices_532), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_644), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 15 else
  if p.val = (false, vertices_75) then 0 else
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_46) then 17 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
cert_nodeAtPriority_23 75 281 266 290 322 268 524 532 164 292 548 644 224 416 539 611 46 405 457 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 7 8 796 268 2
cert_row_2 1 0 1 2 4 46
cert_row_4 2 0 4 5 6 7 482 98 3
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 1 0 1 2 7 46 302 3
cert_coverFacet 1 558
cert_cover_5 1 1 0 1 2 8 46 558 3
cert_coverFacet 2 330
cert_cover_2 2 2 0 5 7 74 330 3
cert_coverFacet 3 482
cert_cover_5 3 2 0 4 5 6 98 482 3
cert_coverFacet 4 796
cert_cover_5 4 0 1 2 3 7 268 796 2
cert_coverFacet 5 660
cert_cover_2 5 3 1 6 8 148 660 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 164 740 2
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0568

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0570.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0570

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 397, 613, 165, 325, 665, 841, 118, 182, 794, 338, 658, 866, 468, 408, 37, 69, 133, 261, 137, 265, 521, 161, 545, 321, 577, 641, 54, 82, 146, 274, 530, 98, 162, 546, 322, 642, 770, 84, 148, 100, 164, 324, 388, 152, 280, 536, 392, 776, 336, 400, 656, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_397, vertices_613, vertices_165, vertices_325, vertices_665, vertices_841, vertices_118, vertices_182, vertices_794, vertices_338, vertices_658, vertices_866, vertices_468, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_133, vertices_261, vertices_137, vertices_265, vertices_521, vertices_161, vertices_545, vertices_321, vertices_577, vertices_641, vertices_54, vertices_82, vertices_146, vertices_274, vertices_530, vertices_98, vertices_162, vertices_546, vertices_322, vertices_642, vertices_770, vertices_84, vertices_148, vertices_100, vertices_164, vertices_324, vertices_388, vertices_152, vertices_280, vertices_536, vertices_392, vertices_776, vertices_336, vertices_400, vertices_656, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_397), (false, vertices_613), (false, vertices_165), (false, vertices_325), (false, vertices_665), (false, vertices_841), (true, vertices_54), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_322), (true, vertices_770), (true, vertices_84), (true, vertices_148), (true, vertices_280), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_325) then 1 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (true, vertices_54) then 16 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
cert_nodeAtPriority_25 0 165 1 325 82 146 274 530 98 322 770 84 148 280 336 400 675 54 397 613 665 841
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 7 8 794 274 1
cert_row_4 1 0 4 5 7 8 866 98 3
cert_row_2 2 0 1 3 4 54
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 2 0 1 3 5 54 118 3
cert_coverFacet 1 182
cert_cover_5 1 2 0 1 3 6 54 182 3
cert_coverFacet 2 794
cert_cover_5 2 0 0 2 3 7 274 794 1
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 866
cert_cover_5 5 1 0 4 5 7 98 866 3
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 84 468 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0570

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0571.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0571

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 779, 659, 163, 421, 601, 409, 614, 774, 674, 844, 468, 228, 344, 752, 35, 131, 259, 515, 293, 25, 265, 521, 145, 529, 161, 385, 38, 262, 518, 162, 546, 642, 770, 100, 164, 196, 324, 580, 388, 772, 88, 280, 328, 584, 776, 208, 336, 592, 400, 656, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_779, vertices_659, vertices_163, vertices_421, vertices_601, vertices_409, vertices_614, vertices_774, vertices_674, vertices_844, vertices_468, vertices_228, vertices_344, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_293, vertices_25, vertices_265, vertices_521, vertices_145, vertices_529, vertices_161, vertices_385, vertices_38, vertices_262, vertices_518, vertices_162, vertices_546, vertices_642, vertices_770, vertices_100, vertices_164, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_88, vertices_280, vertices_328, vertices_584, vertices_776, vertices_208, vertices_336, vertices_592, vertices_400, vertices_656, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_779), (false, vertices_659), (false, vertices_163), (false, vertices_421), (false, vertices_601), (false, vertices_409), (true, vertices_518), (true, vertices_546), (true, vertices_100), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_328), (true, vertices_208), (true, vertices_336), (true, vertices_224), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 18 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 8 614 38 3
cert_row_4 1 1 2 5 7 8 844 324 1
cert_row_4 2 1 3 5 6 7 468 196 1
cert_row_4 3 3 4 5 6 8 752 208 1
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 0 0 1 4 5 38 614 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 674
cert_cover_2 2 4 0 6 8 162 674 3
cert_coverFacet 3 844
cert_cover_5 3 1 1 2 5 7 324 844 1
cert_coverFacet 4 468
cert_cover_5 4 2 1 3 5 6 196 468 1
cert_coverFacet 5 228
cert_cover_2 5 4 1 5 6 100 228 3
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 208 752 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0571

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0572.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0572

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 901, 569, 433, 737, 94, 278, 710, 774, 538, 618, 348, 484, 312, 360, 49, 273, 529, 161, 545, 385, 641, 769, 22, 70, 262, 518, 26, 74, 522, 274, 530, 578, 770, 92, 276, 196, 324, 388, 644, 772, 56, 280, 536, 104, 296, 552, 328, 304, 224, 352, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_901, vertices_569, vertices_433, vertices_737, vertices_94, vertices_278, vertices_710, vertices_774, vertices_538, vertices_618, vertices_348, vertices_484, vertices_312, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_273, vertices_529, vertices_161, vertices_545, vertices_385, vertices_641, vertices_769, vertices_22, vertices_70, vertices_262, vertices_518, vertices_26, vertices_74, vertices_522, vertices_274, vertices_530, vertices_578, vertices_770, vertices_92, vertices_276, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_56, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_328, vertices_304, vertices_224, vertices_352, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_901), (false, vertices_569), (false, vertices_433), (false, vertices_737), (true, vertices_22), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_578), (true, vertices_92), (true, vertices_276), (true, vertices_196), (true, vertices_324), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_328), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 17 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_569) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_92) then 20 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_328) then 14 else
  if p.val = (true, vertices_352) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
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
cert_row_2 0 1 2 3 5 92
cert_row_4 1 0 2 4 5 8 618 74 2
cert_row_4 2 0 1 5 6 8 710 70 3
cert_row_4 3 1 4 5 6 7 484 196 1
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 22 94 2
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 710
cert_cover_5 2 2 0 1 5 6 70 710 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 618
cert_cover_5 5 1 0 2 4 5 74 618 2
cert_coverFacet 6 348
cert_cover_5 6 0 1 2 3 7 92 348 3
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 196 484 1
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coverFacet 9 360
cert_cover_2 9 4 2 5 7 104 360 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0572

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0573.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0573

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [23, 39, 595, 675, 213, 421, 713, 790, 806, 348, 452, 824, 600, 488, 680, 7, 19, 35, 515, 21, 37, 133, 81, 161, 193, 577, 641, 22, 38, 774, 530, 546, 84, 276, 292, 196, 324, 388, 88, 280, 536, 168, 296, 552, 200, 328, 584, 648, 592, 784, 416, 672, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_23, vertices_39, vertices_595, vertices_675, vertices_213, vertices_421, vertices_713, vertices_790, vertices_806, vertices_348, vertices_452, vertices_824, vertices_600, vertices_488, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_19, vertices_35, vertices_515, vertices_21, vertices_37, vertices_133, vertices_81, vertices_161, vertices_193, vertices_577, vertices_641, vertices_22, vertices_38, vertices_774, vertices_530, vertices_546, vertices_84, vertices_276, vertices_292, vertices_196, vertices_324, vertices_388, vertices_88, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_648, vertices_592, vertices_784, vertices_416, vertices_672, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_23), (false, vertices_39), (false, vertices_595), (false, vertices_675), (false, vertices_213), (false, vertices_421), (false, vertices_713), (true, vertices_774), (true, vertices_276), (true, vertices_324), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_784), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 14 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_23) then 0 else
  if p.val = (false, vertices_39) then 1 else
  if p.val = (false, vertices_595) then 19 else
  if p.val = (false, vertices_675) then 20 else
  if p.val = (false, vertices_213) then 15 else
  if p.val = (false, vertices_421) then 16 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (true, vertices_774) then 17 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_23), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_39), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
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
cert_row_2 0 0 1 7 8 774
cert_row_4 1 1 2 3 5 7 348 84 1
cert_row_4 2 2 3 4 7 8 824 280 2
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 22 790 3
cert_coverFacet 1 806
cert_cover_5 1 0 0 1 4 7 38 806 3
cert_coverFacet 2 348
cert_cover_5 2 1 1 2 3 5 84 348 1
cert_coverFacet 3 452
cert_cover_2 3 5 1 6 7 196 452 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 280 824 2
cert_coverFacet 5 600
cert_cover_2 5 3 2 5 8 88 600 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 168 488 2
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0573

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0577.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0577

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 301, 525, 677, 57, 601, 241, 334, 590, 774, 466, 930, 804, 440, 344, 13, 37, 517, 25, 41, 521, 49, 81, 161, 193, 577, 641, 78, 262, 518, 194, 322, 578, 386, 642, 770, 268, 524, 292, 548, 772, 56, 88, 280, 296, 328, 584, 176, 208, 336, 400, 416, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_301, vertices_525, vertices_677, vertices_57, vertices_601, vertices_241, vertices_334, vertices_590, vertices_774, vertices_466, vertices_930, vertices_804, vertices_440, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_517, vertices_25, vertices_41, vertices_521, vertices_49, vertices_81, vertices_161, vertices_193, vertices_577, vertices_641, vertices_78, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_268, vertices_524, vertices_292, vertices_548, vertices_772, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_584, vertices_176, vertices_208, vertices_336, vertices_400, vertices_416, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_301), (false, vertices_525), (false, vertices_677), (false, vertices_57), (false, vertices_601), (false, vertices_241), (true, vertices_78), (true, vertices_262), (true, vertices_518), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_772), (true, vertices_280), (true, vertices_328), (true, vertices_336), (true, vertices_400), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_57) then 1 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_78) then 16 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 525 1 57 262 518 322 386 770 772 280 328 336 400 416 800 707 78 301 677 601 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 3 5 6 7 466 194 1
cert_row_4 2 0 4 6 7 8 930 386 1
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 7 78 334 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 466
cert_cover_5 3 1 0 3 5 6 194 466 1
cert_coverFacet 4 930
cert_cover_5 4 2 0 4 6 7 386 930 1
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coverFacet 6 440
cert_cover_5 6 3 2 3 4 6 56 440 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0577

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0578.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0578

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 547, 451, 579, 557, 905, 721, 310, 342, 626, 300, 460, 652, 692, 212, 35, 67, 259, 515, 41, 265, 521, 545, 193, 577, 385, 641, 278, 50, 82, 290, 546, 322, 578, 44, 140, 268, 524, 52, 84, 148, 292, 548, 196, 324, 644, 296, 392, 648, 560, 208, 592, 656, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_547, vertices_451, vertices_579, vertices_557, vertices_905, vertices_721, vertices_310, vertices_342, vertices_626, vertices_300, vertices_460, vertices_652, vertices_692, vertices_212] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_259, vertices_515, vertices_41, vertices_265, vertices_521, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_278, vertices_50, vertices_82, vertices_290, vertices_546, vertices_322, vertices_578, vertices_44, vertices_140, vertices_268, vertices_524, vertices_52, vertices_84, vertices_148, vertices_292, vertices_548, vertices_196, vertices_324, vertices_644, vertices_296, vertices_392, vertices_648, vertices_560, vertices_208, vertices_592, vertices_656, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_547), (false, vertices_451), (false, vertices_579), (false, vertices_557), (false, vertices_905), (false, vertices_721), (true, vertices_278), (true, vertices_50), (true, vertices_82), (true, vertices_140), (true, vertices_268), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_292), (true, vertices_196), (true, vertices_324), (true, vertices_644), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 18 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_579) then 1 else
  if p.val = (false, vertices_557) then 15 else
  if p.val = (false, vertices_905) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_278) then 16 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_644) then 12 else
  if p.val = (true, vertices_560) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 1 547 0 579 50 82 140 268 52 84 148 292 196 324 644 560 557 278 299 451 905 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 5 6 7 460 140 2
cert_row_2 1 0 1 3 7 278
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 1 0 1 3 4 278 310 3
cert_coverFacet 1 342
cert_cover_5 1 1 0 1 3 5 278 342 3
cert_coverFacet 2 626
cert_cover_5 2 2 0 3 4 5 50 626 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 460
cert_cover_5 4 0 1 2 5 6 140 460 2
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 52 692 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0578

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0579.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0579

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 173, 333, 293, 649, 369, 737, 398, 406, 666, 330, 626, 338, 692, 308, 13, 37, 261, 73, 137, 521, 97, 161, 289, 321, 577, 641, 390, 74, 138, 266, 522, 82, 146, 274, 530, 322, 578, 140, 268, 52, 148, 276, 164, 292, 328, 648, 112, 304, 560, 336, 656, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_173, vertices_333, vertices_293, vertices_649, vertices_369, vertices_737, vertices_398, vertices_406, vertices_666, vertices_330, vertices_626, vertices_338, vertices_692, vertices_308] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_261, vertices_73, vertices_137, vertices_521, vertices_97, vertices_161, vertices_289, vertices_321, vertices_577, vertices_641, vertices_390, vertices_74, vertices_138, vertices_266, vertices_522, vertices_82, vertices_146, vertices_274, vertices_530, vertices_322, vertices_578, vertices_140, vertices_268, vertices_52, vertices_148, vertices_276, vertices_164, vertices_292, vertices_328, vertices_648, vertices_112, vertices_304, vertices_560, vertices_336, vertices_656, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_173), (false, vertices_333), (false, vertices_293), (false, vertices_649), (false, vertices_369), (false, vertices_737), (true, vertices_390), (true, vertices_138), (true, vertices_266), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_322), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_173) then 18 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_649) then 1 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_390) then 16 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_656) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_4 1 0 2 3 6 8 666 138 2
cert_row_4 2 0 3 4 5 8 626 82 2
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 390 398 2
cert_coverFacet 1 406
cert_cover_5 1 0 0 1 3 6 390 406 2
cert_coverFacet 2 666
cert_cover_5 2 1 0 2 3 6 138 666 2
cert_coverFacet 3 330
cert_cover_2 3 2 0 5 7 74 330 3
cert_coverFacet 4 626
cert_cover_5 4 2 0 3 4 5 82 626 2
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 52 692 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0579

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0580.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0580

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 405, 357, 709, 841, 393, 118, 214, 58, 154, 810, 738, 316, 408, 864, 69, 133, 261, 137, 265, 521, 321, 577, 385, 641, 86, 26, 42, 138, 522, 50, 146, 98, 546, 194, 642, 52, 148, 276, 100, 292, 196, 56, 152, 280, 296, 392, 776, 400, 352, 608, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_405, vertices_357, vertices_709, vertices_841, vertices_393, vertices_118, vertices_214, vertices_58, vertices_154, vertices_810, vertices_738, vertices_316, vertices_408, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_137, vertices_265, vertices_521, vertices_321, vertices_577, vertices_385, vertices_641, vertices_86, vertices_26, vertices_42, vertices_138, vertices_522, vertices_50, vertices_146, vertices_98, vertices_546, vertices_194, vertices_642, vertices_52, vertices_148, vertices_276, vertices_100, vertices_292, vertices_196, vertices_56, vertices_152, vertices_280, vertices_296, vertices_392, vertices_776, vertices_400, vertices_352, vertices_608, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_405), (false, vertices_357), (false, vertices_709), (false, vertices_841), (false, vertices_393), (true, vertices_86), (true, vertices_26), (true, vertices_42), (true, vertices_50), (true, vertices_146), (true, vertices_98), (true, vertices_546), (true, vertices_194), (true, vertices_52), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_841) then 23 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (true, vertices_86) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
cert_nodeAtPriority_51 393 26 42 50 146 98 546 194 52 56 152 280 296 608 800 651 86 405 357 709 841
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 6 8 738 98 3
cert_row_2 1 0 1 3 5 86
cert_row_4 2 0 2 4 7 8 810 42 3
cert_row_4 3 1 2 3 4 7 316 52 1
cert_rows
cert_pivot_2 6 5 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 1 0 1 3 4 86 118 3
cert_coverFacet 1 214
cert_cover_5 1 1 0 1 3 6 86 214 3
cert_coverFacet 2 58
cert_cover_2 2 2 0 3 4 26 58 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 810
cert_cover_5 4 2 0 2 4 7 42 810 3
cert_coverFacet 5 738
cert_cover_5 5 0 0 4 5 6 98 738 3
cert_coverFacet 6 316
cert_cover_5 6 3 1 2 3 4 52 316 1
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 864
cert_cover_2 8 5 4 7 8 352 864 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0580

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0581.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0581

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 285, 601, 425, 553, 369, 174, 558, 646, 722, 482, 540, 396, 468, 660, 25, 41, 265, 521, 81, 273, 97, 289, 545, 577, 46, 134, 518, 98, 162, 546, 194, 578, 642, 28, 140, 268, 524, 148, 276, 532, 388, 644, 536, 168, 552, 392, 208, 336, 592, 656, 352, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_285, vertices_601, vertices_425, vertices_553, vertices_369, vertices_174, vertices_558, vertices_646, vertices_722, vertices_482, vertices_540, vertices_396, vertices_468, vertices_660] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_521, vertices_81, vertices_273, vertices_97, vertices_289, vertices_545, vertices_577, vertices_46, vertices_134, vertices_518, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_388, vertices_644, vertices_536, vertices_168, vertices_552, vertices_392, vertices_208, vertices_336, vertices_592, vertices_656, vertices_352, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_285), (false, vertices_601), (false, vertices_425), (false, vertices_553), (false, vertices_369), (true, vertices_46), (true, vertices_134), (true, vertices_518), (true, vertices_162), (true, vertices_194), (true, vertices_642), (true, vertices_140), (true, vertices_524), (true, vertices_148), (true, vertices_532), (true, vertices_388), (true, vertices_644), (true, vertices_208), (true, vertices_656), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_285) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_46) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 553 134 518 162 194 642 140 524 148 532 388 644 208 656 448 611 46 285 601 425 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 3 5 6 8 722 194 1
cert_row_4 2 0 4 5 6 7 482 98 3
cert_row_4 3 1 3 5 6 7 468 148 2
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 0 0 1 2 6 46 174 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 8 46 558 3
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 722
cert_cover_5 3 1 0 3 5 6 194 722 1
cert_coverFacet 4 482
cert_cover_5 4 2 0 4 5 6 98 482 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 468
cert_cover_5 7 3 1 3 5 6 148 468 2
cert_coverFacet 8 660
cert_cover_2 8 3 1 6 8 148 660 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0581

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0582.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0582

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 229, 601, 425, 201, 865, 94, 206, 406, 538, 394, 818, 628, 308, 420, 73, 137, 265, 521, 97, 161, 289, 193, 577, 769, 78, 22, 134, 26, 138, 266, 522, 274, 530, 386, 770, 52, 84, 276, 100, 164, 292, 196, 388, 88, 536, 200, 392, 304, 560, 592, 608, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_229, vertices_601, vertices_425, vertices_201, vertices_865, vertices_94, vertices_206, vertices_406, vertices_538, vertices_394, vertices_818, vertices_628, vertices_308, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_193, vertices_577, vertices_769, vertices_78, vertices_22, vertices_134, vertices_26, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_386, vertices_770, vertices_52, vertices_84, vertices_276, vertices_100, vertices_164, vertices_292, vertices_196, vertices_388, vertices_88, vertices_536, vertices_200, vertices_392, vertices_304, vertices_560, vertices_592, vertices_608, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_229), (false, vertices_601), (false, vertices_425), (false, vertices_201), (false, vertices_865), (true, vertices_78), (true, vertices_22), (true, vertices_134), (true, vertices_26), (true, vertices_138), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_292), (true, vertices_388), (true, vertices_304), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_560) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 201 22 134 26 138 274 530 386 52 84 276 292 388 304 560 779 78 229 601 425 865
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 1 3 6 7 406 22 3
cert_row_4 2 0 3 4 7 8 818 274 2
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 78 94 3
cert_coverFacet 1 206
cert_cover_5 1 0 0 1 2 6 78 206 3
cert_coverFacet 2 406
cert_cover_5 2 1 0 1 3 6 22 406 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 818
cert_cover_5 5 2 0 3 4 7 274 818 2
cert_coverFacet 6 628
cert_cover_5 6 3 1 3 4 5 52 628 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coverFacet 8 420
cert_cover_2 8 4 1 6 7 164 420 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0582

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0583.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0583

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 93, 525, 661, 361, 553, 241, 302, 558, 774, 914, 482, 284, 788, 472, 13, 21, 517, 41, 73, 521, 81, 145, 97, 161, 545, 641, 46, 262, 518, 162, 290, 546, 386, 642, 770, 28, 268, 524, 276, 532, 772, 88, 280, 296, 552, 328, 208, 400, 656, 784, 224, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_93, vertices_525, vertices_661, vertices_361, vertices_553, vertices_241, vertices_302, vertices_558, vertices_774, vertices_914, vertices_482, vertices_284, vertices_788, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_517, vertices_41, vertices_73, vertices_521, vertices_81, vertices_145, vertices_97, vertices_161, vertices_545, vertices_641, vertices_46, vertices_262, vertices_518, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_276, vertices_532, vertices_772, vertices_88, vertices_280, vertices_296, vertices_552, vertices_328, vertices_208, vertices_400, vertices_656, vertices_784, vertices_224, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_93), (false, vertices_525), (false, vertices_661), (false, vertices_361), (false, vertices_553), (false, vertices_241), (true, vertices_46), (true, vertices_262), (true, vertices_518), (true, vertices_290), (true, vertices_386), (true, vertices_770), (true, vertices_268), (true, vertices_276), (true, vertices_772), (true, vertices_280), (true, vertices_400), (true, vertices_784), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_46) then 16 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 525 1 553 262 518 290 386 770 268 276 772 280 400 784 448 675 46 93 661 361 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 3 6 7 8 914 386 1
cert_row_4 2 0 4 5 6 7 482 162 2
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 7 46 302 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 8 46 558 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 914
cert_cover_5 3 1 0 3 6 7 386 914 1
cert_coverFacet 4 482
cert_cover_5 4 2 0 4 5 6 162 482 2
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 88 472 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0583

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0584.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0584

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 653, 269, 805, 217, 329, 737, 94, 334, 790, 242, 562, 802, 540, 696, 13, 261, 517, 73, 137, 265, 97, 289, 545, 193, 321, 641, 78, 22, 262, 50, 82, 530, 98, 290, 546, 322, 770, 28, 268, 524, 532, 772, 88, 152, 536, 328, 648, 176, 560, 208, 224, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_653, vertices_269, vertices_805, vertices_217, vertices_329, vertices_737, vertices_94, vertices_334, vertices_790, vertices_242, vertices_562, vertices_802, vertices_540, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_78, vertices_22, vertices_262, vertices_50, vertices_82, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_770, vertices_28, vertices_268, vertices_524, vertices_532, vertices_772, vertices_88, vertices_152, vertices_536, vertices_328, vertices_648, vertices_176, vertices_560, vertices_208, vertices_224, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_653), (false, vertices_269), (false, vertices_805), (false, vertices_217), (false, vertices_329), (false, vertices_737), (true, vertices_78), (true, vertices_22), (true, vertices_262), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_546), (true, vertices_770), (true, vertices_28), (true, vertices_532), (true, vertices_536), (true, vertices_176), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 15 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_78) then 16 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_560) then 13 else
  0
cert_priority
cert_nodeAtPriority_53 0 269 1 329 22 262 50 82 530 546 770 28 532 536 176 560 355 78 653 805 217 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 22 3
cert_row_2 1 0 1 2 5 78
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 2 3 4 6 8 696 152 2
cert_rows
cert_pivot_2 7 1 0 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 3 78 94 3
cert_coverFacet 1 334
cert_cover_5 1 1 0 1 2 7 78 334 3
cert_coverFacet 2 790
cert_cover_5 2 0 0 1 3 7 22 790 3
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 50 242 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 696
cert_cover_5 7 3 2 3 4 6 152 696 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0584

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0585.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0585

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 531, 611, 291, 357, 601, 457, 790, 806, 412, 692, 228, 452, 664, 744, 19, 35, 259, 515, 25, 73, 265, 529, 97, 289, 321, 577, 774, 274, 530, 290, 546, 148, 276, 532, 100, 164, 292, 548, 196, 324, 388, 152, 280, 536, 200, 584, 392, 648, 656, 224, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_531, vertices_611, vertices_291, vertices_357, vertices_601, vertices_457, vertices_790, vertices_806, vertices_412, vertices_692, vertices_228, vertices_452, vertices_664, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_515, vertices_25, vertices_73, vertices_265, vertices_529, vertices_97, vertices_289, vertices_321, vertices_577, vertices_774, vertices_274, vertices_530, vertices_290, vertices_546, vertices_148, vertices_276, vertices_532, vertices_100, vertices_164, vertices_292, vertices_548, vertices_196, vertices_324, vertices_388, vertices_152, vertices_280, vertices_536, vertices_200, vertices_584, vertices_392, vertices_648, vertices_656, vertices_224, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_531), (false, vertices_611), (false, vertices_291), (false, vertices_357), (false, vertices_601), (false, vertices_457), (true, vertices_774), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_548), (true, vertices_196), (true, vertices_388), (true, vertices_152), (true, vertices_648), (true, vertices_656), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 15 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_291) then 1 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (true, vertices_774) then 17 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 1 2 3 6 7 412 148 1
cert_row_4 2 1 3 4 6 8 692 148 2
cert_row_4 3 2 4 5 6 8 744 200 1
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 774 790 2
cert_coverFacet 1 806
cert_cover_5 1 0 0 1 4 7 774 806 2
cert_coverFacet 2 412
cert_cover_5 2 1 1 2 3 6 148 412 1
cert_coverFacet 3 692
cert_cover_5 3 2 1 3 4 6 148 692 2
cert_coverFacet 4 228
cert_cover_2 4 4 1 5 6 100 228 3
cert_coverFacet 5 452
cert_cover_2 5 5 1 6 7 196 452 3
cert_coverFacet 6 664
cert_cover_2 6 3 2 6 8 152 664 3
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 200 744 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0585

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0586.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0586

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 805, 793, 681, 457, 182, 214, 346, 306, 450, 604, 308, 788, 740, 712, 137, 265, 521, 161, 289, 545, 385, 769, 150, 50, 82, 274, 162, 290, 194, 322, 386, 52, 84, 276, 532, 164, 292, 548, 196, 580, 772, 88, 280, 536, 200, 328, 584, 648, 304, 784, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_805, vertices_793, vertices_681, vertices_457, vertices_182, vertices_214, vertices_346, vertices_306, vertices_450, vertices_604, vertices_308, vertices_788, vertices_740, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_385, vertices_769, vertices_150, vertices_50, vertices_82, vertices_274, vertices_162, vertices_290, vertices_194, vertices_322, vertices_386, vertices_52, vertices_84, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_772, vertices_88, vertices_280, vertices_536, vertices_200, vertices_328, vertices_584, vertices_648, vertices_304, vertices_784, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_805), (false, vertices_793), (false, vertices_681), (false, vertices_457), (true, vertices_150), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_196), (true, vertices_580), (true, vertices_88), (true, vertices_584), (true, vertices_304), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 17 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_793) then 22 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (true, vertices_150) then 18 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_150), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 7 346 82 1
cert_row_2 1 0 1 3 6 150
cert_row_4 2 1 2 3 5 8 604 84 1
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 7 0 2 1
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 1 0 1 3 4 150 182 3
cert_coverFacet 1 214
cert_cover_5 1 1 0 1 3 5 150 214 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 5 82 346 1
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 450
cert_cover_2 4 5 0 6 7 194 450 3
cert_coverFacet 5 604
cert_cover_5 5 2 1 2 3 5 84 604 1
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 740
cert_cover_5 8 3 1 4 5 6 164 740 2
cert_coverFacet 9 712
cert_cover_2 9 5 2 6 8 200 712 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0586

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0587.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0587

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 789, 409, 681, 841, 214, 598, 618, 226, 674, 364, 436, 228, 836, 424, 137, 265, 521, 145, 273, 529, 641, 769, 86, 146, 530, 98, 162, 546, 194, 578, 642, 148, 276, 532, 100, 164, 292, 196, 324, 580, 772, 104, 168, 296, 552, 328, 584, 392, 400, 224, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_789, vertices_409, vertices_681, vertices_841, vertices_214, vertices_598, vertices_618, vertices_226, vertices_674, vertices_364, vertices_436, vertices_228, vertices_836, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_641, vertices_769, vertices_86, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_148, vertices_276, vertices_532, vertices_100, vertices_164, vertices_292, vertices_196, vertices_324, vertices_580, vertices_772, vertices_104, vertices_168, vertices_296, vertices_552, vertices_328, vertices_584, vertices_392, vertices_400, vertices_224, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_789), (false, vertices_409), (false, vertices_681), (false, vertices_841), (true, vertices_86), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_578), (true, vertices_148), (true, vertices_100), (true, vertices_164), (true, vertices_292), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_104), (true, vertices_296), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_841) then 24 else
  if p.val = (true, vertices_86) then 18 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
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
cert_row_4 0 0 2 4 5 8 618 98 1
cert_row_2 1 0 1 3 5 86
cert_row_4 2 1 2 4 5 7 364 100 1
cert_row_4 3 1 3 4 6 7 436 148 2
cert_rows
cert_pivot_2 8 0 2 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 1 0 1 3 6 86 214 3
cert_coverFacet 1 598
cert_cover_5 1 1 0 1 3 8 86 598 3
cert_coverFacet 2 618
cert_cover_5 2 0 0 2 4 5 98 618 1
cert_coverFacet 3 226
cert_cover_2 3 4 0 5 6 98 226 3
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 364
cert_cover_5 5 2 1 2 4 5 100 364 1
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 148 436 2
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coverFacet 8 836
cert_cover_2 8 5 1 7 8 324 836 3
cert_coverFacet 9 424
cert_cover_2 9 4 2 6 7 168 424 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0587

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3153 : Certifies 3153 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0554.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3154 : Certifies 3154 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0555.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3155 : Certifies 3155 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0556.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3156 : Certifies 3156 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0557.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3157 : Certifies 3157 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0558.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3158 : Certifies 3158 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0559.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3159 : Certifies 3159 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0560.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3160 : Certifies 3160 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0561.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3161 : Certifies 3161 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0562.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3162 : Certifies 3162 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0563.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3163 : Certifies 3163 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0564.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3164 : Certifies 3164 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0565.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3165 : Certifies 3165 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0566.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3166 : Certifies 3166 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0567.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3167 : Certifies 3167 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0568.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3168 : Certifies 3168 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0570.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3169 : Certifies 3169 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0571.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3170 : Certifies 3170 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0572.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3171 : Certifies 3171 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0573.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3172 : Certifies 3172 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0577.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3173 : Certifies 3173 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0578.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3174 : Certifies 3174 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0579.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3175 : Certifies 3175 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0580.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3176 : Certifies 3176 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0581.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3177 : Certifies 3177 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0582.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3178 : Certifies 3178 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0583.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3179 : Certifies 3179 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0584.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3180 : Certifies 3180 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0585.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3181 : Certifies 3181 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0586.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3182 : Certifies 3182 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0587.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B104 (j : Fin 30) :
    Certifies (3153 + j.val) := by
  fin_cases j
  · exact projection_3153
  · exact projection_3154
  · exact projection_3155
  · exact projection_3156
  · exact projection_3157
  · exact projection_3158
  · exact projection_3159
  · exact projection_3160
  · exact projection_3161
  · exact projection_3162
  · exact projection_3163
  · exact projection_3164
  · exact projection_3165
  · exact projection_3166
  · exact projection_3167
  · exact projection_3168
  · exact projection_3169
  · exact projection_3170
  · exact projection_3171
  · exact projection_3172
  · exact projection_3173
  · exact projection_3174
  · exact projection_3175
  · exact projection_3176
  · exact projection_3177
  · exact projection_3178
  · exact projection_3179
  · exact projection_3180
  · exact projection_3181
  · exact projection_3182

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
