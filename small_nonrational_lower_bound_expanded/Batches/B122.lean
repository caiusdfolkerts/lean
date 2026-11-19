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
/- Source: ProjectionCertificates/R_m15e10q1_1131.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1131

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 613, 569, 177, 849, 481, 206, 270, 838, 186, 282, 450, 796, 236, 556, 49, 145, 273, 529, 97, 161, 545, 321, 577, 385, 14, 70, 262, 26, 138, 266, 146, 274, 194, 322, 386, 44, 204, 268, 524, 100, 548, 580, 772, 56, 280, 536, 168, 552, 176, 784, 224, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_613, vertices_569, vertices_177, vertices_849, vertices_481, vertices_206, vertices_270, vertices_838, vertices_186, vertices_282, vertices_450, vertices_796, vertices_236, vertices_556] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_14, vertices_70, vertices_262, vertices_26, vertices_138, vertices_266, vertices_146, vertices_274, vertices_194, vertices_322, vertices_386, vertices_44, vertices_204, vertices_268, vertices_524, vertices_100, vertices_548, vertices_580, vertices_772, vertices_56, vertices_280, vertices_536, vertices_168, vertices_552, vertices_176, vertices_784, vertices_224, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_613), (false, vertices_569), (false, vertices_177), (false, vertices_849), (false, vertices_481), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_194), (true, vertices_322), (true, vertices_44), (true, vertices_204), (true, vertices_268), (true, vertices_524), (true, vertices_772), (true, vertices_280), (true, vertices_168)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (false, vertices_849) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_204) then 19 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_168) then 14 else
  0
cert_priority
cert_nodeAtPriority_9 0 177 1 14 70 262 26 138 266 194 322 44 268 524 772 280 168 403 613 204 569 849 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 6 186 26 3
cert_row_2 1 1 2 5 6 204
cert_row_4 2 0 1 5 7 8 838 70 3
cert_row_4 3 1 2 3 7 8 796 268 2
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 838
cert_cover_5 2 2 0 1 5 7 70 838 3
cert_coverFacet 3 186
cert_cover_5 3 0 0 2 3 4 26 186 3
cert_coverFacet 4 282
cert_cover_2 4 2 0 3 7 26 282 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 796
cert_cover_5 6 3 1 2 3 7 268 796 2
cert_coverFacet 7 236
cert_cover_5 7 1 1 2 4 5 44 236 3
cert_coverFacet 8 556
cert_cover_2 8 2 1 4 8 44 556 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1131

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_1132.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1132

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 613, 793, 721, 481, 801, 158, 110, 710, 282, 362, 450, 812, 652, 664, 145, 273, 529, 97, 289, 545, 193, 577, 385, 769, 14, 70, 134, 26, 106, 266, 146, 274, 194, 322, 386, 44, 140, 524, 100, 548, 580, 644, 152, 280, 536, 296, 648, 776, 656, 352, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_613, vertices_793, vertices_721, vertices_481, vertices_801, vertices_158, vertices_110, vertices_710, vertices_282, vertices_362, vertices_450, vertices_812, vertices_652, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_70, vertices_134, vertices_26, vertices_106, vertices_266, vertices_146, vertices_274, vertices_194, vertices_322, vertices_386, vertices_44, vertices_140, vertices_524, vertices_100, vertices_548, vertices_580, vertices_644, vertices_152, vertices_280, vertices_536, vertices_296, vertices_648, vertices_776, vertices_656, vertices_352, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_613), (false, vertices_793), (false, vertices_721), (false, vertices_481), (false, vertices_801), (true, vertices_14), (true, vertices_70), (true, vertices_134), (true, vertices_26), (true, vertices_106), (true, vertices_266), (true, vertices_194), (true, vertices_322), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_644), (true, vertices_152), (true, vertices_296), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_106) then 17 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_648) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 801 14 70 134 26 266 194 322 44 140 524 644 152 296 648 403 106 613 793 721 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 6 158 14 3
cert_row_4 1 0 1 5 6 8 710 70 3
cert_row_2 2 0 2 4 5 106
cert_row_4 3 1 2 4 7 8 812 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 14 158 3
cert_coverFacet 1 110
cert_cover_5 1 2 0 1 2 4 14 110 3
cert_coverFacet 2 710
cert_cover_5 2 1 0 1 5 6 70 710 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 362
cert_cover_5 4 2 0 2 4 7 106 362 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 812
cert_cover_5 6 3 1 2 4 7 44 812 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1132

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_1133.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1133

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 901, 601, 361, 777, 737, 94, 334, 150, 390, 626, 178, 354, 796, 692, 73, 265, 521, 97, 161, 289, 577, 385, 641, 769, 78, 22, 134, 262, 50, 82, 146, 98, 162, 290, 322, 386, 28, 268, 148, 532, 388, 644, 772, 88, 536, 328, 776, 176, 560, 592, 352, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_901, vertices_601, vertices_361, vertices_777, vertices_737, vertices_94, vertices_334, vertices_150, vertices_390, vertices_626, vertices_178, vertices_354, vertices_796, vertices_692] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_641, vertices_769, vertices_78, vertices_22, vertices_134, vertices_262, vertices_50, vertices_82, vertices_146, vertices_98, vertices_162, vertices_290, vertices_322, vertices_386, vertices_28, vertices_268, vertices_148, vertices_532, vertices_388, vertices_644, vertices_772, vertices_88, vertices_536, vertices_328, vertices_776, vertices_176, vertices_560, vertices_592, vertices_352, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_901), (false, vertices_601), (false, vertices_361), (false, vertices_777), (false, vertices_737), (true, vertices_78), (true, vertices_22), (true, vertices_134), (true, vertices_262), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_98), (true, vertices_322), (true, vertices_28), (true, vertices_268), (true, vertices_148), (true, vertices_532), (true, vertices_176), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_148) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_560) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 777 22 134 262 50 82 146 98 322 28 268 148 532 176 560 419 78 901 601 361 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 7 8 796 28 3
cert_row_2 1 0 1 2 5 78
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 1 3 4 6 8 692 148 2
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 3 78 94 3
cert_coverFacet 1 334
cert_cover_5 1 1 0 1 2 7 78 334 3
cert_coverFacet 2 150
cert_cover_2 2 1 0 3 6 22 150 3
cert_coverFacet 3 390
cert_cover_2 3 1 0 6 7 134 390 3
cert_coverFacet 4 626
cert_cover_5 4 2 0 3 4 5 50 626 3
cert_coverFacet 5 178
cert_cover_2 5 3 0 4 6 50 178 3
cert_coverFacet 6 354
cert_cover_2 6 4 0 5 7 98 354 3
cert_coverFacet 7 796
cert_cover_5 7 0 1 2 3 7 28 796 3
cert_coverFacet 8 692
cert_cover_5 8 3 1 3 4 6 148 692 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1133

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_1134.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1134

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 93, 789, 229, 293, 625, 422, 410, 234, 618, 778, 156, 204, 404, 856, 21, 37, 69, 261, 81, 529, 97, 289, 545, 769, 106, 138, 266, 522, 162, 290, 546, 386, 770, 28, 76, 140, 148, 276, 164, 292, 196, 388, 88, 152, 280, 200, 584, 776, 592, 400, 784, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_93, vertices_789, vertices_229, vertices_293, vertices_625, vertices_422, vertices_410, vertices_234, vertices_618, vertices_778, vertices_156, vertices_204, vertices_404, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_69, vertices_261, vertices_81, vertices_529, vertices_97, vertices_289, vertices_545, vertices_769, vertices_106, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_28, vertices_76, vertices_140, vertices_148, vertices_276, vertices_164, vertices_292, vertices_196, vertices_388, vertices_88, vertices_152, vertices_280, vertices_200, vertices_584, vertices_776, vertices_592, vertices_400, vertices_784, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_93), (false, vertices_789), (false, vertices_229), (false, vertices_293), (false, vertices_625), (true, vertices_106), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_162), (true, vertices_386), (true, vertices_140), (true, vertices_148), (true, vertices_388), (true, vertices_152), (true, vertices_280), (true, vertices_200), (true, vertices_584), (true, vertices_776), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_93) then 19 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_229) then 21 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_106) then 17 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_19 0 293 1 138 266 522 162 386 140 148 388 152 280 200 584 776 400 803 106 93 789 229 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 7 422 162 1
cert_row_2 1 0 2 4 5 106
cert_row_4 2 0 2 3 6 7 410 138 2
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 162 422 1
cert_coverFacet 1 410
cert_cover_5 1 2 0 2 3 6 138 410 2
cert_coverFacet 2 234
cert_cover_5 2 1 0 2 4 6 106 234 3
cert_coverFacet 3 618
cert_cover_5 3 1 0 2 4 8 106 618 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 204
cert_cover_2 6 2 1 5 6 76 204 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 856
cert_cover_5 8 3 2 3 5 7 88 856 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1134

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_1135.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1135

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 597, 409, 241, 785, 865, 286, 590, 806, 618, 170, 394, 220, 788, 232, 81, 145, 273, 529, 97, 161, 289, 577, 385, 769, 14, 262, 518, 42, 586, 138, 266, 162, 290, 546, 386, 28, 76, 84, 276, 532, 580, 772, 152, 280, 104, 168, 200, 392, 208, 784, 224, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_597, vertices_409, vertices_241, vertices_785, vertices_865, vertices_286, vertices_590, vertices_806, vertices_618, vertices_170, vertices_394, vertices_220, vertices_788, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_769, vertices_14, vertices_262, vertices_518, vertices_42, vertices_586, vertices_138, vertices_266, vertices_162, vertices_290, vertices_546, vertices_386, vertices_28, vertices_76, vertices_84, vertices_276, vertices_532, vertices_580, vertices_772, vertices_152, vertices_280, vertices_104, vertices_168, vertices_200, vertices_392, vertices_208, vertices_784, vertices_224, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_597), (false, vertices_409), (false, vertices_241), (false, vertices_785), (false, vertices_865), (true, vertices_14), (true, vertices_262), (true, vertices_518), (true, vertices_42), (true, vertices_586), (true, vertices_138), (true, vertices_266), (true, vertices_546), (true, vertices_28), (true, vertices_76), (true, vertices_276), (true, vertices_772), (true, vertices_104), (true, vertices_168), (true, vertices_200)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_586) then 17 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_200) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 785 14 262 518 42 138 266 546 28 76 276 772 104 168 200 419 586 597 409 241 865
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 262 2
cert_row_2 1 0 2 5 8 586
cert_row_4 2 0 1 2 3 7 286 14 3
cert_row_4 3 1 2 3 5 6 220 28 3
cert_rows
cert_pivot_2 4 8 0 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 2 0 1 2 3 14 286 3
cert_coverFacet 1 590
cert_cover_5 1 1 0 1 2 5 14 590 3
cert_coverFacet 2 806
cert_cover_5 2 0 0 1 4 7 262 806 2
cert_coverFacet 3 618
cert_cover_5 3 1 0 2 4 5 42 618 3
cert_coverFacet 4 170
cert_cover_2 4 2 0 4 6 42 170 3
cert_coverFacet 5 394
cert_cover_2 5 2 0 6 7 138 394 3
cert_coverFacet 6 220
cert_cover_5 6 3 1 2 3 5 28 220 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 232
cert_cover_2 8 4 2 5 6 104 232 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1135

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_1136.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1136

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 285, 901, 153, 457, 689, 62, 110, 326, 774, 626, 962, 332, 184, 744, 21, 261, 517, 25, 137, 265, 145, 529, 385, 641, 46, 22, 70, 262, 518, 50, 530, 98, 322, 578, 770, 28, 76, 268, 324, 772, 56, 152, 104, 168, 200, 328, 176, 560, 608, 672, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_285, vertices_901, vertices_153, vertices_457, vertices_689, vertices_62, vertices_110, vertices_326, vertices_774, vertices_626, vertices_962, vertices_332, vertices_184, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_261, vertices_517, vertices_25, vertices_137, vertices_265, vertices_145, vertices_529, vertices_385, vertices_641, vertices_46, vertices_22, vertices_70, vertices_262, vertices_518, vertices_50, vertices_530, vertices_98, vertices_322, vertices_578, vertices_770, vertices_28, vertices_76, vertices_268, vertices_324, vertices_772, vertices_56, vertices_152, vertices_104, vertices_168, vertices_200, vertices_328, vertices_176, vertices_560, vertices_608, vertices_672, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_285), (false, vertices_901), (false, vertices_153), (false, vertices_457), (false, vertices_689), (true, vertices_46), (true, vertices_70), (true, vertices_262), (true, vertices_50), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_76), (true, vertices_324), (true, vertices_56), (true, vertices_104), (true, vertices_168), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 16 else
  if p.val = (false, vertices_285) then 19 else
  if p.val = (false, vertices_901) then 20 else
  if p.val = (false, vertices_153) then 0 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (true, vertices_46) then 17 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 153 70 262 50 98 322 578 770 76 324 56 104 168 608 704 535 46 285 901 457 689
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 3 4 5 8 626 50 3
cert_row_4 2 0 5 6 7 8 962 322 2
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 46 62 3
cert_coverFacet 1 110
cert_cover_5 1 0 0 1 2 5 46 110 3
cert_coverFacet 2 326
cert_cover_2 2 1 0 5 7 70 326 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 626
cert_cover_5 4 1 0 3 4 5 50 626 3
cert_coverFacet 5 962
cert_cover_5 5 2 0 5 6 7 322 962 2
cert_coverFacet 6 332
cert_cover_2 6 2 1 5 7 76 332 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 744
cert_cover_5 8 3 2 4 5 6 104 744 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1136

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_1137.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1137

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 397, 361, 713, 433, 673, 654, 182, 534, 370, 594, 674, 348, 604, 404, 73, 137, 265, 97, 161, 289, 545, 577, 385, 641, 22, 134, 518, 50, 82, 530, 98, 162, 546, 578, 642, 92, 140, 268, 524, 148, 276, 532, 388, 328, 584, 648, 176, 304, 336, 592, 400, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_397, vertices_361, vertices_713, vertices_433, vertices_673, vertices_654, vertices_182, vertices_534, vertices_370, vertices_594, vertices_674, vertices_348, vertices_604, vertices_404] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_97, vertices_161, vertices_289, vertices_545, vertices_577, vertices_385, vertices_641, vertices_22, vertices_134, vertices_518, vertices_50, vertices_82, vertices_530, vertices_98, vertices_162, vertices_546, vertices_578, vertices_642, vertices_92, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_388, vertices_328, vertices_584, vertices_648, vertices_176, vertices_304, vertices_336, vertices_592, vertices_400, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_397), (false, vertices_361), (false, vertices_713), (false, vertices_433), (false, vertices_673), (true, vertices_22), (true, vertices_134), (true, vertices_518), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_162), (true, vertices_642), (true, vertices_92), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_336), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_673) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_162) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_92) then 19 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 673 2 22 1 134 3 518 50 82 530 162 642 524 148 276 532 336 592 611 397 92 361 713 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 134 2
cert_row_2 1 1 2 3 5 92
cert_row_4 2 0 1 3 4 6 182 22 3
cert_row_4 3 0 3 4 5 7 370 50 3
cert_rows
cert_pivot_2 8 2 1 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 134 654 2
cert_coverFacet 1 182
cert_cover_5 1 2 0 1 3 4 22 182 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 370
cert_cover_5 3 3 0 3 4 5 50 370 3
cert_coverFacet 4 594
cert_cover_2 4 3 0 5 8 82 594 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 348
cert_cover_5 6 1 1 2 3 7 92 348 3
cert_coverFacet 7 604
cert_cover_5 7 1 1 2 3 8 92 604 3
cert_coverFacet 8 404
cert_cover_2 8 3 1 6 7 148 404 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1137

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_1138.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1138

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 357, 313, 105, 713, 849, 654, 182, 310, 838, 154, 786, 740, 184, 232, 25, 41, 73, 521, 273, 529, 97, 289, 321, 577, 54, 134, 262, 518, 26, 138, 522, 146, 274, 530, 770, 100, 164, 292, 324, 580, 644, 56, 152, 104, 168, 200, 648, 176, 304, 784, 224, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_357, vertices_313, vertices_105, vertices_713, vertices_849, vertices_654, vertices_182, vertices_310, vertices_838, vertices_154, vertices_786, vertices_740, vertices_184, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_73, vertices_521, vertices_273, vertices_529, vertices_97, vertices_289, vertices_321, vertices_577, vertices_54, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_770, vertices_100, vertices_164, vertices_292, vertices_324, vertices_580, vertices_644, vertices_56, vertices_152, vertices_104, vertices_168, vertices_200, vertices_648, vertices_176, vertices_304, vertices_784, vertices_224, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_357), (false, vertices_313), (false, vertices_105), (false, vertices_713), (false, vertices_849), (true, vertices_54), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_146), (true, vertices_274), (true, vertices_770), (true, vertices_164), (true, vertices_580), (true, vertices_644), (true, vertices_152), (true, vertices_168), (true, vertices_176), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 16 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_105) then 0 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (true, vertices_54) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 105 134 262 518 138 146 274 770 164 580 644 152 168 176 224 539 54 357 313 713 849
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 0 1 2 6 8 654 134 2
cert_row_4 2 0 1 5 7 8 838 262 2
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 134 654 2
cert_coverFacet 1 182
cert_cover_5 1 0 0 1 3 6 54 182 3
cert_coverFacet 2 310
cert_cover_5 2 0 0 1 3 7 54 310 3
cert_coverFacet 3 838
cert_cover_5 3 2 0 1 5 7 262 838 2
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 100 740 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 232
cert_cover_2 8 4 2 5 6 104 232 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1138

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_1139.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1139

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 341, 613, 901, 361, 417, 406, 314, 154, 618, 650, 418, 220, 716, 344, 69, 261, 517, 97, 161, 289, 545, 321, 385, 641, 26, 42, 138, 522, 146, 274, 162, 290, 546, 386, 642, 204, 84, 148, 276, 580, 388, 644, 88, 152, 280, 104, 296, 328, 584, 648, 336, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_341, vertices_613, vertices_901, vertices_361, vertices_417, vertices_406, vertices_314, vertices_154, vertices_618, vertices_650, vertices_418, vertices_220, vertices_716, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_545, vertices_321, vertices_385, vertices_641, vertices_26, vertices_42, vertices_138, vertices_522, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_204, vertices_84, vertices_148, vertices_276, vertices_580, vertices_388, vertices_644, vertices_88, vertices_152, vertices_280, vertices_104, vertices_296, vertices_328, vertices_584, vertices_648, vertices_336, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_341), (false, vertices_613), (false, vertices_901), (false, vertices_361), (false, vertices_417), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_290), (true, vertices_386), (true, vertices_204), (true, vertices_148), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_584), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_341) then 21 else
  if p.val = (false, vertices_613) then 22 else
  if p.val = (false, vertices_901) then 23 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_204) then 19 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_648) then 14 else
  0
cert_priority
cert_nodeAtPriority_43 417 1 26 2 42 138 522 146 274 290 386 148 88 152 280 584 648 675 361 204 341 613 901
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 8 618 42 3
cert_row_2 1 1 2 5 6 204
cert_row_4 2 0 1 3 6 7 406 146 1
cert_row_4 3 0 2 3 4 7 314 26 3
cert_rows
cert_pivot_2 8 5 1 0
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 2 0 1 3 6 146 406 1
cert_coverFacet 1 314
cert_cover_5 1 3 0 2 3 4 26 314 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 618
cert_cover_5 3 0 0 2 4 5 42 618 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 220
cert_cover_5 6 1 1 2 3 5 204 220 2
cert_coverFacet 7 716
cert_cover_5 7 1 1 2 5 8 204 716 3
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1139

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_1140.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1140

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 557, 397, 597, 325, 713, 566, 186, 410, 850, 738, 60, 284, 340, 680, 13, 69, 261, 517, 137, 521, 193, 321, 577, 385, 154, 50, 274, 530, 162, 546, 194, 322, 578, 386, 28, 44, 268, 52, 84, 276, 532, 548, 324, 56, 280, 168, 552, 392, 648, 336, 592, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_557, vertices_397, vertices_597, vertices_325, vertices_713, vertices_566, vertices_186, vertices_410, vertices_850, vertices_738, vertices_60, vertices_284, vertices_340, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_517, vertices_137, vertices_521, vertices_193, vertices_321, vertices_577, vertices_385, vertices_154, vertices_50, vertices_274, vertices_530, vertices_162, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_28, vertices_44, vertices_268, vertices_52, vertices_84, vertices_276, vertices_532, vertices_548, vertices_324, vertices_56, vertices_280, vertices_168, vertices_552, vertices_392, vertices_648, vertices_336, vertices_592, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_557), (false, vertices_397), (false, vertices_597), (false, vertices_325), (false, vertices_713), (true, vertices_154), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_578), (true, vertices_28), (true, vertices_52), (true, vertices_276), (true, vertices_56), (true, vertices_280), (true, vertices_168), (true, vertices_336), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_397) then 20 else
  if p.val = (false, vertices_597) then 21 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_713) then 23 else
  if p.val = (true, vertices_154) then 17 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
cert_nodeAtPriority_51 325 50 274 530 162 546 578 28 52 276 56 280 168 336 672 451 154 557 397 597 713
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 0 1 3 4 8 566 50 1
cert_row_4 2 0 3 5 7 8 850 274 2
cert_row_4 3 0 4 5 6 8 738 162 2
cert_rows
cert_pivot_2 2 1 3 0
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 1 0 1 3 4 50 566 1
cert_coverFacet 1 186
cert_cover_5 1 0 0 2 3 4 154 186 3
cert_coverFacet 2 410
cert_cover_5 2 0 0 2 3 7 154 410 3
cert_coverFacet 3 850
cert_cover_5 3 2 0 3 5 7 274 850 2
cert_coverFacet 4 738
cert_cover_5 4 3 0 4 5 6 162 738 2
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coverFacet 8 680
cert_cover_2 8 4 2 6 8 168 680 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1140

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_1141.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1141

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 229, 617, 457, 817, 417, 398, 310, 214, 650, 722, 786, 628, 420, 712, 73, 265, 521, 97, 161, 289, 545, 193, 385, 769, 22, 134, 262, 138, 266, 522, 210, 274, 530, 642, 770, 52, 84, 100, 164, 292, 196, 388, 200, 584, 392, 648, 304, 560, 592, 784, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_229, vertices_617, vertices_457, vertices_817, vertices_417, vertices_398, vertices_310, vertices_214, vertices_650, vertices_722, vertices_786, vertices_628, vertices_420, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_385, vertices_769, vertices_22, vertices_134, vertices_262, vertices_138, vertices_266, vertices_522, vertices_210, vertices_274, vertices_530, vertices_642, vertices_770, vertices_52, vertices_84, vertices_100, vertices_164, vertices_292, vertices_196, vertices_388, vertices_200, vertices_584, vertices_392, vertices_648, vertices_304, vertices_560, vertices_592, vertices_784, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_229), (false, vertices_617), (false, vertices_457), (false, vertices_817), (false, vertices_417), (true, vertices_22), (true, vertices_134), (true, vertices_262), (true, vertices_138), (true, vertices_210), (true, vertices_274), (true, vertices_530), (true, vertices_642), (true, vertices_52), (true, vertices_84), (true, vertices_292), (true, vertices_388), (true, vertices_648), (true, vertices_592), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_210) then 17 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 417 22 134 262 138 274 530 642 52 84 292 388 648 592 704 779 210 229 617 457 817
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_2 1 0 3 5 6 210
cert_row_4 2 0 1 3 4 7 310 22 3
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 310
cert_cover_5 1 2 0 1 3 4 22 310 3
cert_coverFacet 2 214
cert_cover_5 2 1 0 1 3 5 22 214 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 722
cert_cover_5 4 1 0 3 5 8 210 722 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 628
cert_cover_5 6 3 1 3 4 5 52 628 3
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coverFacet 8 712
cert_cover_2 8 5 2 6 8 200 712 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1141

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_1142.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1142

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 405, 357, 197, 713, 929, 110, 302, 602, 282, 914, 802, 668, 284, 204, 69, 133, 261, 97, 289, 545, 193, 577, 385, 641, 46, 26, 74, 266, 274, 530, 98, 290, 546, 578, 770, 28, 76, 140, 268, 148, 276, 100, 292, 196, 280, 536, 200, 584, 648, 400, 656, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_405, vertices_357, vertices_197, vertices_713, vertices_929, vertices_110, vertices_302, vertices_602, vertices_282, vertices_914, vertices_802, vertices_668, vertices_284, vertices_204] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_97, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_46, vertices_26, vertices_74, vertices_266, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_28, vertices_76, vertices_140, vertices_268, vertices_148, vertices_276, vertices_100, vertices_292, vertices_196, vertices_280, vertices_536, vertices_200, vertices_584, vertices_648, vertices_400, vertices_656, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_405), (false, vertices_357), (false, vertices_197), (false, vertices_713), (false, vertices_929), (true, vertices_46), (true, vertices_26), (true, vertices_74), (true, vertices_266), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_770), (true, vertices_28), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_280), (true, vertices_536), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_46) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_268) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
cert_nodeAtPriority_34 197 26 74 266 274 530 290 770 28 76 140 268 280 536 656 611 46 405 357 713 929
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 2 3 5 8 602 26 3
cert_row_4 2 0 3 6 7 8 914 274 2
cert_row_4 3 1 2 3 6 8 668 28 3
cert_rows
cert_pivot_2 4 5 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 5 46 110 3
cert_coverFacet 1 302
cert_cover_5 1 0 0 1 2 7 46 302 3
cert_coverFacet 2 602
cert_cover_5 2 1 0 2 3 5 26 602 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 914
cert_cover_5 4 2 0 3 6 7 274 914 2
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 668
cert_cover_5 6 3 1 2 3 6 28 668 3
cert_coverFacet 7 284
cert_cover_2 7 2 1 3 7 28 284 3
cert_coverFacet 8 204
cert_cover_2 8 2 1 5 6 76 204 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1142

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_1143.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1143

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 613, 121, 809, 649, 721, 782, 710, 390, 314, 650, 402, 244, 436, 804, 25, 41, 137, 521, 81, 145, 97, 545, 577, 641, 134, 262, 518, 26, 138, 266, 522, 146, 274, 386, 642, 180, 100, 292, 548, 196, 580, 388, 772, 56, 296, 648, 776, 112, 304, 208, 400, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_613, vertices_121, vertices_809, vertices_649, vertices_721, vertices_782, vertices_710, vertices_390, vertices_314, vertices_650, vertices_402, vertices_244, vertices_436, vertices_804] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_137, vertices_521, vertices_81, vertices_145, vertices_97, vertices_545, vertices_577, vertices_641, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_386, vertices_642, vertices_180, vertices_100, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_772, vertices_56, vertices_296, vertices_648, vertices_776, vertices_112, vertices_304, vertices_208, vertices_400, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_613), (false, vertices_121), (false, vertices_809), (false, vertices_649), (false, vertices_721), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_386), (true, vertices_642), (true, vertices_180), (true, vertices_292), (true, vertices_196), (true, vertices_388), (true, vertices_772), (true, vertices_304), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 16 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_121) then 21 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_649) then 0 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_180) then 19 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 649 2 134 1 262 3 518 266 522 274 386 642 292 196 388 772 304 400 155 613 180 121 809 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 8 710 134 2
cert_row_2 1 1 3 4 6 180
cert_row_4 2 0 1 2 7 8 782 262 2
cert_row_4 3 0 2 3 4 7 314 26 3
cert_rows
cert_pivot_2 5 6 1 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 262 782 2
cert_coverFacet 1 710
cert_cover_5 1 0 0 1 5 6 134 710 2
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 314
cert_cover_5 3 3 0 2 3 4 26 314 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 244
cert_cover_5 6 1 1 3 4 5 180 244 3
cert_coverFacet 7 436
cert_cover_5 7 1 1 3 4 7 180 436 3
cert_coverFacet 8 804
cert_cover_2 8 4 1 7 8 292 804 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1143

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_1144.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1144

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 541, 45, 229, 837, 57, 689, 782, 666, 282, 242, 370, 834, 364, 312, 13, 37, 69, 517, 25, 41, 49, 529, 161, 193, 577, 641, 26, 266, 522, 114, 146, 274, 194, 322, 578, 642, 770, 44, 268, 524, 100, 324, 772, 56, 280, 536, 296, 176, 304, 656, 224, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_541, vertices_45, vertices_229, vertices_837, vertices_57, vertices_689, vertices_782, vertices_666, vertices_282, vertices_242, vertices_370, vertices_834, vertices_364, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_517, vertices_25, vertices_41, vertices_49, vertices_529, vertices_161, vertices_193, vertices_577, vertices_641, vertices_26, vertices_266, vertices_522, vertices_114, vertices_146, vertices_274, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_44, vertices_268, vertices_524, vertices_100, vertices_324, vertices_772, vertices_56, vertices_280, vertices_536, vertices_296, vertices_176, vertices_304, vertices_656, vertices_224, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_541), (false, vertices_45), (false, vertices_229), (false, vertices_837), (false, vertices_57), (false, vertices_689), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_114), (true, vertices_146), (true, vertices_274), (true, vertices_322), (true, vertices_770), (true, vertices_268), (true, vertices_280), (true, vertices_296), (true, vertices_304), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_541) then 18 else
  if p.val = (false, vertices_45) then 0 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_57) then 1 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_114) then 16 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
cert_nodeAtPriority_15 0 45 1 57 26 266 522 146 274 322 770 268 280 296 304 352 707 114 541 229 837 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 26 3
cert_row_2 1 0 3 4 5 114
cert_row_4 2 0 1 2 7 8 782 266 1
cert_row_4 3 1 2 4 5 7 364 44 3
cert_rows
cert_pivot_2 6 3 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 266 782 1
cert_coverFacet 1 666
cert_cover_5 1 0 0 2 3 6 26 666 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 242
cert_cover_5 3 1 0 3 4 6 114 242 3
cert_coverFacet 4 370
cert_cover_5 4 1 0 3 4 7 114 370 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 364
cert_cover_5 6 3 1 2 4 5 44 364 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1144

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_1145.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1145

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 405, 837, 645, 313, 153, 681, 454, 218, 626, 306, 402, 834, 716, 632, 133, 261, 517, 25, 41, 137, 145, 273, 289, 545, 641, 769, 50, 82, 146, 274, 290, 546, 194, 322, 578, 386, 770, 196, 324, 580, 388, 644, 56, 88, 152, 552, 200, 584, 648, 624, 304, 400, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_405, vertices_837, vertices_645, vertices_313, vertices_153, vertices_681, vertices_454, vertices_218, vertices_626, vertices_306, vertices_402, vertices_834, vertices_716, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_41, vertices_137, vertices_145, vertices_273, vertices_289, vertices_545, vertices_641, vertices_769, vertices_50, vertices_82, vertices_146, vertices_274, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_56, vertices_88, vertices_152, vertices_552, vertices_200, vertices_584, vertices_648, vertices_624, vertices_304, vertices_400, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_405), (false, vertices_837), (false, vertices_645), (false, vertices_313), (false, vertices_153), (false, vertices_681), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_196), (true, vertices_88), (true, vertices_200), (true, vertices_584), (true, vertices_624)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_313) then 20 else
  if p.val = (false, vertices_153) then 1 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_386) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_624) then 23 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_645), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_153), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(true, vertices_624), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 8 624
cert_row_4 1 0 1 5 6 7 454 194 1
cert_row_4 2 0 2 3 5 6 218 82 1
cert_row_4 3 1 2 5 6 8 716 196 1
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 1 0 1 5 6 194 454 1
cert_coverFacet 1 218
cert_cover_5 1 2 0 2 3 5 82 218 1
cert_coverFacet 2 626
cert_cover_5 2 0 0 3 4 5 50 626 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 716
cert_cover_5 6 3 1 2 5 6 196 716 1
cert_coverFacet 7 632
cert_cover_5 7 0 2 3 4 5 56 632 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1145

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_1146.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1146

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [91, 563, 323, 899, 677, 177, 465, 334, 538, 778, 572, 236, 780, 964, 248, 19, 67, 259, 515, 49, 81, 145, 161, 545, 321, 385, 641, 26, 74, 266, 522, 530, 322, 770, 44, 76, 268, 524, 164, 548, 196, 324, 644, 772, 56, 88, 536, 232, 776, 176, 560, 208, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_91, vertices_563, vertices_323, vertices_899, vertices_677, vertices_177, vertices_465, vertices_334, vertices_538, vertices_778, vertices_572, vertices_236, vertices_780, vertices_964, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_259, vertices_515, vertices_49, vertices_81, vertices_145, vertices_161, vertices_545, vertices_321, vertices_385, vertices_641, vertices_26, vertices_74, vertices_266, vertices_522, vertices_530, vertices_322, vertices_770, vertices_44, vertices_76, vertices_268, vertices_524, vertices_164, vertices_548, vertices_196, vertices_324, vertices_644, vertices_772, vertices_56, vertices_88, vertices_536, vertices_232, vertices_776, vertices_176, vertices_560, vertices_208, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_91), (false, vertices_563), (false, vertices_323), (false, vertices_899), (false, vertices_677), (false, vertices_177), (false, vertices_465), (true, vertices_266), (true, vertices_522), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_196), (true, vertices_324), (true, vertices_772), (true, vertices_56), (true, vertices_536), (true, vertices_232), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_177) then 1 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_232) then 21 else
  if p.val = (true, vertices_776) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 7 334 74 1
cert_row_4 1 1 2 3 4 8 572 44 2
cert_row_2 2 2 4 5 6 232
cert_row_4 3 1 5 6 7 8 964 196 3
cert_rows
cert_pivot_2 0 3 2 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 74 334 1
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 572
cert_cover_5 3 1 1 2 3 4 44 572 2
cert_coverFacet 4 236
cert_cover_5 4 2 1 2 4 5 44 236 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 964
cert_cover_5 6 3 1 5 6 7 196 964 3
cert_coverFacet 7 248
cert_cover_5 7 2 2 3 4 5 56 248 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1146

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_1147.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1147

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [79, 29, 789, 709, 345, 929, 449, 46, 566, 582, 426, 458, 738, 60, 824, 13, 21, 69, 517, 25, 73, 273, 193, 321, 385, 641, 769, 14, 38, 70, 518, 42, 74, 394, 162, 546, 194, 578, 28, 44, 52, 532, 580, 56, 280, 296, 328, 560, 784, 416, 672, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_79, vertices_29, vertices_789, vertices_709, vertices_345, vertices_929, vertices_449, vertices_46, vertices_566, vertices_582, vertices_426, vertices_458, vertices_738, vertices_60, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_69, vertices_517, vertices_25, vertices_73, vertices_273, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_38, vertices_70, vertices_518, vertices_42, vertices_74, vertices_394, vertices_162, vertices_546, vertices_194, vertices_578, vertices_28, vertices_44, vertices_52, vertices_532, vertices_580, vertices_56, vertices_280, vertices_296, vertices_328, vertices_560, vertices_784, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_79), (false, vertices_29), (false, vertices_789), (false, vertices_709), (false, vertices_345), (false, vertices_929), (false, vertices_449), (true, vertices_38), (true, vertices_518), (true, vertices_42), (true, vertices_394), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_578), (true, vertices_44), (true, vertices_52), (true, vertices_56), (true, vertices_296), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_79) then 15 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_929) then 24 else
  if p.val = (false, vertices_449) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_394) then 16 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_52) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_560) then 13 else
  0
cert_priority
cert_nodeAtPriority_53 0 29 1 449 38 518 42 162 546 194 578 44 52 56 296 560 79 394 789 709 345 929
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 38 2
cert_row_4 1 0 4 5 6 8 738 162 2
cert_row_2 2 0 2 6 7 394
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 46
cert_cover_2 0 1 0 2 4 14 46 3
cert_coverFacet 1 566
cert_cover_5 1 0 0 1 3 4 38 566 2
cert_coverFacet 2 582
cert_cover_2 2 1 0 5 8 70 582 3
cert_coverFacet 3 426
cert_cover_5 3 2 0 2 4 6 42 426 3
cert_coverFacet 4 458
cert_cover_5 4 2 0 2 5 6 74 458 3
cert_coverFacet 5 738
cert_cover_5 5 1 0 4 5 6 162 738 2
cert_coverFacet 6 60
cert_cover_2 6 2 1 3 4 28 60 3
cert_coverFacet 7 824
cert_cover_5 7 3 2 3 4 7 56 824 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1147

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_1148.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1148

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [227, 789, 185, 561, 465, 865, 286, 590, 454, 618, 170, 394, 572, 836, 408, 49, 145, 273, 529, 97, 161, 545, 193, 321, 769, 14, 70, 262, 42, 586, 138, 266, 98, 162, 194, 386, 28, 524, 276, 532, 324, 580, 772, 56, 152, 280, 168, 552, 392, 560, 400, 608, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_789, vertices_185, vertices_561, vertices_465, vertices_865, vertices_286, vertices_590, vertices_454, vertices_618, vertices_170, vertices_394, vertices_572, vertices_836, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_769, vertices_14, vertices_70, vertices_262, vertices_42, vertices_586, vertices_138, vertices_266, vertices_98, vertices_162, vertices_194, vertices_386, vertices_28, vertices_524, vertices_276, vertices_532, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_552, vertices_392, vertices_560, vertices_400, vertices_608, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_789), (false, vertices_185), (false, vertices_561), (false, vertices_465), (false, vertices_865), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_42), (true, vertices_586), (true, vertices_138), (true, vertices_266), (true, vertices_386), (true, vertices_28), (true, vertices_524), (true, vertices_324), (true, vertices_580), (true, vertices_280), (true, vertices_552), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 16 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (false, vertices_865) then 25 else
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
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 561 14 70 262 42 138 266 386 28 524 324 580 280 552 392 227 586 789 185 465 865
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
cert_coverFacet 7 836
cert_cover_2 7 5 1 7 8 324 836 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1148

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_1149.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1149

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 789, 601, 241, 401, 865, 206, 270, 406, 618, 298, 226, 220, 540, 812, 81, 145, 273, 529, 97, 161, 289, 577, 385, 769, 14, 134, 262, 42, 74, 266, 98, 162, 290, 194, 386, 28, 204, 268, 524, 148, 276, 532, 772, 88, 536, 296, 552, 584, 208, 400, 224, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_789, vertices_601, vertices_241, vertices_401, vertices_865, vertices_206, vertices_270, vertices_406, vertices_618, vertices_298, vertices_226, vertices_220, vertices_540, vertices_812] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_769, vertices_14, vertices_134, vertices_262, vertices_42, vertices_74, vertices_266, vertices_98, vertices_162, vertices_290, vertices_194, vertices_386, vertices_28, vertices_204, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_772, vertices_88, vertices_536, vertices_296, vertices_552, vertices_584, vertices_208, vertices_400, vertices_224, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_789), (false, vertices_601), (false, vertices_241), (false, vertices_401), (false, vertices_865), (true, vertices_14), (true, vertices_134), (true, vertices_262), (true, vertices_42), (true, vertices_74), (true, vertices_266), (true, vertices_98), (true, vertices_194), (true, vertices_28), (true, vertices_204), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_296), (true, vertices_552)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_194) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_204) then 19 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_148) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_552) then 14 else
  0
cert_priority
cert_nodeAtPriority_9 0 401 1 14 134 262 42 74 266 98 194 28 268 524 148 296 552 419 789 204 601 241 865
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
cert_coverFacet 5 226
cert_cover_2 5 4 0 5 6 98 226 3
cert_coverFacet 6 220
cert_cover_5 6 1 1 2 3 5 28 220 3
cert_coverFacet 7 540
cert_cover_2 7 2 1 3 8 28 540 3
cert_coverFacet 8 812
cert_cover_5 8 3 1 2 4 7 268 812 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1149

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_1150.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1150

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 651, 355, 195, 541, 45, 293, 233, 722, 834, 412, 428, 852, 664, 496, 67, 131, 259, 515, 13, 37, 261, 517, 41, 137, 521, 97, 289, 193, 194, 322, 578, 642, 770, 28, 44, 396, 276, 532, 292, 772, 152, 536, 168, 648, 208, 336, 592, 400, 656, 224, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_651, vertices_355, vertices_195, vertices_541, vertices_45, vertices_293, vertices_233, vertices_722, vertices_834, vertices_412, vertices_428, vertices_852, vertices_664, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_13, vertices_37, vertices_261, vertices_517, vertices_41, vertices_137, vertices_521, vertices_97, vertices_289, vertices_193, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_44, vertices_396, vertices_276, vertices_532, vertices_292, vertices_772, vertices_152, vertices_536, vertices_168, vertices_648, vertices_208, vertices_336, vertices_592, vertices_400, vertices_656, vertices_224, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_651), (false, vertices_355), (false, vertices_195), (false, vertices_541), (false, vertices_45), (false, vertices_293), (false, vertices_233), (true, vertices_578), (true, vertices_396), (true, vertices_276), (true, vertices_152), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_400), (true, vertices_656), (true, vertices_416), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_355) then 16 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_541) then 18 else
  if p.val = (false, vertices_45) then 1 else
  if p.val = (false, vertices_293) then 2 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_396) then 19 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 3 5 6 8 722 194 1
cert_row_4 2 1 3 5 7 8 852 276 2
cert_row_4 3 3 4 5 6 7 496 208 1
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 722
cert_cover_5 0 1 0 3 5 6 194 722 1
cert_coverFacet 1 834
cert_cover_2 1 5 0 7 8 322 834 3
cert_coverFacet 2 412
cert_cover_5 2 0 1 2 3 6 28 412 3
cert_coverFacet 3 428
cert_cover_5 3 0 1 2 4 6 44 428 3
cert_coverFacet 4 852
cert_cover_5 4 2 1 3 5 7 276 852 2
cert_coverFacet 5 664
cert_cover_2 5 3 2 6 8 152 664 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 208 496 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1150

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_1151.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1151

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 109, 781, 805, 713, 241, 561, 454, 842, 818, 402, 706, 332, 436, 228, 13, 37, 773, 73, 521, 49, 145, 529, 97, 545, 193, 641, 146, 274, 530, 194, 322, 578, 386, 642, 770, 76, 268, 100, 164, 292, 196, 324, 388, 328, 584, 776, 176, 304, 560, 400, 224, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_109, vertices_781, vertices_805, vertices_713, vertices_241, vertices_561, vertices_454, vertices_842, vertices_818, vertices_402, vertices_706, vertices_332, vertices_436, vertices_228] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_773, vertices_73, vertices_521, vertices_49, vertices_145, vertices_529, vertices_97, vertices_545, vertices_193, vertices_641, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_76, vertices_268, vertices_100, vertices_164, vertices_292, vertices_196, vertices_324, vertices_388, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_560, vertices_400, vertices_224, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_109), (false, vertices_781), (false, vertices_805), (false, vertices_713), (false, vertices_241), (false, vertices_561), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_770), (true, vertices_164), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_328), (true, vertices_304), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_109) then 17 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
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
cert_row_4 0 0 2 5 7 8 842 322 1
cert_row_4 1 0 1 5 6 7 454 194 1
cert_row_4 2 0 3 4 7 8 818 274 2
cert_row_4 3 1 3 4 6 7 436 164 1
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 1 0 1 5 6 194 454 1
cert_coverFacet 1 842
cert_cover_5 1 0 0 2 5 7 322 842 1
cert_coverFacet 2 818
cert_cover_5 2 2 0 3 4 7 274 818 2
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 164 436 1
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1151

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_1152.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1152

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 327, 555, 579, 313, 601, 465, 230, 722, 674, 812, 916, 676, 452, 792, 263, 35, 67, 515, 25, 41, 521, 81, 273, 289, 321, 577, 38, 70, 162, 546, 194, 578, 642, 164, 292, 548, 196, 324, 388, 644, 772, 280, 536, 296, 552, 776, 208, 592, 400, 656, 784, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_327, vertices_555, vertices_579, vertices_313, vertices_601, vertices_465, vertices_230, vertices_722, vertices_674, vertices_812, vertices_916, vertices_676, vertices_452, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_263, vertices_35, vertices_67, vertices_515, vertices_25, vertices_41, vertices_521, vertices_81, vertices_273, vertices_289, vertices_321, vertices_577, vertices_38, vertices_70, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_164, vertices_292, vertices_548, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_280, vertices_536, vertices_296, vertices_552, vertices_776, vertices_208, vertices_592, vertices_400, vertices_656, vertices_784, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_327), (false, vertices_555), (false, vertices_579), (false, vertices_313), (false, vertices_601), (false, vertices_465), (true, vertices_162), (true, vertices_194), (true, vertices_642), (true, vertices_164), (true, vertices_548), (true, vertices_196), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_776), (true, vertices_656), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 15 else
  if p.val = (false, vertices_327) then 16 else
  if p.val = (false, vertices_555) then 17 else
  if p.val = (false, vertices_579) then 0 else
  if p.val = (false, vertices_313) then 20 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_579), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 7 8 812 292 1
cert_row_4 1 0 1 4 5 6 230 38 3
cert_row_4 2 0 3 5 6 8 722 194 1
cert_row_4 3 1 3 6 7 8 916 388 1
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 1 0 1 4 5 38 230 3
cert_coverFacet 1 722
cert_cover_5 1 2 0 3 5 6 194 722 1
cert_coverFacet 2 674
cert_cover_2 2 4 0 6 8 162 674 3
cert_coverFacet 3 812
cert_cover_5 3 0 1 2 4 7 292 812 1
cert_coverFacet 4 916
cert_cover_5 4 3 1 3 6 7 388 916 1
cert_coverFacet 5 676
cert_cover_2 5 4 1 6 8 164 676 3
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1152

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_1153.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1153

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 653, 421, 773, 313, 153, 241, 838, 218, 346, 650, 738, 372, 612, 676, 133, 261, 517, 25, 137, 265, 521, 49, 145, 161, 289, 769, 90, 138, 266, 522, 194, 322, 578, 642, 770, 100, 164, 292, 548, 324, 580, 644, 772, 152, 280, 648, 112, 304, 208, 336, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_653, vertices_421, vertices_773, vertices_313, vertices_153, vertices_241, vertices_838, vertices_218, vertices_346, vertices_650, vertices_738, vertices_372, vertices_612, vertices_676] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_161, vertices_289, vertices_769, vertices_90, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_100, vertices_164, vertices_292, vertices_548, vertices_324, vertices_580, vertices_644, vertices_772, vertices_152, vertices_280, vertices_648, vertices_112, vertices_304, vertices_208, vertices_336, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_653), (false, vertices_421), (false, vertices_773), (false, vertices_313), (false, vertices_153), (false, vertices_241), (true, vertices_90), (true, vertices_138), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_100), (true, vertices_548), (true, vertices_324), (true, vertices_580), (true, vertices_336), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_153) then 1 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_90) then 16 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 773 1 153 138 194 322 578 642 100 548 324 580 336 608 672 779 90 653 421 313 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 4 5 6 8 738 194 1
cert_row_4 2 0 1 5 7 8 838 322 1
cert_row_4 3 1 3 4 5 7 372 100 1
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 2 0 1 5 7 322 838 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 6 90 218 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 7 90 346 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 738
cert_cover_5 4 1 0 4 5 6 194 738 1
cert_coverFacet 5 372
cert_cover_5 5 3 1 3 4 5 100 372 1
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 676
cert_cover_2 7 4 1 6 8 164 676 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1153

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_1154.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1154

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 341, 229, 293, 793, 625, 422, 410, 234, 618, 778, 604, 156, 204, 404, 37, 69, 261, 81, 273, 529, 97, 289, 545, 769, 106, 138, 266, 522, 162, 290, 546, 386, 770, 28, 76, 140, 84, 148, 276, 164, 292, 196, 388, 152, 280, 536, 200, 584, 776, 592, 400, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_341, vertices_229, vertices_293, vertices_793, vertices_625, vertices_422, vertices_410, vertices_234, vertices_618, vertices_778, vertices_604, vertices_156, vertices_204, vertices_404] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_261, vertices_81, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_769, vertices_106, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_28, vertices_76, vertices_140, vertices_84, vertices_148, vertices_276, vertices_164, vertices_292, vertices_196, vertices_388, vertices_152, vertices_280, vertices_536, vertices_200, vertices_584, vertices_776, vertices_592, vertices_400, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_341), (false, vertices_229), (false, vertices_293), (false, vertices_793), (false, vertices_625), (true, vertices_106), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_162), (true, vertices_386), (true, vertices_28), (true, vertices_76), (true, vertices_140), (true, vertices_148), (true, vertices_388), (true, vertices_152), (true, vertices_200), (true, vertices_584), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_229) then 20 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_793) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_106) then 17 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 293 138 266 522 162 386 28 76 140 148 388 152 200 584 400 803 106 341 229 793 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 5 8 604 28 3
cert_row_2 1 0 2 4 5 106
cert_row_4 2 0 1 4 6 7 422 162 1
cert_row_4 3 0 2 3 6 7 410 138 2
cert_rows
cert_pivot_2 8 5 1 0
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 2 0 1 4 6 162 422 1
cert_coverFacet 1 410
cert_cover_5 1 3 0 2 3 6 138 410 2
cert_coverFacet 2 234
cert_cover_5 2 1 0 2 4 6 106 234 3
cert_coverFacet 3 618
cert_cover_5 3 1 0 2 4 8 106 618 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 604
cert_cover_5 5 0 1 2 3 5 28 604 3
cert_coverFacet 6 156
cert_cover_2 6 2 1 3 6 28 156 3
cert_coverFacet 7 204
cert_cover_2 7 2 1 5 6 76 204 3
cert_coverFacet 8 404
cert_cover_2 8 3 1 6 7 148 404 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1154

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_1155.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1155

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 589, 341, 773, 625, 433, 782, 410, 234, 618, 418, 156, 284, 204, 244, 69, 261, 517, 49, 81, 273, 289, 545, 577, 769, 106, 138, 266, 522, 162, 290, 546, 386, 770, 28, 76, 140, 268, 524, 84, 148, 276, 196, 772, 152, 280, 200, 584, 112, 176, 400, 224, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_589, vertices_341, vertices_773, vertices_625, vertices_433, vertices_782, vertices_410, vertices_234, vertices_618, vertices_418, vertices_156, vertices_284, vertices_204, vertices_244] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_49, vertices_81, vertices_273, vertices_289, vertices_545, vertices_577, vertices_769, vertices_106, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_28, vertices_76, vertices_140, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_196, vertices_772, vertices_152, vertices_280, vertices_200, vertices_584, vertices_112, vertices_176, vertices_400, vertices_224, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_589), (false, vertices_341), (false, vertices_773), (false, vertices_625), (false, vertices_433), (true, vertices_106), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_162), (true, vertices_386), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_148), (true, vertices_196), (true, vertices_152), (true, vertices_280), (true, vertices_200), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_341) then 20 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_106) then 17 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_106), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 0 2 3 6 7 410 138 2
cert_row_2 2 0 2 4 5 106
cert_row_4 3 1 3 4 5 6 244 84 2
cert_rows
cert_pivot_2 8 7 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 410
cert_cover_5 1 1 0 2 3 6 138 410 2
cert_coverFacet 2 234
cert_cover_5 2 2 0 2 4 6 106 234 3
cert_coverFacet 3 618
cert_cover_5 3 2 0 2 4 8 106 618 3
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 204
cert_cover_2 7 2 1 5 6 76 204 3
cert_coverFacet 8 244
cert_cover_5 8 3 1 3 4 5 84 244 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1155

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_1156.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1156

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 83, 355, 557, 601, 297, 737, 158, 398, 722, 450, 540, 300, 692, 484, 19, 67, 259, 25, 41, 265, 521, 81, 97, 289, 545, 577, 142, 26, 266, 82, 146, 194, 322, 386, 28, 44, 268, 524, 148, 532, 164, 292, 548, 388, 536, 296, 592, 656, 224, 352, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_83, vertices_355, vertices_557, vertices_601, vertices_297, vertices_737, vertices_158, vertices_398, vertices_722, vertices_450, vertices_540, vertices_300, vertices_692, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_259, vertices_25, vertices_41, vertices_265, vertices_521, vertices_81, vertices_97, vertices_289, vertices_545, vertices_577, vertices_142, vertices_26, vertices_266, vertices_82, vertices_146, vertices_194, vertices_322, vertices_386, vertices_28, vertices_44, vertices_268, vertices_524, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_536, vertices_296, vertices_592, vertices_656, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_83), (false, vertices_355), (false, vertices_557), (false, vertices_601), (false, vertices_297), (false, vertices_737), (true, vertices_142), (true, vertices_146), (true, vertices_194), (true, vertices_386), (true, vertices_28), (true, vertices_268), (true, vertices_148), (true, vertices_532), (true, vertices_164), (true, vertices_292), (true, vertices_388), (true, vertices_656), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 15 else
  if p.val = (false, vertices_83) then 0 else
  if p.val = (false, vertices_355) then 16 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_142) then 17 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_83), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_142), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
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
cert_row_2 0 0 1 2 6 142
cert_row_4 1 0 3 5 6 8 722 82 3
cert_row_4 2 1 3 4 6 8 692 148 2
cert_row_4 3 1 4 5 6 7 484 164 2
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 142 158 3
cert_coverFacet 1 398
cert_cover_5 1 0 0 1 2 7 142 398 3
cert_coverFacet 2 722
cert_cover_5 2 1 0 3 5 6 82 722 3
cert_coverFacet 3 450
cert_cover_2 3 5 0 6 7 194 450 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 692
cert_cover_5 6 2 1 3 4 6 148 692 2
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 164 484 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1156

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_1157.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1157

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 805, 217, 617, 393, 481, 94, 590, 790, 154, 394, 434, 244, 308, 612, 73, 137, 265, 521, 97, 289, 545, 193, 385, 769, 78, 22, 518, 26, 138, 266, 522, 146, 274, 386, 770, 52, 84, 276, 100, 292, 548, 580, 772, 88, 152, 584, 392, 176, 304, 208, 224, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_805, vertices_217, vertices_617, vertices_393, vertices_481, vertices_94, vertices_590, vertices_790, vertices_154, vertices_394, vertices_434, vertices_244, vertices_308, vertices_612] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_521, vertices_97, vertices_289, vertices_545, vertices_193, vertices_385, vertices_769, vertices_78, vertices_22, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_386, vertices_770, vertices_52, vertices_84, vertices_276, vertices_100, vertices_292, vertices_548, vertices_580, vertices_772, vertices_88, vertices_152, vertices_584, vertices_392, vertices_176, vertices_304, vertices_208, vertices_224, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_805), (false, vertices_217), (false, vertices_617), (false, vertices_393), (false, vertices_481), (true, vertices_78), (true, vertices_22), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_146), (true, vertices_274), (true, vertices_386), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_100), (true, vertices_580), (true, vertices_176), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_580) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_304) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 393 22 518 26 138 146 274 386 52 84 276 100 580 176 304 779 78 805 217 617 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 1 3 7 8 790 22 3
cert_row_4 2 0 3 4 6 7 434 146 2
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 78 94 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 790
cert_cover_5 2 1 0 1 3 7 22 790 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 434
cert_cover_5 5 2 0 3 4 6 146 434 2
cert_coverFacet 6 244
cert_cover_5 6 3 1 3 4 5 52 244 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coverFacet 8 612
cert_cover_2 8 4 1 5 8 100 612 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1157

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_1158.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1158

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 589, 805, 325, 433, 737, 334, 314, 218, 402, 60, 540, 300, 692, 728, 69, 261, 517, 161, 289, 545, 193, 321, 577, 385, 26, 74, 266, 146, 274, 194, 322, 386, 28, 44, 76, 268, 524, 52, 532, 292, 548, 324, 56, 216, 536, 296, 584, 176, 304, 400, 656, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_589, vertices_805, vertices_325, vertices_433, vertices_737, vertices_334, vertices_314, vertices_218, vertices_402, vertices_60, vertices_540, vertices_300, vertices_692, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_26, vertices_74, vertices_266, vertices_146, vertices_274, vertices_194, vertices_322, vertices_386, vertices_28, vertices_44, vertices_76, vertices_268, vertices_524, vertices_52, vertices_532, vertices_292, vertices_548, vertices_324, vertices_56, vertices_216, vertices_536, vertices_296, vertices_584, vertices_176, vertices_304, vertices_400, vertices_656, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_589), (false, vertices_805), (false, vertices_325), (false, vertices_433), (false, vertices_737), (true, vertices_26), (true, vertices_74), (true, vertices_266), (true, vertices_146), (true, vertices_274), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_52), (true, vertices_532), (true, vertices_56), (true, vertices_216), (true, vertices_536), (true, vertices_296), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_216) then 21 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 6 8 692 52 3
cert_row_2 1 2 3 5 6 216
cert_row_4 2 0 1 2 5 7 334 74 1
cert_row_4 3 0 2 3 4 7 314 26 3
cert_rows
cert_pivot_2 8 6 1 0
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 2 0 1 2 5 74 334 1
cert_coverFacet 1 314
cert_cover_5 1 3 0 2 3 4 26 314 3
cert_coverFacet 2 218
cert_cover_5 2 1 0 2 3 5 26 218 3
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 60
cert_cover_2 4 2 1 3 4 28 60 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 692
cert_cover_5 7 0 1 3 4 6 52 692 3
cert_coverFacet 8 728
cert_cover_5 8 1 2 3 5 8 216 728 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1158

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_1159.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1159

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 653, 601, 409, 369, 449, 398, 358, 166, 626, 674, 450, 316, 572, 676, 25, 137, 521, 81, 273, 193, 321, 577, 385, 641, 38, 134, 262, 98, 162, 546, 194, 322, 578, 386, 642, 60, 140, 268, 524, 164, 292, 548, 644, 280, 536, 392, 112, 304, 560, 592, 352, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_653, vertices_601, vertices_409, vertices_369, vertices_449, vertices_398, vertices_358, vertices_166, vertices_626, vertices_674, vertices_450, vertices_316, vertices_572, vertices_676] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_521, vertices_81, vertices_273, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_38, vertices_134, vertices_262, vertices_98, vertices_162, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_60, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_644, vertices_280, vertices_536, vertices_392, vertices_112, vertices_304, vertices_560, vertices_592, vertices_352, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_653), (false, vertices_601), (false, vertices_409), (false, vertices_369), (false, vertices_449), (true, vertices_38), (true, vertices_134), (true, vertices_262), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_322), (true, vertices_386), (true, vertices_60), (true, vertices_268), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_560), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_60) then 19 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_548) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 449 2 38 1 134 3 262 98 162 546 322 386 268 164 292 548 560 672 707 653 60 601 409 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 1 4 5 7 358 38 3
cert_row_4 3 0 3 4 5 8 626 98 1
cert_rows
cert_pivot_2 6 2 1 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 358
cert_cover_5 1 2 0 1 4 5 38 358 3
cert_coverFacet 2 166
cert_cover_2 2 1 0 4 6 38 166 3
cert_coverFacet 3 626
cert_cover_5 3 3 0 3 4 5 98 626 1
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 316
cert_cover_5 6 1 1 2 3 7 60 316 3
cert_coverFacet 7 572
cert_cover_5 7 1 1 2 3 8 60 572 3
cert_coverFacet 8 676
cert_cover_2 8 4 1 6 8 164 676 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1159

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_1160.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1160

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 397, 341, 709, 689, 401, 334, 590, 570, 426, 114, 354, 684, 368, 432, 69, 133, 261, 81, 145, 273, 529, 577, 385, 641, 78, 42, 266, 522, 50, 82, 530, 98, 290, 322, 578, 140, 268, 524, 324, 580, 644, 168, 552, 392, 112, 176, 304, 560, 336, 400, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_397, vertices_341, vertices_709, vertices_689, vertices_401, vertices_334, vertices_590, vertices_570, vertices_426, vertices_114, vertices_354, vertices_684, vertices_368, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_81, vertices_145, vertices_273, vertices_529, vertices_577, vertices_385, vertices_641, vertices_78, vertices_42, vertices_266, vertices_522, vertices_50, vertices_82, vertices_530, vertices_98, vertices_290, vertices_322, vertices_578, vertices_140, vertices_268, vertices_524, vertices_324, vertices_580, vertices_644, vertices_168, vertices_552, vertices_392, vertices_112, vertices_176, vertices_304, vertices_560, vertices_336, vertices_400, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_397), (false, vertices_341), (false, vertices_709), (false, vertices_689), (false, vertices_401), (true, vertices_78), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_98), (true, vertices_290), (true, vertices_322), (true, vertices_524), (true, vertices_168), (true, vertices_552), (true, vertices_112), (true, vertices_304), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 16 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_341) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_19 0 401 1 42 266 522 50 98 290 322 524 168 552 112 304 352 416 595 78 397 341 709 689
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 2 3 4 8 570 42 2
cert_row_4 2 0 2 4 6 7 426 42 3
cert_row_4 3 1 2 4 6 8 684 140 2
cert_rows
cert_pivot_2 5 3 0 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 7 78 334 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 570
cert_cover_5 2 1 0 2 3 4 42 570 2
cert_coverFacet 3 426
cert_cover_5 3 2 0 2 4 6 42 426 3
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 684
cert_cover_5 6 3 1 2 4 6 140 684 2
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1160

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3693 : Certifies 3693 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1131.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3694 : Certifies 3694 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1132.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3695 : Certifies 3695 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1133.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3696 : Certifies 3696 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1134.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3697 : Certifies 3697 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1135.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3698 : Certifies 3698 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1136.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3699 : Certifies 3699 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1137.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3700 : Certifies 3700 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1138.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3701 : Certifies 3701 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1139.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3702 : Certifies 3702 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1140.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3703 : Certifies 3703 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1141.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3704 : Certifies 3704 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1142.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3705 : Certifies 3705 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1143.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3706 : Certifies 3706 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1144.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3707 : Certifies 3707 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1145.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3708 : Certifies 3708 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1146.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3709 : Certifies 3709 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1147.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3710 : Certifies 3710 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1148.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3711 : Certifies 3711 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1149.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3712 : Certifies 3712 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1150.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3713 : Certifies 3713 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1151.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3714 : Certifies 3714 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1152.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3715 : Certifies 3715 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1153.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3716 : Certifies 3716 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1154.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3717 : Certifies 3717 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1155.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3718 : Certifies 3718 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1156.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3719 : Certifies 3719 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1157.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3720 : Certifies 3720 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1158.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3721 : Certifies 3721 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1159.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3722 : Certifies 3722 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1160.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B122 (j : Fin 30) :
    Certifies (3693 + j.val) := by
  fin_cases j
  · exact projection_3693
  · exact projection_3694
  · exact projection_3695
  · exact projection_3696
  · exact projection_3697
  · exact projection_3698
  · exact projection_3699
  · exact projection_3700
  · exact projection_3701
  · exact projection_3702
  · exact projection_3703
  · exact projection_3704
  · exact projection_3705
  · exact projection_3706
  · exact projection_3707
  · exact projection_3708
  · exact projection_3709
  · exact projection_3710
  · exact projection_3711
  · exact projection_3712
  · exact projection_3713
  · exact projection_3714
  · exact projection_3715
  · exact projection_3716
  · exact projection_3717
  · exact projection_3718
  · exact projection_3719
  · exact projection_3720
  · exact projection_3721
  · exact projection_3722

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
